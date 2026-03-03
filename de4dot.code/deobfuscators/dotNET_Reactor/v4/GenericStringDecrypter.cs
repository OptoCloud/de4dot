/*
    Copyright (C) 2011-2015 de4dot@gmail.com

    This file is part of de4dot.

    de4dot is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    de4dot is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with de4dot.  If not, see <http://www.gnu.org/licenses/>.
*/

using System;
using System.Text;
using System.Reflection;
using System.Collections.Generic;
using dnlib.DotNet;
using dnlib.DotNet.Emit;
using de4dot.blocks;

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4 {
	/// <summary>
	/// Handles .NET Reactor v6.x generic string/constant decryption methods.
	///
	/// These are <Module> methods with signature !!0 Method&lt;T&gt;(int32), called as
	/// Method&lt;string&gt;(193412188). The int32 argument is transformed via multiply-XOR
	/// to produce an offset into a runtime-initialized byte[] from which the string
	/// is read (4-byte LE length + UTF-8 data).
	///
	/// The byte[] field has HasFieldRVA=false (no static initial value in PE) — it's
	/// populated by the .cctor at runtime via XorShift PRNG + block XOR decryption.
	/// We extract it by dynamically loading the assembly (Assembly.Load) which triggers
	/// the .cctor, then reading the field value via reflection.
	/// </summary>
	class GenericStringDecrypter {
		ModuleDefMD module;
		byte[] dataArray;         // runtime-initialized data extracted via dynamic loading
		FieldDef dataField;       // the byte[] field on <Module> that holds encrypted data
		List<DecrypterMethod> decrypterMethods = new List<DecrypterMethod>();

		public class DecrypterMethod {
			public MethodDef method;
			public uint mulConstant;  // per-method multiply constant from IL pattern
			public uint xorConstant;  // per-method XOR constant from IL pattern
		}

		public bool Detected => decrypterMethods.Count > 0;
		public bool Initialized => dataArray != null;
		public IEnumerable<DecrypterMethod> DecrypterMethods => decrypterMethods;

		public GenericStringDecrypter(ModuleDefMD module) => this.module = module;

		/// <summary>
		/// Scans all module types for generic constant decrypter methods matching
		/// the signature: static !!0 Method&lt;T&gt;(int32) with GenericMVar return type.
		/// Extracts the per-method MUL/XOR constants and the shared byte[] field.
		/// </summary>
		public void Find() {
			foreach (var type in module.Types) {
				foreach (var method in type.Methods) {
					if (!method.IsStatic || !method.HasBody)
						continue;
					// Must be a generic method with exactly 1 type parameter
					if (!method.HasGenericParameters || method.GenericParameters.Count != 1)
						continue;
					var sig = method.MethodSig;
					if (sig == null || sig.Params.Count != 1)
						continue;
					// Single int32 argument
					if (sig.Params[0].GetElementType() != ElementType.I4)
						continue;
					// Return type is the generic type parameter (!!0)
					if (!(sig.RetType.RemovePinnedAndModifiers() is GenericMVar))
						continue;

					if (TryExtractConstants(method, out uint mul, out uint xor, out var field)) {
						decrypterMethods.Add(new DecrypterMethod {
							method = method,
							mulConstant = mul,
							xorConstant = xor,
						});
						if (dataField == null && field != null)
							dataField = field;
					}
				}
			}

			if (decrypterMethods.Count > 0)
				Logger.v("Found {0} generic constant decrypter method(s)", decrypterMethods.Count);
		}

		public void Initialize(byte[] fileData) {
			if (dataField == null || decrypterMethods.Count == 0)
				return;

			// Try dynamic loading: load the assembly, trigger .cctor, read the field
			dataArray = TryDynamicExtract(fileData);

			if (dataArray != null)
				Logger.v("Generic string decrypter: data size: {0}", dataArray.Length);
			else
				Logger.w("Could not extract generic string decrypter data array");
		}

		/// <summary>
		/// Loads the obfuscated assembly into the current process to trigger its .cctor,
		/// which initializes the byte[] data field. Then reads the field via reflection.
		/// Note: Module.ResolveType(0x02000001) throws for &lt;Module&gt;, so we use
		/// Module.ResolveField() with the field's metadata token directly.
		/// </summary>
		byte[] TryDynamicExtract(byte[] fileData) {
			try {
				var asm = Assembly.Load(fileData);
				var mod = asm.GetModules()[0];

				// For <Module> (global type), use Module.ResolveField() or Module.GetFields()
				// to access module-level fields directly
				try {
					var field = mod.ResolveField(dataField.MDToken.ToInt32());
					if (field != null) {
						var value = field.GetValue(null);
						if (value is byte[] bytes && bytes.Length > 0)
							return (byte[])bytes.Clone();
					}
				}
				catch (Exception ex) {
					Logger.v("ResolveField failed: {0}", ex.Message);
				}

				// Fallback: enumerate all module-level byte[] fields
				var fields = mod.GetFields(BindingFlags.Static | BindingFlags.NonPublic | BindingFlags.Public);
				foreach (var field in fields) {
					if (field.FieldType != typeof(byte[]))
						continue;
					try {
						var value = field.GetValue(null);
						if (value is byte[] bytes && bytes.Length > 0)
							return (byte[])bytes.Clone();
					}
					catch { }
				}
			}
			catch (Exception ex) {
				Logger.v("Dynamic assembly load failed: {0}: {1}", ex.GetType().Name, ex.Message);
			}
			return null;
		}

		/// <summary>
		/// Extracts MUL and XOR constants from the method's IL pattern:
		///   ldarg.0; ldc.i4 MUL; mul; ldc.i4 XOR; xor; starg
		/// This pattern transforms the int32 argument in-place before using it as
		/// an index into the data array. Also finds the byte[] field (ldsfld).
		/// </summary>
		bool TryExtractConstants(MethodDef method, out uint mul, out uint xor, out FieldDef byteArrayField) {
			mul = 0;
			xor = 0;
			byteArrayField = null;

			var instrs = method.Body.Instructions;

			// Look for: ldarg.0, ldc.i4 <MUL>, mul, ldc.i4 <XOR>, xor, starg.s|starg
			for (int i = 0; i < instrs.Count - 5; i++) {
				var code = instrs[i].OpCode.Code;
				if (code != Code.Ldarg_0 && code != Code.Ldarg && code != Code.Ldarg_S)
					continue;
				if (code == Code.Ldarg || code == Code.Ldarg_S) {
					var param = instrs[i].Operand as Parameter;
					if (param == null || param.Index != 0)
						continue;
				}
				if (!instrs[i + 1].IsLdcI4())
					continue;
				if (instrs[i + 2].OpCode.Code != Code.Mul)
					continue;
				if (!instrs[i + 3].IsLdcI4())
					continue;
				if (instrs[i + 4].OpCode.Code != Code.Xor)
					continue;
				if (instrs[i + 5].OpCode.Code != Code.Starg_S && instrs[i + 5].OpCode.Code != Code.Starg)
					continue;

				mul = (uint)instrs[i + 1].GetLdcI4Value();
				xor = (uint)instrs[i + 3].GetLdcI4Value();

				// Find the byte array field (ldsfld of byte[])
				for (int j = 0; j < instrs.Count; j++) {
					if (instrs[j].OpCode.Code != Code.Ldsfld)
						continue;
					if (instrs[j].Operand is FieldDef fd &&
						fd.FieldType != null &&
						fd.FieldType.FullName == "System.Byte[]") {
						byteArrayField = fd;
						break;
					}
				}

				return true;
			}

			return false;
		}

		/// <summary>
		/// Decrypts a constant given the method and its int32 argument.
		/// Transform: (arg * MUL) ^ XOR → top 2 bits = type flag, bottom 30 bits * 4 = offset.
		/// Type flag 3 = string (4-byte LE length + UTF-8 payload in dataArray).
		/// </summary>
		public string Decrypt(MethodDef method, int arg) {
			var info = FindDecrypterMethod(method);
			if (info == null || dataArray == null)
				return null;

			uint transformed = unchecked((uint)arg * info.mulConstant) ^ info.xorConstant;
			// The top 2 bits select the type (string/value/array/default), but the
			// obfuscator shuffles the mapping per method. Since this is only called
			// for Method<string>() instantiations, the type flag is always the string
			// case — just use the bottom 30 bits as the offset directly.
			int offset = (int)((transformed & 0x3FFFFFFFU) << 2);  // bottom 30 bits * 4 = byte offset

			if (offset < 0 || offset + 4 > dataArray.Length)
				return null;

			// String: read 4-byte LE length, then UTF-8 string
			int length = dataArray[offset] |
				(dataArray[offset + 1] << 8) |
				(dataArray[offset + 2] << 16) |
				(dataArray[offset + 3] << 24);
			if (length < 0 || offset + 4 + length > dataArray.Length)
				return null;
			return Encoding.UTF8.GetString(dataArray, offset + 4, length);
		}

		DecrypterMethod FindDecrypterMethod(MethodDef method) {
			foreach (var dm in decrypterMethods) {
				if (dm.method == method)
					return dm;
			}
			return null;
		}
	}
}
