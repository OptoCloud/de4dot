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
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using dnlib.DotNet;

namespace AssemblyData.methodsrewriter {
	static class Resolver {
		static readonly Dictionary<string, AssemblyResolver> AssemblyResolvers = new(StringComparer.Ordinal);
		static readonly Dictionary<Module, MModule> Modules = new();

		public static MModule LoadAssembly(Module module) {
			if (Modules.TryGetValue(module, out var info))
				return info;

			info = new MModule(module, ModuleDefMD.Load(module.FullyQualifiedName));
			Modules[module] = info;
			return info;
		}

		static MModule GetModule(ModuleDef moduleDef) => Modules.Values.FirstOrDefault(mm => mm.moduleDef == moduleDef);

		static MModule GetModule(AssemblyRef asmRef) {
			foreach (var mm in Modules.Values) {
				var asm = mm.moduleDef.Assembly;
				if (asm is not null && asm.FullName == asmRef.FullName)
					return mm;
			}
			return null;
		}

		public static MModule GetModule(IScope scope) =>
			scope.ScopeType switch {
				ScopeType.ModuleDef => GetModule((ModuleDef)scope),
				ScopeType.AssemblyRef => GetModule((AssemblyRef)scope),
				_ => null
			};

		public static MType GetType(IType typeRef) {
			if (typeRef is null) return null;
			return GetModule(typeRef.Scope)?.GetType(typeRef);
		}

		public static MMethod GetMethod(IMethod methodRef) {
			if (methodRef is null) return null;
			return GetModule(methodRef.DeclaringType.Scope)?.GetMethod(methodRef);
		}

		public static MField GetField(IField fieldRef) {
			if (fieldRef is null) return null;
			return GetModule(fieldRef.DeclaringType.Scope)?.GetField(fieldRef);
		}

		public static object GetRtObject(ITokenOperand memberRef) =>
			memberRef switch {
				null => null,
				ITypeDefOrRef tdr => GetRtType(tdr),
				IField { FieldSig: not null } field => GetRtField(field),
				IMethod { MethodSig: not null } method => GetRtMethod(method),
				_ => throw new ApplicationException($"Unknown MemberRef: {memberRef}")
			};

		public static Type GetRtType(IType typeRef) {
			var mtype = GetType(typeRef);
			if (mtype is not null)
				return mtype.type;

			return Resolver.Resolve(typeRef);
		}

		public static FieldInfo GetRtField(IField fieldRef) {
			var mfield = GetField(fieldRef);
			if (mfield is not null)
				return mfield.fieldInfo;

			return Resolver.Resolve(fieldRef);
		}

		public static MethodBase GetRtMethod(IMethod methodRef) {
			var mmethod = GetMethod(methodRef);
			if (mmethod is not null)
				return mmethod.methodBase;

			return Resolver.Resolve(methodRef);
		}

		static AssemblyResolver GetAssemblyResolver(ITypeDefOrRef type) {
			var asmName = type.DefinitionAssembly.FullName;
			if (!AssemblyResolvers.TryGetValue(asmName, out var resolver))
				AssemblyResolvers[asmName] = resolver = new AssemblyResolver(asmName);
			return resolver;
		}

		static Type Resolve(IType typeRef) {
			if (typeRef is null)
				return null;
			var scopeType = typeRef.ScopeType;
			var resolver = GetAssemblyResolver(scopeType);
			var resolvedType = resolver.Resolve(scopeType);
			if (resolvedType is not null)
				return FixType(typeRef, resolvedType);
			throw new ApplicationException($"Could not resolve type {typeRef} ({typeRef.MDToken.Raw:X8}) in assembly {resolver}");
		}

		static FieldInfo Resolve(IField fieldRef) {
			if (fieldRef is null)
				return null;
			var resolver = GetAssemblyResolver(fieldRef.DeclaringType);
			var fieldInfo = resolver.Resolve(fieldRef);
			if (fieldInfo is not null)
				return fieldInfo;
			throw new ApplicationException($"Could not resolve field {fieldRef} ({fieldRef.MDToken.Raw:X8}) in assembly {resolver}");
		}

		static MethodBase Resolve(IMethod methodRef) {
			if (methodRef is null)
				return null;
			var resolver = GetAssemblyResolver(methodRef.DeclaringType);
			var methodBase = resolver.Resolve(methodRef);
			if (methodBase is not null)
				return methodBase;
			throw new ApplicationException($"Could not resolve method {methodRef} ({methodRef.MDToken.Raw:X8}) in assembly {resolver}");
		}

		static Type FixType(IType typeRef, Type type) {
			if (typeRef is not TypeSig sig) {
				sig = (typeRef as TypeSpec)?.TypeSig;
			}
			
			while (sig is not null) {
				switch (sig.ElementType) {
				case ElementType.SZArray:
					type = type.MakeArrayType();
					break;

				case ElementType.Array:
					type = type.MakeArrayType((int)((ArraySig)sig).Rank);
					break;

				case ElementType.ByRef:
					type = type.MakeByRefType();
					break;

				case ElementType.Ptr:
					type = type.MakePointerType();
					break;

				case ElementType.GenericInst:
					var git = (GenericInstSig)sig;
					var args = new Type[git.GenericArguments.Count];
					bool isGenericTypeDef = true;
					for (int i = 0; i < args.Length; i++) {
						var arg = git.GenericArguments[i];
						if (arg is not GenericSig)
							isGenericTypeDef = false;
						args[i] = Resolve(arg);
					}
					if (!isGenericTypeDef)
						type = type.MakeGenericType(args);
					break;
				}

				sig = sig.Next;
			}
			return type;
		}
	}
}
