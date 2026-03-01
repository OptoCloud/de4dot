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

using System.Collections.Generic;
using de4dot.blocks;
using dnlib.DotNet.Emit;

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4.cflow;

/// <summary>
///     Pattern matching for XOR-switch dispatch and multiply-XOR transitions.
/// </summary>
class PatternMatcher {
	readonly IList<Local> locals;

	internal PatternMatcher(IList<Local> locals) => this.locals = locals;

	/// <summary>
	///     Returns true for instructions that have no effect on the dispatch computation:
	///     nop, conv.i4, conv.u4.
	/// </summary>
	internal static bool IsHarmlessOp(Instr instr) {
		var code = instr.OpCode.Code;
		return code == Code.Nop || code == Code.Conv_I4 || code == Code.Conv_U4;
	}

	/// <summary>
	///     Folds opaque-predicate junk of the form "ldc X; ldc X; pop" → "ldc X".
	/// </summary>
	internal static bool FoldOpaqueConstants(Block block) {
		var instrs = block.Instructions;
		bool changed = false;
		for (int i = instrs.Count - 3; i >= 0; i--) {
			if (instrs[i].IsLdcI4() && instrs[i + 1].IsLdcI4() &&
			    instrs[i + 2].OpCode.Code == Code.Pop &&
			    instrs[i].GetLdcI4Value() == instrs[i + 1].GetLdcI4Value()) {
				instrs.RemoveAt(i + 2); // pop
				instrs.RemoveAt(i + 1); // duplicate ldc
				changed = true;
			}
		}

		return changed;
	}

	/// <summary>
	///     Minimal backward slice: starting from instruction at 'idx', evaluates
	///     the expression that produces the top-of-stack value by walking backward
	///     through the instruction stream.
	///     Returns (value, startIdx) where startIdx is the earliest instruction
	///     index contributing to the result. Returns null on failure.
	/// </summary>
	internal (uint value, int startIdx)? SliceBackward(List<Instr> instrs, int idx, int depth = 0) {
		if (depth > 20 || idx < 0 || idx >= instrs.Count)
			return null;

		var instr = instrs[idx];

		if (instr.IsLdcI4())
			return ((uint)instr.GetLdcI4Value(), idx);

		if (instr.IsLdloc()) {
			var local = Instr.GetLocalVar(locals, instr);
			if (local == null)
				return null;
			for (int j = idx - 1; j >= 0; j--) {
				if (instrs[j].IsStloc() && Instr.GetLocalVar(locals, instrs[j]) == local)
					return SliceBackward(instrs, j - 1, depth + 1);
			}

			return null;
		}

		var code = instr.OpCode.Code;

		if (code == Code.Nop)
			return SliceBackward(instrs, idx - 1, depth + 1);

		if (code == Code.Conv_I4 || code == Code.Conv_U4)
			return SliceBackward(instrs, idx - 1, depth + 1);

		if (code == Code.Dup)
			return null;

		if (code == Code.Pop) {
			var popped = SliceBackward(instrs, idx - 1, depth + 1);
			if (popped == null)
				return null;
			return SliceBackward(instrs, popped.Value.startIdx - 1, depth + 1);
		}

		if (code == Code.Xor || code == Code.Mul || code == Code.Add || code == Code.Sub) {
			var right = SliceBackward(instrs, idx - 1, depth + 1);
			if (right == null)
				return null;
			var left = SliceBackward(instrs, right.Value.startIdx - 1, depth + 1);
			if (left == null)
				return null;

			uint result = DomainMath.ApplyBinaryOp(code, left.Value.value, right.Value.value);
			return (result, left.Value.startIdx);
		}

		return null;
	}

	/// <summary>
	///     Scans backwards from the switch instruction to extract the dispatch pattern.
	/// </summary>
	internal bool TryExtractDispatchInfo(Block switchBlock, out DispatchInfo info) {
		info = default;
		var instrs = switchBlock.Instructions;
		int switchIdx = instrs.Count - 1;

		if (switchIdx < 4)
			return false;

		int idx = switchIdx - 1;

		// rem.un
		if (instrs[idx].OpCode.Code != Code.Rem_Un)
			return false;
		idx--;

		// ldc.i4 MODULUS
		if (!instrs[idx].IsLdcI4())
			return false;
		uint modulus = (uint)instrs[idx].GetLdcI4Value();
		if (modulus == 0)
			return false;
		idx--;

		// Optional: stloc dispatch_var + dup
		Local dispatchVar = null;
		if (idx >= 1 && instrs[idx].IsStloc()) {
			dispatchVar = Instr.GetLocalVar(locals, instrs[idx]);
			idx--;
			if (instrs[idx].OpCode.Code != Code.Dup)
				return false;
			idx--;
		}

		if (idx < 1)
			return false;

		// xor
		if (instrs[idx].OpCode.Code != Code.Xor)
			return false;
		idx--;

		// ldc.i4 XOR_KEY
		if (!instrs[idx].IsLdcI4())
			return false;
		uint xorKey = (uint)instrs[idx].GetLdcI4Value();

		Local stateVar = null;
		uint? internalStateVarInput = null;
		if (idx == 0) {
			if (TryExtractSplitEmbeddedMul(switchBlock, xorKey, dispatchVar, modulus, out info))
				return true;
			// All predecessors have divergent mul/xor constants (per-case transitions),
			// or no mul-xor predecessor exists at all.
			// Treat as a plain xor+stack dispatch: state arrives on the stack,
			// no state variable owned by this block.
			info = new DispatchInfo { DispatchVar = dispatchVar, XorKey = xorKey, Modulus = modulus, StateVar = null };
			return true;
		}

		if (idx >= 1 && instrs[idx - 1].IsLdloc()) {
			stateVar = Instr.GetLocalVar(locals, instrs[idx - 1]);
		}
		else if (TryExtractEmbeddedMul(instrs, idx, xorKey, dispatchVar, modulus, out info)) {
			return true;
		}
		else {
			var stackVal = SliceBackward(instrs, idx - 1);
			if (stackVal == null)
				return false;
			if (stackVal.Value.startIdx > 10)
				return false;
			stateVar = null;
			internalStateVarInput = stackVal.Value.value;
		}

		info = new DispatchInfo {
			DispatchVar = dispatchVar,
			XorKey = xorKey,
			Modulus = modulus,
			StateVar = stateVar,
			InternalStateVarInput = internalStateVarInput
		};
		return true;
	}

	bool TryExtractEmbeddedMul(List<Instr> instrs, int idx, uint xorKey,
		Local dispatchVar, uint modulus, out DispatchInfo info) {
		info = default;

		int i = idx - 1;
		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i < 0 || instrs[i].OpCode.Code != Code.Xor)
			return false;
		i--;

		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i < 0 || !instrs[i].IsLdcI4())
			return false;
		uint xor2 = (uint)instrs[i].GetLdcI4Value();
		i--;

		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i < 0 || instrs[i].OpCode.Code != Code.Mul)
			return false;
		i--;

		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i < 0 || !instrs[i].IsLdcI4())
			return false;
		uint embeddedMul = (uint)instrs[i].GetLdcI4Value();
		i--;

		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i < 0 || !instrs[i].IsLdloc())
			return false;
		var stateVar = Instr.GetLocalVar(locals, instrs[i]);

		uint originalXorKey = xorKey;
		xorKey = unchecked(xor2 ^ xorKey);

		info = new DispatchInfo {
			DispatchVar = dispatchVar,
			XorKey = xorKey,
			Modulus = modulus,
			StateVar = stateVar,
			EmbeddedMul = embeddedMul,
			HasEmbeddedMul = true,
			OriginalXorKey = originalXorKey
		};
		return true;
	}

	bool TryExtractSplitEmbeddedMul(Block switchBlock, uint xorKey,
		Local dispatchVar, uint modulus, out DispatchInfo info) {
		info = default;

		// Require ALL matching predecessors to use identical mul/xor constants.
		// If they differ, the predecessors are per-case transition blocks (not a
		// uniform split dispatch), so this is NOT a split-embedded-mul pattern.
		uint? commonEmbeddedMul = null;
		uint? commonXor2 = null;
		Local commonStateVar = null;

		foreach (var pred in switchBlock.Sources) {
			if (pred == switchBlock) continue;
			var predInstrs = pred.Instructions;
			if (predInstrs.Count < 5) continue;

			int i = predInstrs.Count - 1;
			while (i >= 0 && IsHarmlessOp(predInstrs[i])) i--;

			if (i < 0 || predInstrs[i].OpCode.Code != Code.Xor) continue;
			i--;

			while (i >= 0 && IsHarmlessOp(predInstrs[i])) i--;
			if (i < 0 || !predInstrs[i].IsLdcI4()) continue;
			uint xor2 = (uint)predInstrs[i].GetLdcI4Value();
			i--;

			while (i >= 0 && IsHarmlessOp(predInstrs[i])) i--;
			if (i < 0 || predInstrs[i].OpCode.Code != Code.Mul) continue;
			i--;

			while (i >= 0 && IsHarmlessOp(predInstrs[i])) i--;
			if (i < 0 || !predInstrs[i].IsLdcI4()) continue;
			uint embeddedMul = (uint)predInstrs[i].GetLdcI4Value();
			i--;

			while (i >= 0 && IsHarmlessOp(predInstrs[i])) i--;
			if (i < 0 || !predInstrs[i].IsLdloc()) continue;
			var stateVar = Instr.GetLocalVar(locals, predInstrs[i]);

			if (commonEmbeddedMul == null) {
				commonEmbeddedMul = embeddedMul;
				commonXor2 = xor2;
				commonStateVar = stateVar;
			}
			else if (commonEmbeddedMul.Value != embeddedMul || commonXor2.Value != xor2
			                                                || commonStateVar != stateVar) {
				// Inconsistent constants or state variable across predecessors — these are
				// per-case transitions, not a uniform split-embedded-mul header.
				return false;
			}
		}

		if (commonEmbeddedMul == null)
			return false;

		uint originalXorKey = xorKey;
		xorKey = unchecked(commonXor2.Value ^ xorKey);

		info = new DispatchInfo {
			DispatchVar = dispatchVar,
			XorKey = xorKey,
			Modulus = modulus,
			StateVar = commonStateVar,
			EmbeddedMul = commonEmbeddedMul.Value,
			HasEmbeddedMul = true,
			OriginalXorKey = originalXorKey,
			SplitEmbeddedMul = true
		};
		return true;
	}

	/// <summary>
	///     Searches a block for the multiply-XOR state transition pattern.
	///     Returns the MUL and XOR2 constants, the exact pattern start index and length,
	///     and which local variable was loaded as input to the transition.
	/// </summary>
	internal bool TryGetMultiplyXorPattern(Block block, DispatchInfo info,
		out uint mulConst, out uint xor2Const, out int patternStart, out int patternLen,
		out Local loadedVar) {
		mulConst = 0;
		xor2Const = 0;
		patternStart = 0;
		patternLen = 0;
		loadedVar = null;
		var instrs = block.Instructions;

		if (instrs.Count < 5)
			return false;

		bool acceptAnyLocal = info.DispatchVar == null && info.StateVar == null && info.OriginalStateVar == null;

		for (int end = instrs.Count - 1; end >= 4; end--) {
			int i = end;
			bool hasTrailingStloc = false;

			// Optional trailing stloc
			if (instrs[i].IsStloc()) {
				var storeVar = Instr.GetLocalVar(locals, instrs[i]);
				if ((info.StateVar != null && storeVar == info.StateVar) ||
				    (info.OriginalStateVar != null && storeVar == info.OriginalStateVar) ||
				    (info.DispatchVar != null && storeVar == info.DispatchVar)) {
					hasTrailingStloc = true;
					i--;
				}
			}

			// xor
			while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
			if (i < 0 || instrs[i].OpCode.Code != Code.Xor)
				continue;
			i--;

			int afterXor = i;

			// Try standard order: ldloc V; ldc MUL; mul; ldc XOR2; xor
			var standardMatch = TryMatchStandardOrder(instrs, i, info, acceptAnyLocal);
			if (standardMatch != null) {
				mulConst = standardMatch.Value.mulConst;
				xor2Const = standardMatch.Value.xor2Const;
				patternStart = standardMatch.Value.matchStart;
				patternLen = end - patternStart + 1;
				loadedVar = standardMatch.Value.loadedVar;
				return true;
			}

			// Try reversed order: ldc XOR2; ldloc V; ldc MUL; mul; xor
			var reversedMatch = TryMatchReversedOrder(instrs, i, info, block, acceptAnyLocal);
			if (reversedMatch != null) {
				mulConst = reversedMatch.Value.mulConst;
				xor2Const = reversedMatch.Value.xor2Const;
				patternStart = reversedMatch.Value.matchStart;
				patternLen = end - patternStart + 1;
				loadedVar = reversedMatch.Value.loadedVar;
				return true;
			}
		}

		return false;
	}

	/// <summary>
	///     Convenience overload that discards the loaded variable info.
	/// </summary>
	internal bool TryGetMultiplyXorPattern(Block block, DispatchInfo info,
		out uint mulConst, out uint xor2Const, out int patternStart, out int patternLen) =>
		TryGetMultiplyXorPattern(block, info, out mulConst, out xor2Const,
			out patternStart, out patternLen, out _);

	(uint mulConst, uint xor2Const, int matchStart, Local loadedVar)? TryMatchStandardOrder(
		List<Instr> instrs, int i, DispatchInfo info, bool acceptAnyLocal) {
		// ldc.i4 XOR2
		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i < 0 || !instrs[i].IsLdcI4())
			return null;
		uint xor2 = (uint)instrs[i].GetLdcI4Value();
		i--;

		// mul
		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i < 0 || instrs[i].OpCode.Code != Code.Mul)
			return null;
		i--;

		// ldc.i4 MUL
		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i < 0 || !instrs[i].IsLdcI4())
			return null;
		uint mul = (uint)instrs[i].GetLdcI4Value();
		i--;

		// ldloc V
		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i < 0 || !instrs[i].IsLdloc())
			return null;
		var loadedVar = Instr.GetLocalVar(locals, instrs[i]);
		if (loadedVar == null)
			return null;
		if (!IsKnownDispatchVar(loadedVar, info, acceptAnyLocal))
			return null;

		return (mul, xor2, i, loadedVar);
	}

	(uint mulConst, uint xor2Const, int matchStart, Local loadedVar)? TryMatchReversedOrder(
		List<Instr> instrs, int i, DispatchInfo info, Block block, bool acceptAnyLocal) {
		// mul
		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i < 0 || instrs[i].OpCode.Code != Code.Mul)
			return null;
		i--;

		// ldc.i4 MUL
		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i < 0 || !instrs[i].IsLdcI4())
			return null;
		uint mul = (uint)instrs[i].GetLdcI4Value();
		i--;

		// ldloc V
		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i < 0 || !instrs[i].IsLdloc())
			return null;
		var loadedVar = Instr.GetLocalVar(locals, instrs[i]);
		if (loadedVar == null)
			return null;
		if (!IsKnownDispatchVar(loadedVar, info, acceptAnyLocal))
			return null;
		i--;

		// ldc.i4 XOR2 (at bottom in reversed order)
		while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
		if (i >= 0 && instrs[i].IsLdcI4()) {
			uint xor2 = (uint)instrs[i].GetLdcI4Value();
			return (mul, xor2, i, loadedVar);
		}

		// Stack-based XOR2 disabled: removing the pop orphans
		// the predecessor's value on the stack, causing max-stack errors.
		// Needs StackAnalyzer-based cleanup (Phase D) to work correctly.

		return null;
	}

	static bool IsKnownDispatchVar(Local loadedVar, DispatchInfo info, bool acceptAnyLocal) =>
		acceptAnyLocal ||
		(info.DispatchVar != null && loadedVar == info.DispatchVar) ||
		(info.StateVar != null && loadedVar == info.StateVar) ||
		(info.OriginalStateVar != null && loadedVar == info.OriginalStateVar);

	/// <summary>
	///     Looks at a block's predecessors for the opaque-predicate pattern:
	///     ldc.i4 X; ldc.i4 X (equal values). Returns X, or null if not found.
	/// </summary>
	internal static uint? FindPredecessorOpaqueConstant(Block block) {
		foreach (var pred in block.Sources) {
			var predInstrs = pred.Instructions;
			int lastIdx = predInstrs.Count - 1;
			while (lastIdx >= 0 && IsHarmlessOp(predInstrs[lastIdx])) lastIdx--;
			if (lastIdx < 1 || !predInstrs[lastIdx].IsLdcI4())
				continue;
			int prevIdx = lastIdx - 1;
			while (prevIdx >= 0 && IsHarmlessOp(predInstrs[prevIdx])) prevIdx--;
			if (prevIdx < 0 || !predInstrs[prevIdx].IsLdcI4())
				continue;
			if (predInstrs[lastIdx].GetLdcI4Value() != predInstrs[prevIdx].GetLdcI4Value())
				continue;
			return (uint)predInstrs[lastIdx].GetLdcI4Value();
		}

		return null;
	}
}
