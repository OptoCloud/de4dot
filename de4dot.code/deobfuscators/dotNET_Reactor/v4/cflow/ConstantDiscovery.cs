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
using de4dot.blocks;
using dnlib.DotNet.Emit;

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4.cflow;

/// <summary>
///     Constant discovery for XOR-switch dispatch deobfuscation.
/// </summary>
class ConstantDiscovery {
	readonly IList<Local> locals;
	readonly PatternMatcher patternMatcher;

	internal ConstantDiscovery(IList<Local> locals, PatternMatcher patternMatcher) {
		this.locals = locals;
		this.patternMatcher = patternMatcher;
	}

	/// <summary>
	///     Scans case-region blocks to find the original state variable S that case
	///     blocks write to via ldc.i4 CONST; stloc S.
	/// </summary>
	internal Local FindOriginalStateVar(Block switchBlock, DispatchInfo info, Dictionary<Block, int> blockToCase) {
		var candidates = new Dictionary<Local, int>();

		foreach (var kv in blockToCase) {
			var block = kv.Key;
			if (block == switchBlock)
				continue;

			var instrs = block.Instructions;
			for (int i = instrs.Count - 1; i >= 1; i--) {
				if (!instrs[i].IsStloc())
					continue;
				if (!instrs[i - 1].IsLdcI4())
					continue;
				var local = Instr.GetLocalVar(locals, instrs[i]);
				if (local == null)
					continue;
				if (local == info.StateVar || local == info.DispatchVar)
					continue;

				if (!CfgAnalysis.IsTrailingSafe(instrs, i + 1))
					continue;

				if (!candidates.TryGetValue(local, out int count))
					count = 0;
				candidates[local] = count + 1;
			}
		}

		Local best = null;
		int bestCount = 0;
		foreach (var kv in candidates) {
			if (kv.Value > bestCount) {
				bestCount = kv.Value;
				best = kv.Key;
			}
		}

		return best;
	}

	/// <summary>
	///     Finds a constant value that feeds the dispatch state variable.
	///     Returns (stateVal, startIdx, patternLen).
	/// </summary>
	internal (uint stateVal, int startIdx, int patternLen) FindConstantForDispatch(List<Instr> instrs,
		DispatchInfo info) {
		var targetVar = info.HasEmbeddedMul && info.OriginalStateVar != null
			? info.OriginalStateVar
			: info.StateVar;

		if (targetVar != null) {
			for (int i = instrs.Count - 1; i >= 1; i--) {
				if (!instrs[i].IsStloc())
					continue;
				var local = Instr.GetLocalVar(locals, instrs[i]);
				if (local != targetVar)
					continue;

				var result = patternMatcher.SliceBackward(instrs, i - 1);
				if (result != null) {
					int startIdx = result.Value.startIdx;
					int patternLen = i - startIdx + 1;
					return (result.Value.value, startIdx, patternLen);
				}

				break;
			}
		}
		else {
			int effectiveEnd = CfgAnalysis.FindEffectiveEnd(instrs);
			if (effectiveEnd >= 0) {
				var result = patternMatcher.SliceBackward(instrs, effectiveEnd);
				if (result != null) {
					int startIdx = result.Value.startIdx;
					int patternLen = effectiveEnd - startIdx + 1;
					return (result.Value.value, startIdx, patternLen);
				}
			}
		}

		var fwd = ForwardEvaluateStore(instrs, targetVar);
		if (fwd != null)
			return fwd.Value;

		return (0, -1, 0);
	}

	/// <summary>
	///     Forward-evaluates a block's instructions to find the constant stored to
	///     targetVar. Handles dup, conv, nop, and stack shapes naturally.
	/// </summary>
	internal (uint stateVal, int startIdx, int patternLen)? ForwardEvaluateStore(
		List<Instr> instrs, Local targetVar) {
		var stack = new List<(uint value, int startIdx)>();
		var localValues = new Dictionary<Local, (uint value, int startIdx)>();

		int? lastStoreIdx = null;
		uint? lastStoreVal = null;
		int lastStoreStartIdx = -1;

		for (int i = 0; i < instrs.Count; i++) {
			var instr = instrs[i];
			var code = instr.OpCode.Code;

			if (instr.IsLdcI4()) {
				stack.Add(((uint)instr.GetLdcI4Value(), i));
				continue;
			}

			if (instr.IsLdloc()) {
				var local = Instr.GetLocalVar(locals, instr);
				if (local != null && localValues.TryGetValue(local, out var entry)) {
					stack.Add(entry);
					continue;
				}

				stack.Clear();
				continue;
			}

			if (instr.IsStloc()) {
				var local = Instr.GetLocalVar(locals, instr);
				if (stack.Count < 1) {
					if (local == targetVar) {
						lastStoreIdx = null;
						lastStoreVal = null;
					}

					stack.Clear();
					continue;
				}

				var top = stack[stack.Count - 1];
				stack.RemoveAt(stack.Count - 1);
				if (local != null) {
					localValues[local] = top;
					if (local == targetVar) {
						lastStoreIdx = i;
						lastStoreVal = top.value;
						lastStoreStartIdx = top.startIdx;
					}
				}

				continue;
			}

			if (code == Code.Xor || code == Code.Mul || code == Code.Add || code == Code.Sub) {
				if (stack.Count < 2) {
					stack.Clear();
					continue;
				}

				var r = stack[stack.Count - 1];
				stack.RemoveAt(stack.Count - 1);
				var l = stack[stack.Count - 1];
				stack.RemoveAt(stack.Count - 1);
				uint result = DomainMath.ApplyBinaryOp(code, l.value, r.value);
				stack.Add((result, Math.Min(l.startIdx, r.startIdx)));
				continue;
			}

			if (code == Code.Dup) {
				if (stack.Count < 1) {
					stack.Clear();
					continue;
				}

				stack.Add(stack[stack.Count - 1]);
				continue;
			}

			if (code == Code.Conv_I4 || code == Code.Conv_U4 || code == Code.Nop)
				continue;
			if (code == Code.Br || code == Code.Br_S)
				break;
			if (code == Code.Pop) {
				if (stack.Count >= 1)
					stack.RemoveAt(stack.Count - 1);
				else
					stack.Clear();
				continue;
			}

			stack.Clear();
			localValues.Clear();
		}

		if (targetVar != null && lastStoreIdx.HasValue && lastStoreVal.HasValue) {
			int patternLen = lastStoreIdx.Value - lastStoreStartIdx + 1;
			if (patternLen > 0 && patternLen <= 20)
				return (lastStoreVal.Value, lastStoreStartIdx, patternLen);
		}

		if (targetVar == null && stack.Count >= 1) {
			var top = stack[stack.Count - 1];
			int effectiveEnd = CfgAnalysis.FindEffectiveEnd(instrs);
			if (effectiveEnd >= 0) {
				int patternLen = effectiveEnd - top.startIdx + 1;
				if (patternLen > 0 && patternLen <= 20)
					return (top.value, top.startIdx, patternLen);
			}
		}

		return null;
	}

	/// <summary>
	///     Collects dispatch vals from all discoverable sources.
	/// </summary>
	internal Dictionary<int, HashSet<uint>> CollectAllDispatchVals(Block switchBlock, DispatchInfo info,
		HashSet<Block> reverseReachable, Dictionary<Block, int> blockToCase) {
		var caseToDispatchVals = new Dictionary<int, HashSet<uint>>();

		if (info.InternalStateVarInput.HasValue) {
			uint dv = DomainMath.StateToDispatchVal(info, info.InternalStateVarInput.Value);
			AddDispatchVal(caseToDispatchVals, info, dv);
		}

		var eligible = new HashSet<Block>();
		foreach (var kv in blockToCase)
			eligible.Add(kv.Key);
		foreach (var source in switchBlock.Sources) {
			if (source == switchBlock)
				continue;
			eligible.Add(source);
			if (CfgAnalysis.IsFunnelBlock(source)) {
				foreach (var funnelSource in source.Sources) {
					if (funnelSource != switchBlock)
						eligible.Add(funnelSource);
				}
			}
		}

		foreach (var block in eligible) {
			if (block == switchBlock)
				continue;
			if (!reverseReachable.Contains(block))
				continue;
			(uint stateVal, int startIdx, _) = FindConstantForDispatch(block.Instructions, info);
			if (startIdx >= 0) {
				uint svInput = DomainMath.StateValToStateVarInput(info, stateVal);
				uint dv = DomainMath.StateToDispatchVal(info, svInput);
				AddDispatchVal(caseToDispatchVals, info, dv);
			}
		}

		foreach (var source in switchBlock.Sources) {
			if (source == switchBlock)
				continue;
			if (!CfgAnalysis.IsPopThroughBlock(source))
				continue;
			foreach (var pred in source.Sources) {
				if (pred == switchBlock || pred == source)
					continue;
				if (!reverseReachable.Contains(pred))
					continue;
				var instrs = pred.Instructions;
				int lastIdx = CfgAnalysis.FindEffectiveEnd(instrs);
				if (lastIdx < 1 || instrs[lastIdx].OpCode.Code != Code.Dup)
					continue;
				var result = patternMatcher.SliceBackward(instrs, lastIdx - 1);
				if (result == null)
					continue;
				uint svInput = DomainMath.StateValToStateVarInput(info, result.Value.value);
				uint dv = DomainMath.StateToDispatchVal(info, svInput);
				AddDispatchVal(caseToDispatchVals, info, dv);
			}
		}

		// Seed for split-embedded-mul: find initial StateVar value when constant
		// discovery finds nothing (case blocks use mul-xor transitions, not constant stores).
		// Falls back to 0 (default local initialization) if no explicit store is found.
		if (info.SplitEmbeddedMul && caseToDispatchVals.Count == 0) {
			uint? initialValue = TryFindInitialStateVarValue(switchBlock, info, reverseReachable);
			uint seedValue = initialValue ?? 0;
			uint dv = DomainMath.StateToDispatchVal(info, seedValue);
			AddDispatchVal(caseToDispatchVals, info, dv);
		}

		// Seeding for xor+stack dispatches where all case bodies use per-case mul-xor
		// transitions and standard constant discovery finds nothing.
		// External predecessor blocks (sources of the switch block that are NOT in
		// blockToCase, i.e., not reachable from any switch target) carry the initial
		// dispatch value at method entry. C# zero-initializes locals, so with
		// DispatchVar starting at 0 and a block pattern (ldloc V; ldc M; mul; ldc X2; xor):
		//   stackValue = 0 * M ^ X2 = X2
		//   initialDv  = X2 ^ XorKey
		// PropagateMultiplyXor then follows the per-case chain from this seed.
		if (info.StateVar == null && info.DispatchVar != null && caseToDispatchVals.Count == 0) {
			foreach (var source in switchBlock.Sources) {
				if (source == switchBlock)
					continue;
				if (blockToCase.ContainsKey(source))
					continue; // skip case bodies — only the initial entry matters
				if (!reverseReachable.Contains(source))
					continue;
				if (!patternMatcher.TryGetMultiplyXorPattern(source, info,
					    out _, out uint xor2Const, out _, out _))
					continue;
				// When DispatchVar=0: stackValue = 0 * mulConst ^ xor2Const = xor2Const
				uint dv = unchecked(xor2Const ^ info.XorKey);
				AddDispatchVal(caseToDispatchVals, info, dv);
			}
		}

		PropagateMultiplyXor(switchBlock, info, caseToDispatchVals, blockToCase);

		return caseToDispatchVals;
	}

	internal static void AddDispatchVal(Dictionary<int, HashSet<uint>> caseToDispatchVals, DispatchInfo info, uint dv) {
		int ci = DomainMath.NormalizeCaseIndex(info, dv);
		if (!caseToDispatchVals.TryGetValue(ci, out var set))
			caseToDispatchVals[ci] = set = new HashSet<uint>();
		set.Add(dv);
	}

	/// <summary>
	///     Seeds dispatch vals for "pure self-loop" embedded-mul dispatches.
	/// </summary>
	internal void SeedSelfLoopDispatchVals(Block switchBlock, DispatchInfo info,
		Dictionary<int, HashSet<uint>> caseToDispatchVals, HashSet<Block> reverseReachable) {
		if (!info.HasEmbeddedMul || info.StateVar == null)
			return;

		uint? initialValue = TryFindInitialStateVarValue(switchBlock, info, reverseReachable);
		// .NET locals default-initialize to 0. If no explicit store is found,
		// seed with 0 — the simulation hard gate will reject incorrect rewrites.
		if (initialValue == null)
			initialValue = 0;

		uint dv = DomainMath.StateToDispatchVal(info, initialValue.Value);
		var seen = new HashSet<uint>();
		int maxIter = (int)info.Modulus + 1;
		while (maxIter-- > 0 && seen.Add(dv)) {
			AddDispatchVal(caseToDispatchVals, info, dv);
			dv = DomainMath.SelfLoopNext(info, dv);
		}
	}

	uint? TryFindInitialStateVarValue(Block switchBlock, DispatchInfo info, HashSet<Block> reverseReachable) {
		foreach (var block in reverseReachable) {
			if (block == switchBlock)
				continue;
			var instrs = block.Instructions;
			for (int i = instrs.Count - 1; i >= 1; i--) {
				if (!instrs[i].IsStloc())
					continue;
				var local = Instr.GetLocalVar(locals, instrs[i]);
				if (local != info.StateVar)
					continue;
				var result = patternMatcher.SliceBackward(instrs, i - 1);
				if (result != null && CfgAnalysis.IsTrailingSafe(instrs, i + 1))
					return result.Value.value;
			}
		}

		return null;
	}

	/// <summary>
	///     Fixed-point propagation through multiply-XOR chains.
	///     Capped at maxTotalVals total dispatch vals to prevent unbounded growth
	///     when the mul-xor orbit is long (can be up to 2^32 for pathological constants).
	/// </summary>
	internal void PropagateMultiplyXor(Block switchBlock, DispatchInfo info,
		Dictionary<int, HashSet<uint>> caseToDispatchVals, Dictionary<Block, int> blockToCase) {
		if (switchBlock.Targets == null)
			return;

		// isStateDomain: true when the mul-xor transition loads StateVar (not DispatchVar)
		var caseToMulXorPatterns = new Dictionary<int, List<(uint mulConst, uint xor2Const, bool isStateDomain)>>();

		void AddMulXorPattern(Block block, int ownerCase) {
			if (!patternMatcher.TryGetMultiplyXorPattern(block, info,
				    out uint mulConst, out uint xor2Const, out _, out _, out var loadedVar))
				return;
			// isStateDomain only applies to split dispatches where case blocks
			// load StateVar instead of DispatchVar. For non-split dispatches,
			// always use dispatch-val domain to match committed behavior.
			bool isStateDomain = info.SplitEmbeddedMul && info.HasEmbeddedMul
			                                           && loadedVar != null && loadedVar != info.DispatchVar
			                                           && loadedVar == info.StateVar;
			if (!caseToMulXorPatterns.TryGetValue(ownerCase, out var patterns))
				caseToMulXorPatterns[ownerCase] = patterns = new List<(uint, uint, bool)>();
			var pat = (mulConst, xor2Const, isStateDomain);
			if (!patterns.Contains(pat))
				patterns.Add(pat);
		}

		foreach (var source in switchBlock.Sources) {
			if (source == switchBlock)
				continue;
			if (!blockToCase.TryGetValue(source, out int ownerCase))
				continue;
			AddMulXorPattern(source, ownerCase);
		}

		// For split dispatches, also scan case blocks from blockToCase.
		// These blocks branch to a predecessor, not directly to the switch,
		// so they aren't in switchBlock.Sources.
		if (info.SplitEmbeddedMul) {
			foreach (var kv in blockToCase) {
				if (kv.Key == switchBlock)
					continue;
				AddMulXorPattern(kv.Key, kv.Value);
			}
		}

		if (caseToMulXorPatterns.Count == 0)
			return;

		var worklist = new Queue<(int caseIdx, uint dispatchVal)>();
		var processed = new HashSet<(int, uint)>();

		foreach (var kv in caseToDispatchVals) {
			if (!caseToMulXorPatterns.ContainsKey(kv.Key))
				continue;
			foreach (uint dv in kv.Value) {
				if (processed.Add((kv.Key, dv)))
					worklist.Enqueue((kv.Key, dv));
			}
		}

		int maxIterations = 100_000;
		int iterations = 0;
		while (worklist.Count > 0) {
			if (++iterations > maxIterations)
				break;

			(int caseIdx, uint dispatchVal) = worklist.Dequeue();

			if (!caseToMulXorPatterns.TryGetValue(caseIdx, out var patterns))
				continue;

			foreach ((uint mulConst, uint xor2Const, bool isStateDomain) in patterns) {
				uint nextState;
				if (isStateDomain) {
					// Transition loads StateVar: convert dispatch val → stateVar, apply mul-xor
					uint? sv = DomainMath.DispatchValToStateVar(info, dispatchVal);
					if (sv == null)
						continue;
					nextState = DomainMath.MulXorToNextState(sv.Value, mulConst, xor2Const);
				}
				else {
					nextState = DomainMath.MulXorToNextState(dispatchVal, mulConst, xor2Const);
				}

				uint svInput = DomainMath.StateValToStateVarInput(info, nextState);
				uint newDv = DomainMath.StateToDispatchVal(info, svInput);
				int newCase = DomainMath.NormalizeCaseIndex(info, newDv);

				if (!caseToDispatchVals.TryGetValue(newCase, out var newSet))
					caseToDispatchVals[newCase] = newSet = new HashSet<uint>();

				if (newSet.Add(newDv)) {
					if (processed.Add((newCase, newDv)))
						worklist.Enqueue((newCase, newDv));
				}
			}
		}
	}
}
