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
///     Targeted constant-transition shortcut for loop-machine regions:
///     split-embedded-mul dispatchers where case blocks push or store
///     next-state constants (no OriginalStateVar). Two extraction strategies:
///     (1) stloc StateVar — block stores a constant to the state variable;
///     (2) stack-top — block pushes a constant on the stack (stored to
///         StateVar by a shared predecessor block downstream).
///     Resolves the target through the full domain math chain and branches
///     directly, bypassing the dispatch.
/// </summary>
static class LoopMachineRewriter {
	// Diagnostic counters (reset per call, read by caller)
	internal static int Detected, Rewrites;
	internal static int SkipNoStore, SkipResolve, SkipTarget, SkipScope;
	internal static int SkipStack, SkipBranch, SkipNoop;

	internal static bool TryRewrite(
		DispatchModel model,
		Dictionary<Block, int> blockToCase,
		PatternMatcher matcher,
		ConstantDiscovery discovery,
		IList<Local> locals) {
		Detected = Rewrites = 0;
		SkipNoStore = SkipResolve = SkipTarget = SkipScope = 0;
		SkipStack = SkipBranch = SkipNoop = 0;

		var info = model.Info;
		var switchBlock = model.SwitchBlock;

		// Detection gates
		if (!info.SplitEmbeddedMul)
			return false;
		if (info.OriginalStateVar != null)
			return false;
		if (info.StateVar == null)
			return false;

		Detected = 1;
		bool anyRewritten = false;

		foreach (var kv in blockToCase) {
			var block = kv.Key;
			if (block == switchBlock)
				continue;

			var instrs = block.Instructions;
			if (instrs.Count == 0)
				continue;

			// Skip conditional blocks — this is a cheap constant-store shortcut
			if (block.Targets != null && block.Targets.Count > 0) {
				SkipBranch++;
				continue;
			}

			// Extract constant state-transition value via two strategies:
			// (1) stloc StateVar — block stores a constant to the state variable
			// (2) stack-top — block pushes a constant on the stack (stored by
			//     a shared predecessor downstream)
			uint? extractedValue = null;
			int stateUpdateStart = -1;

			// Strategy 1: Find suffix stloc to StateVar with a constant
			for (int i = instrs.Count - 1; i >= 0; i--) {
				if (!instrs[i].IsStloc())
					continue;
				var local = Instr.GetLocalVar(locals, instrs[i]);
				if (local != info.StateVar)
					continue;
				if (!CfgAnalysis.IsTrailingSafe(instrs, i + 1))
					break;
				// Try SliceBackward for pure constants
				if (i >= 1) {
					var result = matcher.SliceBackward(instrs, i - 1);
					if (result != null) {
						extractedValue = result.Value.value;
						stateUpdateStart = result.Value.startIdx;
					}
				}
				// Fallback: ForwardEvaluateStore for block-internal expressions
				if (extractedValue == null) {
					var fwd = discovery.ForwardEvaluateStore(instrs, info.StateVar);
					if (fwd != null) {
						extractedValue = fwd.Value.stateVal;
						stateUpdateStart = fwd.Value.startIdx;
					}
				}
				break;
			}

			// Strategy 2: Stack-top constant extraction — for split dispatches
			// where case blocks push the state value on the stack (not stored to
			// StateVar within the block itself; a shared predecessor does the store).
			if (extractedValue == null) {
				// Forward evaluate with null targetVar finds the stack-top value
				var fwdStack = discovery.ForwardEvaluateStore(instrs, null);
				if (fwdStack != null) {
					extractedValue = fwdStack.Value.stateVal;
					stateUpdateStart = fwdStack.Value.startIdx;
				}
				// Fallback: SliceBackward from effective end (handles dup)
				if (extractedValue == null) {
					int effectiveEnd = CfgAnalysis.FindEffectiveEnd(instrs);
					if (effectiveEnd >= 0) {
						int sliceFrom = effectiveEnd;
						if (instrs[effectiveEnd].OpCode.Code == Code.Dup && effectiveEnd >= 1)
							sliceFrom = effectiveEnd - 1;
						var result = matcher.SliceBackward(instrs, sliceFrom);
						if (result != null) {
							extractedValue = result.Value.value;
							stateUpdateStart = result.Value.startIdx;
						}
					}
				}
			}

			if (extractedValue == null || stateUpdateStart < 0) {
				SkipNoStore++;
				continue;
			}

			// Compute target through full domain chain
			uint svInput = DomainMath.StateValToStateVarInput(info, extractedValue.Value);
			uint dispatchVal = DomainMath.StateToDispatchVal(info, svInput);
			int caseIdx = DomainMath.NormalizeCaseIndex(info, dispatchVal);

			// Verify via simulation
			if (!model.Verify(svInput, caseIdx)) {
				SkipResolve++;
				continue;
			}

			var target = model.GetTarget(caseIdx);
			if (target == null) {
				SkipTarget++;
				continue;
			}

			// Scope check: don't rewrite across exception handler boundaries
			if (block.Parent != target.Parent) {
				SkipScope++;
				continue;
			}

			// Stack safety
			int numToRemove = instrs.Count - stateUpdateStart;
			if (numToRemove < 0 || numToRemove > instrs.Count) {
				SkipStack++;
				continue;
			}

			int prefixExitDepth = StackAnalyzer.DepthAt(instrs, stateUpdateStart);
			if (prefixExitDepth < 0) {
				SkipStack++;
				continue;
			}

			// No-op check: block already branches to target with nothing to change
			if (numToRemove == 0 && prefixExitDepth == 0 && block.FallThrough == target) {
				SkipNoop++;
				continue;
			}

			// Apply rewrite: remove state-update suffix and branch to target
			block.ReplaceLastInstrsWithBranch(numToRemove, target);

			// Insert exact number of pops for stack cleanup
			for (int i = 0; i < prefixExitDepth; i++)
				block.Add(new Instr(OpCodes.Pop.ToInstruction()));

			Rewrites++;
			anyRewritten = true;
		}

		// Trampoline cleanup: redirect funnel blocks whose predecessors
		// were rewritten, eliminating dead relay blocks
		if (anyRewritten)
			CleanupTrampolines(blockToCase, switchBlock);

		return anyRewritten;
	}

	/// <summary>
	///     For funnel blocks (br-only relays) in the region with a single
	///     predecessor and single successor both in the region, redirects
	///     the predecessor directly to the successor.
	/// </summary>
	static void CleanupTrampolines(Dictionary<Block, int> blockToCase, Block switchBlock) {
		var funnels = new List<Block>();
		foreach (var kv in blockToCase) {
			if (kv.Key == switchBlock)
				continue;
			if (CfgAnalysis.IsFunnelBlock(kv.Key))
				funnels.Add(kv.Key);
		}

		foreach (var funnel in funnels) {
			var successor = funnel.FallThrough;
			if (successor == null)
				continue;

			// Single predecessor only
			if (funnel.Sources.Count != 1)
				continue;
			var predecessor = funnel.Sources[0];
			if (predecessor == switchBlock)
				continue;

			// Both must be in the region
			if (!blockToCase.ContainsKey(predecessor))
				continue;

			// Only redirect if predecessor unconditionally falls through to funnel
			if (predecessor.FallThrough != funnel)
				continue;
			if (predecessor.Targets != null && predecessor.Targets.Count > 0)
				continue;

			// Both in same scope
			if (predecessor.Parent != successor.Parent)
				continue;

			predecessor.ReplaceLastInstrsWithBranch(0, successor);
		}
	}
}
