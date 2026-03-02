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
///     Rebuilds control flow from sliced blocks and dispatch values.
///     For each case block with a recognized state update, computes the
///     exit state directly from the block's own slice data (not from
///     per-case traced exits), verifies via simulation, computes exact
///     stack cleanup via StackAnalyzer, and applies the rewrite.
///     Falls back per-block (not per-dispatch): blocks that can't be
///     resolved are left for the legacy pipeline.
/// </summary>
static class Rebuilder {
	// Diagnostic counters (reset per call, read by caller if needed)
	internal static int SkipNone, SkipNoTrace, SkipUnknownExit, SkipResolve,
		SkipTarget, SkipScope, SkipBounds, SkipBranch, SkipNoop, Applied;

	internal static bool Rebuild(DispatchModel model,
		Dictionary<int, (StateValue entry, StateValue exit)> traced,
		Dictionary<Block, SlicedBlock> sliced,
		Dictionary<Block, int> blockToCase) {
		return Rebuild(model, traced, sliced, blockToCase, null);
	}

	internal static bool Rebuild(DispatchModel model,
		Dictionary<int, (StateValue entry, StateValue exit)> traced,
		Dictionary<Block, SlicedBlock> sliced,
		Dictionary<Block, int> blockToCase,
		Dictionary<int, HashSet<uint>> caseToDispatchVals) {
		SkipNone = SkipNoTrace = SkipUnknownExit = SkipResolve = SkipTarget = 0;
		SkipScope = SkipBounds = SkipBranch = SkipNoop = Applied = 0;

		if (sliced == null)
			return false;

		var switchBlock = model.SwitchBlock;
		var info = model.Info;
		var dvToSv = model.DvToSv;
		bool modified = false;

		foreach (var kv in sliced) {
			var block = kv.Key;
			var slice = kv.Value;

			// Only handle blocks with recognized state updates
			if (slice.UpdateKind == StateUpdateKind.None) {
				SkipNone++;
				continue;
			}

			// Compute per-block exit values directly from the block's own slice data.
			// This is correct for multi-block cases and avoids the per-case traced exit
			// picking the wrong block (e.g., a trampoline instead of the real case body).
			Block target = null;
			int targetCase = -1;

			if (slice.UpdateKind == StateUpdateKind.Constant) {
				// Constant: use this block's own ConstantNext (STATE-domain value)
				if (!slice.ConstantNext.HasValue) {
					SkipResolve++;
					continue;
				}
				var exitVals = new HashSet<uint> { slice.ConstantNext.Value };
				var resolved = model.ResolveUniform(exitVals,
					sv => DomainMath.StateValToStateVarInput(info, sv));
				if (resolved == null) {
					SkipResolve++;
					continue;
				}
				target = resolved.Value.target;
				targetCase = resolved.Value.caseIdx;
			}
			else if (slice.UpdateKind == StateUpdateKind.MulXor) {
				// MulXor: compute exit from this block's mul/xor constants and entry dispatch vals.
				// Entry dispatch vals come from caseToDispatchVals (preferred) or traced entry.
				HashSet<uint> entryDvs = null;
				if (caseToDispatchVals != null)
					caseToDispatchVals.TryGetValue(slice.CaseIndex, out entryDvs);
				if ((entryDvs == null || entryDvs.Count == 0) && traced != null &&
				    traced.TryGetValue(slice.CaseIndex, out var tracedState) &&
				    !tracedState.entry.IsUnknown && tracedState.entry.Values != null) {
					entryDvs = new HashSet<uint>(tracedState.entry.Values);
				}
				if (entryDvs == null || entryDvs.Count == 0) {
					SkipNoTrace++;
					continue;
				}

				// Compute exit STATE-domain values from this block's transition
				var exitVals = new HashSet<uint>();
				bool ok = true;
				foreach (uint dv in entryDvs) {
					uint? mulInput = DomainMath.DispatchValToMulXorInput(
						info, dv, slice.InputDomain, slice.CaseIndex, dvToSv);
					if (mulInput == null) { ok = false; break; }
					uint nextState = DomainMath.MulXorToNextState(mulInput.Value, slice.MulConst, slice.XorConst);
					exitVals.Add(nextState);
				}
				if (!ok || exitVals.Count == 0) {
					SkipResolve++;
					continue;
				}

				var resolved = model.ResolveUniform(exitVals,
					sv => DomainMath.StateValToStateVarInput(info, sv));
				if (resolved == null) {
					SkipResolve++;
					continue;
				}
				target = resolved.Value.target;
				targetCase = resolved.Value.caseIdx;
			}
			else if (slice.UpdateKind == StateUpdateKind.SelfLoop) {
				// SelfLoop: compute exit from entry dispatch vals via SelfLoopNext.
				HashSet<uint> entryDvs = null;
				if (caseToDispatchVals != null)
					caseToDispatchVals.TryGetValue(slice.CaseIndex, out entryDvs);
				if ((entryDvs == null || entryDvs.Count == 0) && traced != null &&
				    traced.TryGetValue(slice.CaseIndex, out var tracedState) &&
				    !tracedState.entry.IsUnknown && tracedState.entry.Values != null) {
					entryDvs = new HashSet<uint>(tracedState.entry.Values);
				}
				if (entryDvs == null || entryDvs.Count == 0) {
					SkipNoTrace++;
					continue;
				}

				// SelfLoop exit values are DISPATCH-VAL domain
				var exitVals = new HashSet<uint>();
				foreach (uint dv in entryDvs)
					exitVals.Add(DomainMath.SelfLoopNext(info, dv));

				int? resolvedCase = null;
				bool allMatch = true;
				foreach (uint exitDv in exitVals) {
					int ci = DomainMath.NormalizeCaseIndex(info, exitDv);
					if (resolvedCase == null)
						resolvedCase = ci;
					else if (resolvedCase.Value != ci) {
						allMatch = false;
						break;
					}
				}

				if (!allMatch || resolvedCase == null) {
					SkipResolve++;
					continue;
				}

				// Verify using an entry dispatch val
				uint? firstEntryDv = null;
				foreach (uint v in entryDvs) {
					firstEntryDv = v;
					break;
				}

				if (!firstEntryDv.HasValue || !model.Verify(firstEntryDv.Value, resolvedCase.Value)) {
					SkipResolve++;
					continue;
				}

				target = model.GetTarget(resolvedCase.Value);
				targetCase = resolvedCase.Value;
			}

			if (target == null) {
				SkipTarget++;
				continue;
			}

			// Don't rewrite across exception handler scope boundaries
			if (block.Parent != target.Parent) {
				SkipScope++;
				continue;
			}

			// Compute exact pop count at the cut point
			int popCount = slice.StackDepthAtCut;
			int numToRemove = block.Instructions.Count - slice.PayloadEnd;

			if (numToRemove < 0 || numToRemove > block.Instructions.Count) {
				SkipBounds++;
				continue;
			}

			// If the block has a conditional/switch branch (Targets != null),
			// the rewrite must remove the branch instruction itself. Otherwise
			// ReplaceLastInstrsWithBranch disconnects Targets (setting it null)
			// but leaves the branch instruction with a stale operand, causing
			// "removed instruction" errors when dnlib writes the method body.
			if (block.Targets != null && block.Targets.Count > 0) {
				if (numToRemove == 0) {
					SkipBranch++;
					continue;
				}
				// Ensure the branch instruction (always last) is within the removal range
				if (slice.PayloadEnd >= block.Instructions.Count) {
					SkipBranch++;
					continue;
				}
			}

			// Skip no-op rewrites (block already branches to target with nothing to change).
			// Prevents infinite cycling when already-rewritten blocks get re-sliced as
			// SelfLoop (no pattern found → fallback → PayloadEnd=instrs.Count → 0 to remove).
			if (numToRemove == 0 && popCount == 0 &&
			    block.FallThrough == target &&
			    (block.Targets == null || block.Targets.Count == 0)) {
				SkipNoop++;
				continue;
			}

			// Apply rewrite: remove state-update instructions and branch to target
			block.ReplaceLastInstrsWithBranch(numToRemove, target);

			// Insert exact number of pops for stack cleanup
			for (int i = 0; i < popCount; i++)
				block.Add(new Instr(OpCodes.Pop.ToInstruction()));

			Applied++;
			modified = true;
		}

		return modified;
	}
}
