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
///     Rebuilds control flow from traced states. For each case block with a
///     resolved exit state, verifies via simulation, computes exact stack
///     cleanup via StackAnalyzer, and applies the rewrite.
///     Falls back per-case (not per-dispatch): cases that can't be resolved
///     are left for the legacy pipeline.
/// </summary>
static class Rebuilder {
	/// <summary>
	///     Returns true if any rewrites were applied.
	/// </summary>
	internal static bool Rebuild(DispatchModel model,
		Dictionary<int, (StateValue entry, StateValue exit)> traced,
		Dictionary<Block, SlicedBlock> sliced,
		Dictionary<Block, int> blockToCase) {
		if (traced == null || sliced == null)
			return false;

		var switchBlock = model.SwitchBlock;
		var info = model.Info;
		bool modified = false;

		foreach (var kv in sliced) {
			var block = kv.Key;
			var slice = kv.Value;

			// Only handle blocks with recognized state updates
			if (slice.UpdateKind == StateUpdateKind.None)
				continue;

			// Need traced exit state
			if (!traced.TryGetValue(slice.CaseIndex, out var tracedState))
				continue;

			var exitState = tracedState.exit;
			if (exitState.IsUnknown || exitState.Values == null)
				continue;

			// Compute target case from exit state values
			var exitVals = new HashSet<uint>(exitState.Values);
			Block target = null;
			int targetCase = -1;

			if (slice.UpdateKind == StateUpdateKind.Constant) {
				// Constant: exit is a single STATE-domain value
				var resolved = model.ResolveUniform(exitVals,
					sv => DomainMath.StateValToStateVarInput(info, sv));
				if (resolved == null)
					continue;
				target = resolved.Value.target;
				targetCase = resolved.Value.caseIdx;
			}
			else if (slice.UpdateKind == StateUpdateKind.MulXor) {
				// MulXor: exit values are STATE-domain (from MulXorToNextState)
				var resolved = model.ResolveUniform(exitVals,
					sv => DomainMath.StateValToStateVarInput(info, sv));
				if (resolved == null)
					continue;
				target = resolved.Value.target;
				targetCase = resolved.Value.caseIdx;
			}
			else if (slice.UpdateKind == StateUpdateKind.SelfLoop) {
				// SelfLoop: exit values are DISPATCH-VAL domain — SelfLoopNext(entryDv).
				// NormalizeCaseIndex of an exit val gives the correct TARGET case index.
				int? resolvedCase = null;
				bool allMatch = true;

				foreach (uint dv in exitVals) {
					int ci = DomainMath.NormalizeCaseIndex(info, dv);
					if (resolvedCase == null)
						resolvedCase = ci;
					else if (resolvedCase.Value != ci) {
						allMatch = false;
						break;
					}
				}

				if (!allMatch || resolvedCase == null)
					continue;

				// Verify using an ENTRY dispatch val (what stateVar/dispatchVar holds when
				// the case executes). The dispatch block computes entryDv * EmbMul ^ XorKey
				// and branches to (that % Modulus) = resolvedCase.
				// Using an exit val (SelfLoopNext(entryDv)) would simulate the NEXT iteration
				// and fail verification in the general case.
				uint? firstEntryDv = null;
				if (tracedState.entry.Values != null) {
					foreach (uint v in tracedState.entry.Values) {
						firstEntryDv = v;
						break;
					}
				}

				if (!firstEntryDv.HasValue)
					continue;

				if (!model.Verify(firstEntryDv.Value, resolvedCase.Value))
					continue;

				target = model.GetTarget(resolvedCase.Value);
				targetCase = resolvedCase.Value;
			}

			if (target == null)
				continue;

			// Compute exact pop count at the cut point
			int popCount = slice.StackDepthAtCut;
			int numToRemove = block.Instructions.Count - slice.PayloadEnd;

			if (numToRemove < 0 || numToRemove > block.Instructions.Count)
				continue;

			// Skip no-op rewrites (block already branches to target with nothing to change).
			// Prevents infinite cycling when already-rewritten blocks get re-sliced as
			// SelfLoop (no pattern found → fallback → PayloadEnd=instrs.Count → 0 to remove).
			if (numToRemove == 0 && popCount == 0 &&
			    block.FallThrough == target &&
			    (block.Targets == null || block.Targets.Count == 0))
				continue;

			// Apply rewrite: remove state-update instructions and branch to target
			block.ReplaceLastInstrsWithBranch(numToRemove, target);

			// Insert exact number of pops for stack cleanup
			for (int i = 0; i < popCount; i++)
				block.Add(new Instr(OpCodes.Pop.ToInstruction()));

			modified = true;
		}

		return modified;
	}
}
