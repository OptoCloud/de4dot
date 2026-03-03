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

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4.xorswitch;

/// <summary>
///     Applies resolved edges to the CFG. Pure transformation.
/// </summary>
static class SwitchRewriter {
	public static int Apply(DispatchNode dispatch, List<ResolvedEdge> edges) {
		int applied = 0;

		foreach (var edge in edges) {
			// Self-loop guard: never redirect a block to itself
			if (edge.Target == edge.Predecessor)
				continue;

			// Scope check: predecessor and target must be in the same exception handler scope
			if (edge.Predecessor.Parent != edge.Target.Parent)
				continue;

			// Noop check: skip if predecessor already branches directly to target
			if (AlreadyBranchesTo(edge.Predecessor, edge.Target))
				continue;

			// For conditional predecessors (InstructionsToRemove == 0), retarget the
			// edge that goes to the switch block
			if (edge.InstructionsToRemove == 0 && edge.Predecessor.IsConditionalBranch()) {
				if (RetargetConditionalEdge(edge.Predecessor, dispatch.SwitchBlock, edge.Target))
					applied++;
				continue;
			}

			// Standard rewrite: replace tail instructions with branch to target
			try {
				edge.Predecessor.ReplaceLastInstrsWithBranch(edge.InstructionsToRemove, edge.Target);
			}
			catch {
				continue;
			}

			// Insert pop instructions for stack cleanup
			for (int i = 0; i < edge.StackCleanupPops; i++)
				edge.Predecessor.Instructions.Add(new Instr(OpCodes.Pop.ToInstruction()));

			applied++;
		}

		// Clean up dead cases after rewriting
		CleanupDeadCases(dispatch, edges);

		return applied;
	}

	static bool AlreadyBranchesTo(Block block, Block target) {
		var onlyTarget = block.GetOnlyTarget();
		return onlyTarget == target;
	}

	/// <summary>
	///     Retarget a conditional branch edge from the switch block to the resolved target.
	/// </summary>
	static bool RetargetConditionalEdge(Block predecessor, Block switchBlock, Block target) {
		// Check fallthrough
		if (predecessor.FallThrough == switchBlock) {
			predecessor.SetNewFallThrough(target);
			return true;
		}

		// Check explicit targets
		if (predecessor.Targets != null) {
			for (int i = 0; i < predecessor.Targets.Count; i++) {
				if (predecessor.Targets[i] == switchBlock) {
					predecessor.SetNewTarget(i, target);
					return true;
				}
			}
		}

		return false;
	}

	/// <summary>
	///     After rewriting, check each case target. If a target has no remaining sources
	///     (other than the switch block) and all its predecessors were rewritten, it's dead.
	/// </summary>
	static void CleanupDeadCases(DispatchNode dispatch, List<ResolvedEdge> edges) {
		if (edges.Count == 0)
			return;

		foreach (var caseTarget in dispatch.CaseTargets) {
			if (caseTarget.Sources.Count == 0 && caseTarget.Parent != null) {
				try {
					caseTarget.Parent.RemoveGuaranteedDeadBlock(caseTarget);
				}
				catch {
					// Block may not be in the parent's baseBlocks list
				}
			}
		}
	}
}
