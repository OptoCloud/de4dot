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
///     CFG analysis helpers for XOR-switch dispatch deobfuscation.
/// </summary>
static class CfgAnalysis {
	/// <summary>
	///     Reverse BFS from target: returns the set of all blocks that can reach 'target'
	///     by traversing the Sources (predecessor) links. O(N+E) — computed once per dispatch.
	/// </summary>
	internal static HashSet<Block> ComputeReverseReachable(Block target, int maxNodes = 5000) {
		var reachable = new HashSet<Block> { target };
		var queue = new Queue<Block>();
		queue.Enqueue(target);

		while (queue.Count > 0 && reachable.Count < maxNodes) {
			var block = queue.Dequeue();
			foreach (var pred in block.Sources) {
				if (pred == null)
					continue;
				if (reachable.Add(pred))
					queue.Enqueue(pred);
			}
		}

		return reachable;
	}

	/// <summary>
	///     BFS from each switch target to map every reachable block to its owning case index.
	///     Blocks reachable from multiple cases are marked ambiguous and excluded.
	///     The switch block itself is always excluded from the map.
	/// </summary>
	internal static Dictionary<Block, int> BuildBlockToCase(Block switchBlock) {
		var blockToCase = new Dictionary<Block, int>();
		var ambiguousBlocks = new HashSet<Block>();
		if (switchBlock.Targets == null)
			return blockToCase;

		var queue = new Queue<(Block block, int caseIdx)>();
		var seenPair = new HashSet<(Block, int)>();

		// Seed: enqueue each case target with its case index
		for (int i = 0; i < switchBlock.Targets.Count; i++) {
			var caseBlock = switchBlock.Targets[i];
			if (caseBlock == null || caseBlock == switchBlock)
				continue;
			ClaimOrMarkAmbiguous(blockToCase, ambiguousBlocks, caseBlock, i);
			if (seenPair.Add((caseBlock, i)))
				queue.Enqueue((caseBlock, i));
		}

		// Multi-source BFS: each wave carries its case index
		while (queue.Count > 0) {
			(var block, int caseIdx) = queue.Dequeue();

			// Don't expand ambiguous blocks
			if (ambiguousBlocks.Contains(block))
				continue;

			// Check if this block was claimed by a different case since enqueue
			if (blockToCase.TryGetValue(block, out int curCase) && curCase != caseIdx) {
				ambiguousBlocks.Add(block);
				blockToCase.Remove(block);
				continue;
			}

			// Expand successors
			foreach (var succ in block.GetTargets()) {
				if (succ == null || succ == switchBlock)
					continue;
				if (!seenPair.Add((succ, caseIdx)))
					continue; // this case wave already explored it

				ClaimOrMarkAmbiguous(blockToCase, ambiguousBlocks, succ, caseIdx);
				queue.Enqueue((succ, caseIdx));
			}
		}

		return blockToCase;
	}

	/// <summary>
	///     Claims a block for a case index, or marks it ambiguous if already claimed by a different case.
	/// </summary>
	static void ClaimOrMarkAmbiguous(Dictionary<Block, int> blockToCase,
		HashSet<Block> ambiguous, Block block, int caseIdx) {
		if (ambiguous.Contains(block))
			return;
		if (blockToCase.TryGetValue(block, out int existingCase)) {
			if (existingCase != caseIdx) {
				ambiguous.Add(block);
				blockToCase.Remove(block);
			}
		}
		else {
			blockToCase[block] = caseIdx;
		}
	}

	/// <summary>
	///     Returns true if the block is a simple pass-through (funnel): only nop/br instructions.
	///     These act as shared junction points between case exits and the dispatch.
	/// </summary>
	internal static bool IsFunnelBlock(Block block) {
		var instrs = block.Instructions;
		if (instrs.Count == 0)
			return true;
		for (int i = 0; i < instrs.Count; i++) {
			var code = instrs[i].OpCode.Code;
			if (code != Code.Nop && code != Code.Br && code != Code.Br_S)
				return false;
		}

		return true;
	}

	/// <summary>
	///     Returns true if the block is a pop-through relay: contains only pop + nop/br.
	///     These appear in opaque predicate patterns where two conditional paths each
	///     push a constant via dup, then merge at this pop block before the dispatch.
	/// </summary>
	internal static bool IsPopThroughBlock(Block block) {
		var instrs = block.Instructions;
		if (instrs.Count == 0)
			return false;
		bool hasPop = false;
		for (int i = 0; i < instrs.Count; i++) {
			var code = instrs[i].OpCode.Code;
			if (code == Code.Pop) {
				hasPop = true;
				continue;
			}

			if (code != Code.Nop && code != Code.Br && code != Code.Br_S)
				return false;
		}

		return hasPop;
	}

	/// <summary>
	///     Returns true if instructions from 'fromIdx' to end are safe to remove:
	///     only nop/br or nothing follows. This ensures we don't delete real code.
	/// </summary>
	internal static bool IsTrailingSafe(List<Instr> instrs, int fromIdx) {
		for (int i = fromIdx; i < instrs.Count; i++) {
			var code = instrs[i].OpCode.Code;
			if (code != Code.Nop && code != Code.Br && code != Code.Br_S)
				return false;
		}

		return true;
	}

	/// <summary>
	///     Centralized safety check before every rewrite. Verifies:
	///     1. Switch targets list exists
	///     2. Modulus == switch target count (arithmetic consistency)
	///     3. Case index is in bounds [0, Targets.Count)
	///     4. Target block is not null
	///     Returns the target block on success, null on failure (skip rewrite).
	/// </summary>
	internal static Block VerifyAndGetTarget(Block switchBlock, DispatchInfo info, int caseIdx) {
		if (switchBlock.Targets == null)
			return null;
		if (info.Modulus != (uint)switchBlock.Targets.Count)
			return null;
		if (caseIdx < 0 || caseIdx >= switchBlock.Targets.Count)
			return null;
		return switchBlock.Targets[caseIdx];
	}

	/// <summary>
	///     Returns the index of the last instruction that is not nop/br/br.s,
	///     or -1 if the block is empty or contains only trailing instructions.
	/// </summary>
	internal static int FindEffectiveEnd(List<Instr> instrs) {
		int idx = instrs.Count - 1;
		while (idx >= 0) {
			var code = instrs[idx].OpCode.Code;
			if (code != Code.Nop && code != Code.Br && code != Code.Br_S)
				break;
			idx--;
		}

		return idx;
	}
}
