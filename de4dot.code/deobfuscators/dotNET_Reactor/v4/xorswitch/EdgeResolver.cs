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
using de4dot.blocks.cflow;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4.xorswitch;

struct ResolvedEdge {
	public Block Predecessor;
	public Block Target;
	public int CaseIndex;
	public int InstructionsToRemove;
	public int StackCleanupPops;
	public int? TargetIncomingStateVar;
}

/// <summary>
///     For each predecessor of the switch block, uses InstructionEmulator to determine
///     which case it dispatches to. Five resolution phases:
///     1. Direct resolution (entry blocks that set stateVar = constant)
///     2. Seeded forward propagation (case-to-case using known stateVar values)
///     3. Brute-force seeding (disconnected subgraphs, try all known seeds)
///     4. Indirect resolution through passthrough blocks (e.g., pop blocks)
///     5. Algebraic seed extraction (compute next-case seeds from instruction constants)
///     Phases 2-5 are wrapped in a fixed-point loop that iterates until no new edges
///     or seeds are discovered.
/// </summary>
class EdgeResolver {
	readonly DispatchNode dispatch;
	readonly Blocks blocks;
	readonly MethodDef method;
	int resolvedCount;
	int failedCount;

	public int ResolvedCount => resolvedCount;
	public int FailedCount => failedCount;

	public EdgeResolver(DispatchNode dispatch, Blocks blocks) {
		this.dispatch = dispatch;
		this.blocks = blocks;
		method = blocks.Method;
	}

	/// <summary>
	///     Returns all predecessors of the dispatch (from both SwitchBlock and HeaderBlock).
	///     Excludes the SwitchBlock and HeaderBlock themselves.
	/// </summary>
	List<Block> GetDispatchPredecessors() {
		var seen = new HashSet<Block>();
		var result = new List<Block>();
		seen.Add(dispatch.SwitchBlock);
		if (dispatch.HeaderBlock != null)
			seen.Add(dispatch.HeaderBlock);

		foreach (var pred in dispatch.SwitchBlock.Sources) {
			if (seen.Add(pred))
				result.Add(pred);
		}
		if (dispatch.HeaderBlock != null) {
			foreach (var pred in dispatch.HeaderBlock.Sources) {
				if (seen.Add(pred))
					result.Add(pred);
			}
		}
		return result;
	}

	/// <summary>
	///     Checks if a block is part of the dispatch (either the switch block or header block).
	/// </summary>
	bool IsDispatchBlock(Block block) {
		return block == dispatch.SwitchBlock || block == dispatch.HeaderBlock;
	}

	/// <summary>
	///     Emulates the dispatch blocks (header + switch computation, excluding the switch itself).
	///     Handles both the split case (header + switch-only) and the unified case.
	/// </summary>
	void EmulateDispatchBlocks(InstructionEmulator emu, Block predecessor, out Int32Value preRemDividend) {
		preRemDividend = null;

		// Emulate header block if present and the predecessor targets it
		if (dispatch.HeaderBlock != null && dispatch.HeaderBlock.Sources.Contains(predecessor)) {
			var hdrInstrs = dispatch.HeaderBlock.Instructions;
			int hdrEnd = hdrInstrs.Count;
			if (hdrEnd > 0 && hdrInstrs[hdrEnd - 1].IsBr())
				hdrEnd--;
			emu.Emulate(hdrInstrs, 0, hdrEnd);
		}

		// Split switch block emulation at rem.un to capture pre-rem dividend
		var switchInstrs = dispatch.SwitchBlock.Instructions;
		int switchIdx = FindSwitchIndex(switchInstrs);
		if (switchIdx < 0)
			return;

		int remIdx = FindRemUnIndex(switchInstrs);
		int emuEnd = switchIdx;

		if (remIdx > 0 && remIdx < emuEnd) {
			emu.Emulate(switchInstrs, 0, remIdx);
			if (emu.StackSize() >= 2) {
				var divisor = emu.Pop();
				if (emu.Peek() is Int32Value dv)
					preRemDividend = dv;
				emu.Push(divisor);
				if (divisor is Int32Value divIv && divIv.AllBitsValid() &&
					(uint)divIv.Value != (uint)dispatch.CaseTargets.Count)
					preRemDividend = null;
			}
			emu.Emulate(switchInstrs, remIdx, emuEnd);
		}
		else if (emuEnd > 0) {
			emu.Emulate(switchInstrs, 0, emuEnd);
		}
	}

	public List<ResolvedEdge> ResolveAll() {
		var edges = new List<ResolvedEdge>();
		var resolved = new HashSet<Block>();

		// Phase 1: Direct resolution (unseeded)
		int maxIterations = dispatch.CaseTargets.Count * 4;
		for (int iter = 0; iter < maxIterations; iter++) {
			bool foundNew = false;

			foreach (var pred in GetDispatchPredecessors()) {
				if (resolved.Contains(pred))
					continue;
				if (pred.LastInstr.OpCode.Code == Code.Switch)
					continue;

				if (IsUnconditionalPredecessor(pred)) {
					var edge = TryResolveEdge(pred);
					if (edge != null) {
						edges.Add(edge.Value);
						resolved.Add(pred);
						resolvedCount++;
						foundNew = true;
					}
				}
				else if (IsConditionalPredecessor(pred)) {
					var condEdges = TryResolveConditionalEdge(pred);
					if (condEdges != null && condEdges.Count > 0) {
						edges.AddRange(condEdges);
						resolved.Add(pred);
						resolvedCount += condEdges.Count;
						foundNew = true;
					}
				}
			}

			if (!foundNew)
				break;
		}

		var indirectResolved = new HashSet<Block>();

		// Phases 2-5 with fixed-point iteration (requires stateVar)
		if (dispatch.StateVar != null) {
			var caseStateVar = new Dictionary<int, int>();
			foreach (var edge in edges) {
				if (edge.TargetIncomingStateVar.HasValue)
					caseStateVar[edge.CaseIndex] = edge.TargetIncomingStateVar.Value;
			}
			var allSeeds = new HashSet<int>(caseStateVar.Values);

			int maxOuterIter = dispatch.CaseTargets.Count * 3;
			for (int outerIter = 0; outerIter < maxOuterIter; outerIter++) {
				int prevEdgeCount = edges.Count;
				int prevSeedCount = allSeeds.Count;

				// Phase 2: Seeded forward propagation
				{
					int maxPhase2 = dispatch.CaseTargets.Count * 2;
					for (int iter = 0; iter < maxPhase2; iter++) {
						bool foundNew2 = false;

						foreach (var pred in GetDispatchPredecessors()) {
							if (resolved.Contains(pred))
								continue;
							if (pred.LastInstr.OpCode.Code == Code.Switch)
								continue;
							if (!IsUnconditionalPredecessor(pred))
								continue;

							if (!dispatch.BlockToCase.TryGetValue(pred, out int predCaseIdx))
								continue;
							if (!caseStateVar.TryGetValue(predCaseIdx, out int seed))
								continue;

							var edge = TryResolveEdge(pred, seed);
							if (edge != null) {
								edges.Add(edge.Value);
								resolved.Add(pred);
								resolvedCount++;
								foundNew2 = true;

								if (edge.Value.TargetIncomingStateVar.HasValue) {
									caseStateVar[edge.Value.CaseIndex] = edge.Value.TargetIncomingStateVar.Value;
									allSeeds.Add(edge.Value.TargetIncomingStateVar.Value);
								}
							}
						}

						if (!foundNew2)
							break;
					}
				}

				// Phase 3: Brute-force all known seeds for disconnected subgraphs
				if (allSeeds.Count > 0) {
					bool phase3Progress = true;
					int maxPhase3 = dispatch.CaseTargets.Count * 2;
					for (int iter3 = 0; iter3 < maxPhase3 && phase3Progress; iter3++) {
						phase3Progress = false;

						foreach (var pred in GetDispatchPredecessors()) {
							if (resolved.Contains(pred))
								continue;
							if (pred.LastInstr.OpCode.Code == Code.Switch)
								continue;
							if (!IsUnconditionalPredecessor(pred))
								continue;

							bool hasCaseIdx = dispatch.BlockToCase.TryGetValue(pred, out int ci);
							if (hasCaseIdx && caseStateVar.ContainsKey(ci))
								continue;

							foreach (var trySeed in allSeeds) {
								if (hasCaseIdx && !VerifySeedRoutesToCase(trySeed, ci))
									continue;
								var edge = TryResolveEdge(pred, trySeed);
								if (edge != null) {
									edges.Add(edge.Value);
									resolved.Add(pred);
									resolvedCount++;
									phase3Progress = true;

									if (edge.Value.TargetIncomingStateVar.HasValue) {
										int newSeed = edge.Value.TargetIncomingStateVar.Value;
										caseStateVar[edge.Value.CaseIndex] = newSeed;
										allSeeds.Add(newSeed);
									}
									break;
								}
							}
						}
					}
				}

				// Phase 4: Indirect resolution through passthrough blocks
				{
					bool progress4 = true;
					int maxIter4 = dispatch.CaseTargets.Count * 2;
					for (int iter4 = 0; iter4 < maxIter4 && progress4; iter4++) {
						progress4 = false;

						foreach (var passthrough in GetDispatchPredecessors()) {
							if (resolved.Contains(passthrough))
								continue;
							if (passthrough.LastInstr.OpCode.Code == Code.Switch)
								continue;
							if (!IsUnconditionalPredecessor(passthrough))
								continue;

							bool hasPtCaseIdx = dispatch.BlockToCase.TryGetValue(passthrough, out int ptCaseIdx);

							foreach (var src in new List<Block>(passthrough.Sources)) {
								if (indirectResolved.Contains(src))
									continue;
								if (IsDispatchBlock(src))
									continue;
								if (src.LastInstr.OpCode.Code == Code.Switch)
									continue;

								var intermediates = new List<Block> { passthrough };

								var edge = TryResolveIndirectEdge(src, intermediates);

								if (edge == null) {
									foreach (var seed in allSeeds) {
										if (hasPtCaseIdx && !VerifySeedRoutesToCase(seed, ptCaseIdx))
											continue;
										edge = TryResolveIndirectEdge(src, intermediates, seed);
										if (edge != null)
											break;
									}
								}

								if (edge != null) {
									edges.Add(edge.Value);
									indirectResolved.Add(src);
									resolvedCount++;
									progress4 = true;

									// Immediately merge Phase 4 seeds
									if (edge.Value.TargetIncomingStateVar.HasValue) {
										int newSeed = edge.Value.TargetIncomingStateVar.Value;
										caseStateVar[edge.Value.CaseIndex] = newSeed;
										allSeeds.Add(newSeed);
									}
								}
							}
						}
					}
				}

				// Phase 5: Algebraic seed extraction
				RunAlgebraicSeedExtraction(caseStateVar, allSeeds);

				// Break if neither edges nor seeds grew
				if (edges.Count == prevEdgeCount && allSeeds.Count == prevSeedCount)
					break;
			}
		}
		else {
			// No stateVar: Phase 4 only (unseeded indirect resolution)
			bool progress4 = true;
			int maxIter4 = dispatch.CaseTargets.Count * 2;
			for (int iter4 = 0; iter4 < maxIter4 && progress4; iter4++) {
				progress4 = false;

				foreach (var passthrough in GetDispatchPredecessors()) {
					if (resolved.Contains(passthrough))
						continue;
					if (passthrough.LastInstr.OpCode.Code == Code.Switch)
						continue;
					if (!IsUnconditionalPredecessor(passthrough))
						continue;

					foreach (var src in new List<Block>(passthrough.Sources)) {
						if (indirectResolved.Contains(src))
							continue;
						if (IsDispatchBlock(src))
							continue;
						if (src.LastInstr.OpCode.Code == Code.Switch)
							continue;

						var intermediates = new List<Block> { passthrough };
						var edge = TryResolveIndirectEdge(src, intermediates);

						if (edge != null) {
							edges.Add(edge.Value);
							indirectResolved.Add(src);
							resolvedCount++;
							progress4 = true;
						}
					}
				}
			}
		}

		// Mark passthrough blocks as resolved if all their sources were handled
		foreach (var passthrough in GetDispatchPredecessors()) {
			if (resolved.Contains(passthrough))
				continue;
			bool allSourcesResolved = true;
			foreach (var src in passthrough.Sources) {
				if (!indirectResolved.Contains(src) && !resolved.Contains(src)) {
					allSourcesResolved = false;
					break;
				}
			}
			if (allSourcesResolved && passthrough.Sources.Count > 0)
				resolved.Add(passthrough);
		}

		// Compute accurate unresolved count
		failedCount = 0;
		foreach (var pred in GetDispatchPredecessors()) {
			if (resolved.Contains(pred))
				continue;
			if (pred.LastInstr.OpCode.Code == Code.Switch)
				continue;
			failedCount++;
		}

		return edges;
	}

	bool IsUnconditionalPredecessor(Block block) {
		var lastInstr = block.LastInstr;
		return lastInstr.IsBr() || block.IsFallThrough();
	}

	bool IsConditionalPredecessor(Block block) {
		if (!block.IsConditionalBranch())
			return false;
		if (IsDispatchBlock(block.FallThrough))
			return true;
		if (block.Targets != null) {
			foreach (var target in block.Targets) {
				if (IsDispatchBlock(target))
					return true;
			}
		}
		return false;
	}

	/// <summary>
	///     Builds a chain of blocks to emulate by walking backward from the predecessor
	///     through single-predecessor fall-through chains.
	/// </summary>
	List<Block> BuildEmulationChain(Block predecessor) {
		var chain = new List<Block> { predecessor };
		var visited = new HashSet<Block> { predecessor, dispatch.SwitchBlock };
		if (dispatch.HeaderBlock != null)
			visited.Add(dispatch.HeaderBlock);
		var current = predecessor;
		const int maxChainLength = 20;

		while (chain.Count < maxChainLength) {
			Block singlePred = null;
			int predCount = 0;
			foreach (var src in current.Sources) {
				if (visited.Contains(src))
					continue;
				if (src.LastInstr.OpCode.Code == Code.Switch)
					continue;
				if (src.FallThrough == current || (src.Targets != null && src.Targets.Count == 1 && src.Targets[0] == current && src.LastInstr.IsBr())) {
					singlePred = src;
					predCount++;
				}
				else {
					predCount++;
				}
			}

			if (predCount != 1 || singlePred == null)
				break;

			chain.Add(singlePred);
			visited.Add(singlePred);
			current = singlePred;
		}

		chain.Reverse();
		return chain;
	}

	ResolvedEdge? TryResolveEdge(Block predecessor, int? seedStateVar = null) {
		var predInstrs = predecessor.Instructions;

		var chain = BuildEmulationChain(predecessor);

		var emu = new InstructionEmulator();
		emu.Initialize(method, false);

		if (dispatch.StateVar != null) {
			if (seedStateVar.HasValue)
				emu.SetLocal(dispatch.StateVar, new Int32Value(seedStateVar.Value));
			else if (chain[0].Sources.Count == 0)
				emu.SetLocal(dispatch.StateVar, Int32Value.Zero);
			else
				emu.SetLocal(dispatch.StateVar, Int32Value.CreateUnknown());
		}

		Int32Value preRemDividend = null;

		try {
			foreach (var block in chain) {
				var instrs = block.Instructions;
				int end = instrs.Count;
				if (end > 0 && instrs[end - 1].IsBr())
					end--;
				emu.Emulate(instrs, 0, end);
			}

			EmulateDispatchBlocks(emu, predecessor, out preRemDividend);
		}
		catch {
			return null;
		}

		if (emu.StackSize() < 1)
			return null;

		var tos = emu.Pop();
		int caseIndex;

		if (tos is Int32Value iv && iv.AllBitsValid()) {
			caseIndex = iv.Value; // standard path — already the unsigned remainder
		}
		else if (preRemDividend != null) {
			var partial = TryPartialCaseIndex(preRemDividend);
			if (partial == null)
				return null;
			caseIndex = partial.Value;
		}
		else {
			return null;
		}

		if (caseIndex < 0 || caseIndex >= dispatch.CaseTargets.Count)
			return null;

		var target = dispatch.CaseTargets[caseIndex];

		int? targetIncoming = null;
		if (dispatch.StateVar != null) {
			var sv = emu.GetLocal(dispatch.StateVar);
			if (sv is Int32Value svIv && svIv.AllBitsValid())
				targetIncoming = svIv.Value;
		}

		var boundary = StateUpdateFinder.Find(predecessor, dispatch, blocks.Locals);
		int instrsToRemove;
		int stackPops;

		if (boundary.Found) {
			instrsToRemove = predInstrs.Count - boundary.CutPoint;
			stackPops = boundary.StackDepthAtCut;
		}
		else {
			instrsToRemove = predInstrs[predInstrs.Count - 1].IsBr() ? 1 : 0;
			stackPops = 0;
		}

		return new ResolvedEdge {
			Predecessor = predecessor,
			Target = target,
			CaseIndex = caseIndex,
			InstructionsToRemove = instrsToRemove,
			StackCleanupPops = stackPops,
			TargetIncomingStateVar = targetIncoming,
		};
	}

	List<ResolvedEdge> TryResolveConditionalEdge(Block predecessor) {
		var predInstrs = predecessor.Instructions;
		var edges = new List<ResolvedEdge>();

		int branchIdx = predInstrs.Count - 1;
		if (branchIdx < 0 || !predInstrs[branchIdx].IsConditionalBranch())
			return null;

		var fallThrough = predecessor.FallThrough;
		Block branchTarget = null;
		if (predecessor.Targets != null && predecessor.Targets.Count == 1)
			branchTarget = predecessor.Targets[0];

		bool fallThroughToSwitch = IsDispatchBlock(fallThrough);
		bool branchToSwitch = branchTarget != null && IsDispatchBlock(branchTarget);

		if (!fallThroughToSwitch && !branchToSwitch)
			return null;

		var edge = TryResolveConditionalPath(predecessor);
		if (edge != null) {
			// Add once per path that leads to the switch so Apply retargets each one
			if (fallThroughToSwitch)
				edges.Add(edge.Value);
			if (branchToSwitch)
				edges.Add(edge.Value);
		}

		return edges;
	}

	ResolvedEdge? TryResolveConditionalPath(Block predecessor) {
		var predInstrs = predecessor.Instructions;

		var emu = new InstructionEmulator();
		emu.Initialize(method, false);

		if (dispatch.StateVar != null)
			emu.SetLocal(dispatch.StateVar, Int32Value.CreateUnknown());

		try {
			emu.Emulate(predInstrs, 0, predInstrs.Count);
		}
		catch {
			return null;
		}

		try {
			EmulateDispatchBlocks(emu, predecessor, out _);
		}
		catch {
			return null;
		}

		if (emu.StackSize() < 1)
			return null;

		var tos = emu.Pop();
		if (!(tos is Int32Value iv) || !iv.AllBitsValid())
			return null;

		int caseIndex = iv.Value;
		if (caseIndex < 0 || caseIndex >= dispatch.CaseTargets.Count)
			return null;

		return new ResolvedEdge {
			Predecessor = predecessor,
			Target = dispatch.CaseTargets[caseIndex],
			CaseIndex = caseIndex,
			InstructionsToRemove = 0,
			StackCleanupPops = 0,
		};
	}

	/// <summary>
	///     Resolves an indirect predecessor that reaches the switch through intermediate
	///     (passthrough) blocks. Emulates [source, intermediates..., dispatch].
	/// </summary>
	ResolvedEdge? TryResolveIndirectEdge(Block source, List<Block> intermediates, int? seedStateVar = null) {
		var srcInstrs = source.Instructions;

		// Compute exit stack depth of source block to determine cleanup pops needed
		var depths = StateUpdateFinder.ComputeStackDepths(srcInstrs);
		if (depths == null)
			return null;

		int exitDepth = depths[srcInstrs.Count];

		var emu = new InstructionEmulator();
		emu.Initialize(method, false);

		if (dispatch.StateVar != null) {
			if (seedStateVar.HasValue)
				emu.SetLocal(dispatch.StateVar, new Int32Value(seedStateVar.Value));
			else if (source.Sources.Count == 0)
				emu.SetLocal(dispatch.StateVar, Int32Value.Zero);
			else
				emu.SetLocal(dispatch.StateVar, Int32Value.CreateUnknown());
		}

		Int32Value preRemDividend = null;

		try {
			int srcEnd = srcInstrs.Count;
			if (srcEnd > 0 && srcInstrs[srcEnd - 1].IsBr())
				srcEnd--;
			emu.Emulate(srcInstrs, 0, srcEnd);

			foreach (var mid in intermediates) {
				var midInstrs = mid.Instructions;
				int midEnd = midInstrs.Count;
				if (midEnd > 0 && midInstrs[midEnd - 1].IsBr())
					midEnd--;
				emu.Emulate(midInstrs, 0, midEnd);
			}

			// The last intermediate determines the dispatch entry point
			var lastMid = intermediates[intermediates.Count - 1];
			EmulateDispatchBlocks(emu, lastMid, out preRemDividend);
		}
		catch {
			return null;
		}

		if (emu.StackSize() < 1)
			return null;

		var tos = emu.Pop();
		int caseIndex;

		if (tos is Int32Value iv && iv.AllBitsValid()) {
			caseIndex = iv.Value;
		}
		else if (preRemDividend != null) {
			var partial = TryPartialCaseIndex(preRemDividend);
			if (partial == null)
				return null;
			caseIndex = partial.Value;
		}
		else {
			return null;
		}

		if (caseIndex < 0 || caseIndex >= dispatch.CaseTargets.Count)
			return null;

		var target = dispatch.CaseTargets[caseIndex];

		int? targetIncoming = null;
		if (dispatch.StateVar != null) {
			var sv = emu.GetLocal(dispatch.StateVar);
			if (sv is Int32Value svIv && svIv.AllBitsValid())
				targetIncoming = svIv.Value;
		}

		if (source.Parent != target.Parent)
			return null;

		int instrsToRemove = (srcInstrs.Count > 0 && srcInstrs[srcInstrs.Count - 1].IsBr()) ? 1 : 0;

		return new ResolvedEdge {
			Predecessor = source,
			Target = target,
			CaseIndex = caseIndex,
			InstructionsToRemove = instrsToRemove,
			StackCleanupPops = exitDepth,
			TargetIncomingStateVar = targetIncoming,
		};
	}

	// --- Phase 5: Algebraic seed extraction ---

	/// <summary>
	///     Discovers new seeds by algebraically computing next-case state values
	///     from affine update patterns in blocks that return to the dispatch.
	/// </summary>
	int RunAlgebraicSeedExtraction(Dictionary<int, int> caseStateVar, HashSet<int> allSeeds) {
		if (dispatch.StateVar == null)
			return 0;

		var switchConstants = ExtractSwitchConstants();
		if (switchConstants == null)
			return 0;

		var (xorKey, modulus) = switchConstants.Value;
		if ((uint)modulus != (uint)dispatch.CaseTargets.Count)
			return 0;

		var dispatchPreds = new HashSet<Block>(GetDispatchPredecessors());

		// Collect all derived seeds: nextCase → set of nextSeed values
		var derivedSeeds = new Dictionary<int, HashSet<int>>();

		for (int caseIdx = 0; caseIdx < dispatch.CaseTargets.Count; caseIdx++) {
			if (!caseStateVar.TryGetValue(caseIdx, out int seed))
				continue;

			var caseTarget = dispatch.CaseTargets[caseIdx];

			// BFS forward from case target, bounded by 50 visited blocks
			var queue = new Queue<Block>();
			var visited = new HashSet<Block>();
			queue.Enqueue(caseTarget);
			visited.Add(caseTarget);
			int visitCount = 0;

			while (queue.Count > 0 && visitCount < 50) {
				var block = queue.Dequeue();
				visitCount++;

				if (IsDispatchBlock(block))
					continue;

				// Check if block is a dispatch predecessor
				bool isDispatchPred = dispatchPreds.Contains(block);
				if (!isDispatchPred) {
					if (IsDispatchBlock(block.FallThrough))
						isDispatchPred = true;
					else if (block.LastInstr.IsBr() && block.Targets != null &&
						block.Targets.Count == 1 && IsDispatchBlock(block.Targets[0]))
						isDispatchPred = true;
				}

				if (isDispatchPred) {
					var affine = ExtractAffineUpdate(block, dispatch.StateVar, blocks.Locals);
					if (affine != null) {
						var (mulConst, xorConst) = affine.Value;
						uint nextSeedU = unchecked(((uint)seed * (uint)mulConst) ^ (uint)xorConst ^ (uint)xorKey);
						int nextSeed = (int)nextSeedU;
						int nextCase = (int)(nextSeedU % (uint)modulus);

						if (nextCase < dispatch.CaseTargets.Count) {
							if (!derivedSeeds.TryGetValue(nextCase, out var seedSet)) {
								seedSet = new HashSet<int>();
								derivedSeeds[nextCase] = seedSet;
							}
							seedSet.Add(nextSeed);
						}
					}
				}

				// Enqueue successors
				foreach (var succ in block.GetTargets()) {
					if (visited.Add(succ))
						queue.Enqueue(succ);
				}
			}
		}

		// Merge: only accept unambiguous derived seeds
		int newSeedCount = 0;
		foreach (var kv in derivedSeeds) {
			int nextCase = kv.Key;
			var seedSet = kv.Value;

			if (seedSet.Count != 1)
				continue; // ambiguous — multiple different seeds for same case

			int nextSeed = 0;
			foreach (var s in seedSet) { nextSeed = s; break; }

			if (caseStateVar.TryGetValue(nextCase, out int existing)) {
				if (existing != nextSeed)
					Logger.vv("  Phase 5: seed conflict for case {0}: existing={1:X8}, derived={2:X8}",
						nextCase, existing, nextSeed);
				continue;
			}

			caseStateVar[nextCase] = nextSeed;
			allSeeds.Add(nextSeed);
			newSeedCount++;
		}

		return newSeedCount;
	}

	/// <summary>
	///     O(1) algebraic check: does this seed route to the expected case index?
	///     The seed is already the post-XOR dispatch value (V_7 = incoming_state ^ K),
	///     so case_index = seed % M with no additional XOR.
	/// </summary>
	bool VerifySeedRoutesToCase(int seed, int expectedCaseIndex) {
		int M = dispatch.CaseTargets.Count;
		if (M < 2)
			return true;
		return (int)((uint)seed % (uint)M) == expectedCaseIndex;
	}

	// --- Helper methods ---

	static int FindSwitchIndex(IList<Instr> instrs) {
		for (int i = instrs.Count - 1; i >= 0; i--) {
			if (instrs[i].OpCode.Code == Code.Switch)
				return i;
		}
		return -1;
	}

	static int FindRemUnIndex(IList<Instr> instrs) {
		int switchIdx = FindSwitchIndex(instrs);
		if (switchIdx < 0)
			return -1;
		for (int i = switchIdx - 1; i >= 0; i--) {
			if (instrs[i].OpCode.Code == Code.Rem_Un)
				return i;
		}
		return -1;
	}

	/// <summary>
	///     Extracts the XOR key (K) and modulus (M) from the dispatch blocks' instruction
	///     pattern: ldloc stateVar; ldc.i4 K; xor; dup; stloc; ldc.i4 M; rem.un; switch.
	///     Checks both the switch block and header block (if present).
	/// </summary>
	(int xorKey, int modulus)? ExtractSwitchConstants() {
		var result = ExtractSwitchConstantsFromBlock(dispatch.SwitchBlock);
		if (result != null)
			return result;
		if (dispatch.HeaderBlock != null)
			return ExtractSwitchConstantsFromBlock(dispatch.HeaderBlock);
		return null;
	}

	static (int xorKey, int modulus)? ExtractSwitchConstantsFromBlock(Block block) {
		var instrs = block.Instructions;

		// Find rem.un in this block
		int remIdx = -1;
		for (int i = instrs.Count - 1; i >= 0; i--) {
			if (instrs[i].OpCode.Code == Code.Rem_Un) {
				remIdx = i;
				break;
			}
		}
		if (remIdx < 0)
			return null;

		// Verify no other rem* opcodes after remIdx
		for (int i = remIdx + 1; i < instrs.Count; i++) {
			var code = instrs[i].OpCode.Code;
			if (code == Code.Rem || code == Code.Rem_Un)
				return null;
		}

		// Find ldc.i4 M immediately before rem.un (allowing only nop/dup/stloc between)
		int mIdx = -1;
		for (int i = remIdx - 1; i >= 0; i--) {
			if (instrs[i].IsLdcI4()) {
				mIdx = i;
				break;
			}
			var code = instrs[i].OpCode.Code;
			if (code != Code.Nop && code != Code.Dup && !instrs[i].IsStloc())
				break;
		}
		if (mIdx < 0)
			return null;

		int modulus = instrs[mIdx].GetLdcI4Value();

		// Find xor before mIdx (skip dup/stloc/nop)
		int xorIdx = -1;
		for (int i = mIdx - 1; i >= 0; i--) {
			if (instrs[i].OpCode.Code == Code.Xor) {
				xorIdx = i;
				break;
			}
			var code = instrs[i].OpCode.Code;
			if (code != Code.Nop && code != Code.Dup && !instrs[i].IsStloc())
				break;
		}
		if (xorIdx < 0)
			return null;

		// Find ldc.i4 K immediately before xor
		if (xorIdx < 1)
			return null;
		if (!instrs[xorIdx - 1].IsLdcI4())
			return null;

		return (instrs[xorIdx - 1].GetLdcI4Value(), modulus);
	}

	/// <summary>
	///     Extracts affine state-update constants from a block by finding the pattern:
	///     ldloc stateVar; ldc.i4 A; mul; ldc.i4 B; xor
	///     closest to the block end. Also handles one-step aliases.
	/// </summary>
	static (int mulConst, int xorConst)? ExtractAffineUpdate(Block block, Local stateVar, IList<Local> locals) {
		var instrs = block.Instructions;
		int endIdx = instrs.Count - 1;

		// Skip final br
		if (endIdx >= 0 && instrs[endIdx].IsBr())
			endIdx--;

		// Scan backward for: ldloc stateVar; ldc.i4 A; mul; ldc.i4 B; xor
		// Take the match closest to the block end
		for (int i = endIdx; i >= 4; i--) {
			if (instrs[i].OpCode.Code != Code.Xor)
				continue;
			if (!instrs[i - 1].IsLdcI4())
				continue;
			if (instrs[i - 2].OpCode.Code != Code.Mul)
				continue;
			if (!instrs[i - 3].IsLdcI4())
				continue;
			if (!instrs[i - 4].IsLdloc())
				continue;

			var loadedLocal = Instr.GetLocalVar(locals, instrs[i - 4]);
			bool isStateVar = loadedLocal == stateVar;

			// Alias tracking: check if loadedLocal is a one-step alias of stateVar
			if (!isStateVar && loadedLocal != null) {
				for (int j = i - 5; j >= 1; j--) {
					if (instrs[j].IsStloc() && Instr.GetLocalVar(locals, instrs[j]) == loadedLocal &&
						instrs[j - 1].IsLdloc() && Instr.GetLocalVar(locals, instrs[j - 1]) == stateVar) {
						isStateVar = true;
						break;
					}
				}
			}

			if (!isStateVar)
				continue;

			// Verify: between match end (i) and block end (endIdx), only harmless ops
			bool clean = true;
			for (int j = i + 1; j <= endIdx; j++) {
				var code = instrs[j].OpCode.Code;
				if (code == Code.Nop || code == Code.Dup || instrs[j].IsStloc() ||
					code == Code.Br || code == Code.Br_S)
					continue;
				clean = false;
				break;
			}

			if (clean)
				return (instrs[i - 3].GetLdcI4Value(), instrs[i - 1].GetLdcI4Value());
		}

		return null;
	}

	/// <summary>
	///     Determines the case index from a pre-rem.un dividend with partial bit validity.
	///     For power-of-two moduli, only the low bits matter. For non-power-of-two moduli,
	///     enumerates unknown bit combinations to check if the remainder is unique.
	/// </summary>
	int? TryPartialCaseIndex(Int32Value preRemDividend) {
		if (preRemDividend == null)
			return null;
		int M = dispatch.CaseTargets.Count;
		if (M < 2)
			return null;
		uint mu = (uint)M;

		// Power-of-two fast path: only low bits matter
		if ((mu & (mu - 1)) == 0) {
			uint neededMask = mu - 1;
			if ((preRemDividend.ValidMask & neededMask) == neededMask)
				return (int)((uint)preRemDividend.Value & neededMask);
			return null;
		}

		// Non-power-of-two: enumerate unknown bit combinations
		if (preRemDividend.AllBitsValid())
			return (int)((uint)preRemDividend.Value % mu);

		uint unknownMask = ~preRemDividend.ValidMask;
		int unknownCount = PopCount(unknownMask);
		if (unknownCount == 0)
			return (int)((uint)preRemDividend.Value % mu);
		if (unknownCount > 16)
			return null;
		if (unknownCount > 14 && M > 128)
			return null;

		// Cheap early-out: if flipping just the lowest unknown bit changes the
		// remainder, the full enumeration is guaranteed to be ambiguous
		int base0 = ExpandUnknownBits(preRemDividend.Value, unknownMask, 0);
		int base1 = ExpandUnknownBits(preRemDividend.Value, unknownMask, 1);
		int rem0 = (int)((uint)base0 % mu);
		int rem1 = (int)((uint)base1 % mu);
		if (rem0 != rem1)
			return null;

		int? result = rem0;
		for (uint combo = 2; combo < (1u << unknownCount); combo++) {
			int candidate = ExpandUnknownBits(preRemDividend.Value, unknownMask, combo);
			int rem = (int)((uint)candidate % mu);
			if (rem != result.Value)
				return null; // ambiguous
		}
		return result;
	}

	static int ExpandUnknownBits(int baseValue, uint unknownMask, uint combo) {
		uint v = (uint)baseValue;
		uint m = unknownMask;
		uint bit = 1;
		while (m != 0) {
			uint lsb = m & (~m + 1u); // extract lowest set bit
			m ^= lsb;
			if ((combo & bit) != 0)
				v |= lsb;
			else
				v &= ~lsb;
			bit <<= 1;
		}
		return (int)v;
	}

	static int PopCount(uint value) {
		value -= (value >> 1) & 0x55555555u;
		value = (value & 0x33333333u) + ((value >> 2) & 0x33333333u);
		return (int)(((value + (value >> 4)) & 0x0F0F0F0Fu) * 0x01010101u >> 24);
	}
}
