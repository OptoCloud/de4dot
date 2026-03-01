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
using dnlib.DotNet.Emit;

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4.cflow;

/// <summary>
///     Deobfuscates XOR-switch state machines produced by .NET Reactor v6.x.
///     Dual-path orchestrator: tries the new state-centric pipeline first
///     (TRACE / STATE / PAYLOAD / REBUILD), falls back to the legacy
///     source-centric pipeline when the new one can't handle a dispatch.
/// </summary>
class Deobfuscator : IBlocksDeobfuscator {
	List<Block> allBlocks;
	Blocks blocks;
	ConstantDiscovery constantDiscovery;
	IList<Local> locals;
	PatternMatcher patternMatcher;
	LegacyRewriter rewriter;
	Simulator simulator;

	public bool ExecuteIfNotModified { get; }

	public void DeobfuscateBegin(Blocks blocks) {
		this.blocks = blocks;
		locals = blocks.Locals;
		patternMatcher = new PatternMatcher(locals);
		constantDiscovery = new ConstantDiscovery(locals, patternMatcher);
		simulator = new Simulator(locals);
		rewriter = new LegacyRewriter(patternMatcher, constantDiscovery, simulator);
	}

	public bool Deobfuscate(List<Block> allBlocks) {
		this.allBlocks = allBlocks;
		bool modified = false;
		int totalDispatches = 0, embeddedMulDispatches = 0, rewrittenDispatches = 0;
		int newPipelineHits = 0, legacyHits = 0;

		foreach (var block in allBlocks) {
			if (block.LastInstr.OpCode.Code != Code.Switch)
				continue;
			if (patternMatcher.TryExtractDispatchInfo(block, out var probe)) {
				totalDispatches++;
				if (probe.HasEmbeddedMul)
					embeddedMulDispatches++;
			}

			if (TryDeobfuscateDispatch(block, out bool usedNewPipeline)) {
				modified = true;
				rewrittenDispatches++;
				if (usedNewPipeline)
					newPipelineHits++;
				else
					legacyHits++;
			}
		}

		if (totalDispatches > 0)
			Logger.v("  XOR-switch: {0} dispatches ({1} embedded-mul), {2} rewritten (new={3}, legacy={4})",
				totalDispatches, embeddedMulDispatches, rewrittenDispatches,
				newPipelineHits, legacyHits);
		return modified;
	}

	bool TryDeobfuscateDispatch(Block switchBlock, out bool usedNewPipeline) {
		usedNewPipeline = false;

		// Shared preprocessing: fold opaque constants
		PatternMatcher.FoldOpaqueConstants(switchBlock);
		foreach (var source in switchBlock.Sources) {
			if (source != switchBlock)
				PatternMatcher.FoldOpaqueConstants(source);
		}

		// Stage 0: Build dispatch model
		var model = DispatchModel.TryCreate(switchBlock, patternMatcher, simulator);
		if (model == null)
			return false;

		var info = model.Info;

		// Internal constant dispatch shortcut (handled before either pipeline)
		if (info.InternalStateVarInput.HasValue) {
			var candidate = rewriter.TryBuildInternalConstantCandidate(switchBlock, info);
			if (candidate != null && LegacyRewriter.ApplyCandidate(candidate.Value))
				return true;
		}

		// Precompute shared structures (used by both pipelines)
		var blockToCase = CfgAnalysis.BuildBlockToCase(switchBlock);
		var reverseReachable = CfgAnalysis.ComputeReverseReachable(switchBlock);

		if (info.HasEmbeddedMul) {
			info.OriginalStateVar = constantDiscovery.FindOriginalStateVar(switchBlock, info, blockToCase);
			// Sync model.Info so the new pipeline (BlockSlicer/StateTracer/Rebuilder) sees
			// OriginalStateVar — model.Info is a struct and was copied before this update.
			model.SetInfo(info);
		}

		var caseToDispatchVals = constantDiscovery.CollectAllDispatchVals(
			switchBlock, info, reverseReachable, blockToCase);
		if (info.SelfLoopEligible && caseToDispatchVals.Count == 0)
			constantDiscovery.SeedSelfLoopDispatchVals(switchBlock, info, caseToDispatchVals, reverseReachable);

		// Run both pipelines: new pipeline handles what it can, legacy handles the rest.
		// The new pipeline rewrites case blocks it can trace; the legacy pipeline
		// picks up remaining cases through its own pattern matching.
		bool modified = false;

		// New pipeline: handles cases the legacy pipeline misses.
		if (TryNewPipeline(model, caseToDispatchVals, blockToCase)) {
			usedNewPipeline = true;
			modified = true;
		}

		// Legacy pipeline (runs on remaining unhandled cases)
		modified |= RewriteConstantSources(switchBlock, info);
		modified |= RewriteMultiplyXorSources(switchBlock, info, caseToDispatchVals, blockToCase);
		if (info.SelfLoopEligible)
			modified |= RewriteSelfLoopSources(switchBlock, info, caseToDispatchVals, blockToCase);
		modified |= LegacyRewriter.RemoveDeadSwitchCases(switchBlock, info, caseToDispatchVals);

		return modified;
	}

	bool TryNewPipeline(DispatchModel model,
		Dictionary<int, HashSet<uint>> caseToDispatchVals,
		Dictionary<Block, int> blockToCase) {
		// Early exit: tracing needs dispatch vals to seed from
		if (caseToDispatchVals.Count == 0)
			return false;

		// Stage 1: Slice (computed once, shared by tracer and rebuilder)
		var sliced = BlockSlicer.SliceAll(model, null,
			blockToCase, patternMatcher, constantDiscovery);
		if (sliced == null)
			return false;

		// Stage 2: Trace
		var traced = StateTracer.Trace(model, caseToDispatchVals,
			blockToCase, sliced);
		if (traced == null)
			return false;

		// Stage 3: Rebuild
		return Rebuilder.Rebuild(model, traced, sliced, blockToCase);
	}

	// ── Legacy pipeline methods ──────────────────────────────────────

	bool RewriteConstantSources(Block switchBlock, DispatchInfo info) {
		bool modified = false;

		foreach (var source in new List<Block>(switchBlock.Sources)) {
			if (source == switchBlock)
				continue;
			var candidate = rewriter.TryBuildConstantSourceCandidate(switchBlock, info, source);
			if (candidate != null)
				modified |= LegacyRewriter.ApplyCandidate(candidate.Value);
		}

		foreach (var source in new List<Block>(switchBlock.Sources)) {
			if (source == switchBlock)
				continue;
			if (!CfgAnalysis.IsPopThroughBlock(source))
				continue;
			foreach (var pred in new List<Block>(source.Sources)) {
				if (pred == switchBlock || pred == source)
					continue;
				var candidate = rewriter.TryBuildPopThroughCandidate(switchBlock, info, pred);
				if (candidate != null)
					modified |= LegacyRewriter.ApplyCandidate(candidate.Value);
			}
		}

		return modified;
	}

	bool RewriteMultiplyXorSources(Block switchBlock, DispatchInfo info,
		Dictionary<int, HashSet<uint>> caseToDispatchVals, Dictionary<Block, int> blockToCase) {
		if (info.DispatchVar == null)
			return false;
		// Split dispatches have the mul-xor prefix in a predecessor block,
		// not in the case blocks. The legacy MulXor transition function
		// uses dispatch-val domain which is incorrect for state-domain patterns.
		if (info.SplitEmbeddedMul)
			return false;
		if (switchBlock.Targets == null)
			return false;

		bool modified = false;
		foreach (var source in new List<Block>(switchBlock.Sources)) {
			if (source == switchBlock)
				continue;
			var candidate = rewriter.TryBuildMulXorCandidate(switchBlock, info, source,
				caseToDispatchVals, blockToCase);
			if (candidate != null)
				modified |= LegacyRewriter.ApplyCandidate(candidate.Value);
		}

		return modified;
	}

	bool RewriteSelfLoopSources(Block switchBlock, DispatchInfo info,
		Dictionary<int, HashSet<uint>> caseToDispatchVals, Dictionary<Block, int> blockToCase) {
		if (!info.HasEmbeddedMul || switchBlock.Targets == null)
			return false;

		bool modified = false;

		var sourcesToProcess = new List<Block>();
		foreach (var source in switchBlock.Sources) {
			if (source == switchBlock)
				continue;
			if (blockToCase.ContainsKey(source)) {
				sourcesToProcess.Add(source);
			}
			else if (CfgAnalysis.IsFunnelBlock(source)) {
				foreach (var funnelSource in source.Sources) {
					if (funnelSource != switchBlock && funnelSource != source
					                                && blockToCase.ContainsKey(funnelSource))
						sourcesToProcess.Add(funnelSource);
				}
			}
		}

		foreach (var source in new List<Block>(sourcesToProcess)) {
			var candidate = rewriter.TryBuildSelfLoopCandidate(switchBlock, info, source,
				caseToDispatchVals, blockToCase);
			if (candidate != null)
				modified |= LegacyRewriter.ApplyCandidate(candidate.Value);
		}

		return modified;
	}

}
