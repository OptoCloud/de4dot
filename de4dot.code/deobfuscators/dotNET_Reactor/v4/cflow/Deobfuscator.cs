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
		int residualSwitches = 0, failedModel = 0;
		int failedNoDvs = 0, failedWithDvs = 0;
		var npFailCounts = new Dictionary<string, int>();
		int rbNone = 0, rbNoTrace = 0, rbUnkExit = 0, rbResolve = 0, rbTarget = 0;
		int rbScope = 0, rbBounds = 0, rbBranch = 0, rbNoop = 0, rbApplied = 0;
		int lmDetected = 0, lmRewrites = 0, lmNoStore = 0, lmResolve = 0;
		int lmTarget = 0, lmScope = 0, lmStack = 0, lmBranch = 0, lmNoop = 0;

		// Reset BlockSlicer diagnostics per method (static counters)
		BlockSlicer.DiagSliceAttempts = BlockSlicer.DiagSliceMulXor = 0;
		BlockSlicer.DiagSliceConst = BlockSlicer.DiagSliceNone = 0;

		foreach (var block in allBlocks) {
			if (block.LastInstr.OpCode.Code != Code.Switch)
				continue;
			if (patternMatcher.TryExtractDispatchInfo(block, out var probe)) {
				totalDispatches++;
				if (probe.HasEmbeddedMul)
					embeddedMulDispatches++;
			}
			else {
				// Classify the failure: is this a residual switch from prior rewriting?
				if (IsResidualSwitch(block))
					residualSwitches++;
				else
					failedModel++;
			}

			// Reset Rebuilder counters before each dispatch to prevent stale accumulation
			Rebuilder.SkipNone = Rebuilder.SkipNoTrace = Rebuilder.SkipUnknownExit = 0;
			Rebuilder.SkipResolve = Rebuilder.SkipTarget = Rebuilder.SkipScope = 0;
			Rebuilder.SkipBounds = Rebuilder.SkipBranch = Rebuilder.SkipNoop = Rebuilder.Applied = 0;

			// Reset LoopMachineRewriter counters (in case TryRewrite isn't called for this dispatch)
			LoopMachineRewriter.Detected = LoopMachineRewriter.Rewrites = 0;
			LoopMachineRewriter.SkipNoStore = LoopMachineRewriter.SkipResolve = 0;
			LoopMachineRewriter.SkipTarget = LoopMachineRewriter.SkipScope = 0;
			LoopMachineRewriter.SkipStack = LoopMachineRewriter.SkipBranch = LoopMachineRewriter.SkipNoop = 0;

			if (TryDeobfuscateDispatch(block, out bool usedNewPipeline, out string failStage)) {
				modified = true;
				rewrittenDispatches++;
				if (usedNewPipeline)
					newPipelineHits++;
				else
					legacyHits++;
			}
			else if (failStage != null) {
				if (failStage == "no-dvs")
					failedNoDvs++;
				else if (failStage.StartsWith("dvs=")) {
					failedWithDvs++;
					// Aggregate dispatch type
					foreach (var tag in new[] { "emul", "split", "std", "sv", "stk", "osv", "nosv" }) {
						if (failStage.Contains("," + tag + ",") || failStage.EndsWith("," + tag)) {
							npFailCounts.TryGetValue(tag, out int tc);
							npFailCounts[tag] = tc + 1;
						}
					}
				}
			}
			// Accumulate Rebuilder counters (now safe — reset before each dispatch above)
			rbNone += Rebuilder.SkipNone; rbNoTrace += Rebuilder.SkipNoTrace;
			rbUnkExit += Rebuilder.SkipUnknownExit; rbResolve += Rebuilder.SkipResolve;
			rbTarget += Rebuilder.SkipTarget; rbScope += Rebuilder.SkipScope;
			rbBounds += Rebuilder.SkipBounds; rbBranch += Rebuilder.SkipBranch;
			rbNoop += Rebuilder.SkipNoop; rbApplied += Rebuilder.Applied;
			// Accumulate LoopMachineRewriter counters
			lmDetected += LoopMachineRewriter.Detected; lmRewrites += LoopMachineRewriter.Rewrites;
			lmNoStore += LoopMachineRewriter.SkipNoStore; lmResolve += LoopMachineRewriter.SkipResolve;
			lmTarget += LoopMachineRewriter.SkipTarget; lmScope += LoopMachineRewriter.SkipScope;
			lmStack += LoopMachineRewriter.SkipStack; lmBranch += LoopMachineRewriter.SkipBranch;
			lmNoop += LoopMachineRewriter.SkipNoop;
		}

		if (totalDispatches > 0) {
			string failInfo = "";
			foreach (var kv in npFailCounts)
				failInfo += $" {kv.Key}={kv.Value}";
			Logger.v("  XOR-switch: {0} dispatches ({1} emul), {2} rewritten (new={3}, leg={4}), {5} res, {6} unrec, fail: {7} no-dv, {8} has-dv [{9}]",
				totalDispatches, embeddedMulDispatches, rewrittenDispatches,
				newPipelineHits, legacyHits, residualSwitches, failedModel,
				failedNoDvs, failedWithDvs, failInfo.Trim());
			if (rbApplied + rbNone + rbNoTrace + rbUnkExit + rbResolve + rbTarget + rbBranch + rbNoop > 0)
				Logger.v("    rebuild: applied={0} skipNone={1} noTrace={2} unkExit={3} resolve={4} target={5} scope={6} branch={7} noop={8}",
					rbApplied, rbNone, rbNoTrace, rbUnkExit, rbResolve, rbTarget, rbScope, rbBranch, rbNoop);
			if (lmDetected + lmRewrites > 0)
				Logger.v("    loop-machine: detected={0} rewrites={1} noStore={2} resolve={3} target={4} scope={5} stack={6} branch={7} noop={8}",
					lmDetected, lmRewrites, lmNoStore, lmResolve, lmTarget, lmScope, lmStack, lmBranch, lmNoop);
			if (BlockSlicer.DiagSliceAttempts > 0)
				Logger.v("    slice: attempts={0} mulxor={1} const={2} none={3}",
					BlockSlicer.DiagSliceAttempts, BlockSlicer.DiagSliceMulXor,
					BlockSlicer.DiagSliceConst, BlockSlicer.DiagSliceNone);
		}
		return modified;
	}

	/// <summary>
	///     Detects if a switch block is a residual dispatch left behind after
	///     partial rewriting removed the XOR setup from predecessor blocks.
	///     These have too few instructions to match the full dispatch pattern
	///     but still have the rem.un + ldc.i4 + switch suffix.
	/// </summary>
	static bool IsResidualSwitch(Block block) {
		var instrs = block.Instructions;
		if (instrs.Count >= 5)
			return false; // Enough instructions for a full pattern — not residual
		if (instrs.Count < 3)
			return true; // Just switch or switch+something — clearly residual
		// Check for partial dispatch header: ... ldc.i4 MOD; rem.un; switch
		int si = instrs.Count - 1;
		if (instrs[si].OpCode.Code != Code.Switch)
			return false;
		si--;
		if (instrs[si].OpCode.Code == Code.Rem_Un) {
			si--;
			return instrs[si].IsLdcI4();
		}
		return true;
	}

	bool TryDeobfuscateDispatch(Block switchBlock, out bool usedNewPipeline, out string failStage) {
		usedNewPipeline = false;
		failStage = null;

		// Shared preprocessing: fold opaque constants
		PatternMatcher.FoldOpaqueConstants(switchBlock);
		foreach (var source in switchBlock.Sources) {
			if (source != switchBlock)
				PatternMatcher.FoldOpaqueConstants(source);
		}

		// Stage 0: Build dispatch model
		var model = DispatchModel.TryCreate(switchBlock, patternMatcher, simulator);
		if (model == null) {
			failStage = "model";
			return false;
		}

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
			switchBlock, info, reverseReachable, blockToCase, out var dvToSv);
		model.DvToSv = dvToSv;
		if (info.SelfLoopEligible && caseToDispatchVals.Count == 0)
			constantDiscovery.SeedSelfLoopDispatchVals(switchBlock, info, caseToDispatchVals, reverseReachable, blockToCase);

		if (caseToDispatchVals.Count == 0)
			failStage = "no-dvs";
		else {
			string dtype = info.HasEmbeddedMul ? (info.SplitEmbeddedMul ? "split" : "emul") : "std";
			string sv = info.StateVar != null ? "sv" : "stk";
			string osv = info.OriginalStateVar != null ? "osv" : "nosv";
			string dv = info.DispatchVar != null ? "dv" : "nodv";
			failStage = $"dvs={caseToDispatchVals.Count}/{info.Modulus},{dtype},{sv},{osv},{dv}";
		}

		// Run both pipelines: new pipeline handles what it can, legacy handles the rest.
		// The new pipeline rewrites case blocks it can trace; the legacy pipeline
		// picks up remaining cases through its own pattern matching.
		bool modified = false;

		// Loop-machine path: targeted constant-transition shortcut for split-embedded-mul
		// dispatchers where case blocks write constants to StateVar (no OriginalStateVar).
		if (info.SplitEmbeddedMul && info.OriginalStateVar == null && info.StateVar != null) {
			if (LoopMachineRewriter.TryRewrite(model, blockToCase,
					patternMatcher, constantDiscovery, locals)) {
				modified = true;
			}
		}

		// New pipeline: handles cases the legacy pipeline misses.
		if (TryNewPipeline(model, caseToDispatchVals, blockToCase, out string newPipeStage)) {
			usedNewPipeline = true;
			modified = true;
		}
		// Don't overwrite failStage — keep the dispatch type info for diagnostics

		// Legacy pipeline (runs on remaining unhandled cases)
		modified |= RewriteConstantSources(switchBlock, info);
		modified |= RewriteMultiplyXorSources(switchBlock, info, caseToDispatchVals, blockToCase);
		if (info.SelfLoopEligible)
			modified |= RewriteSelfLoopSources(switchBlock, info, caseToDispatchVals, blockToCase);
		modified |= LegacyRewriter.RemoveDeadSwitchCases(switchBlock, info, caseToDispatchVals);

		if (modified)
			failStage = null;

		return modified;
	}

	bool TryNewPipeline(DispatchModel model,
		Dictionary<int, HashSet<uint>> caseToDispatchVals,
		Dictionary<Block, int> blockToCase, out string newPipeStage) {
		newPipeStage = null;
		// Early exit: tracing needs dispatch vals to seed from
		if (caseToDispatchVals.Count == 0) {
			newPipeStage = "no-dvs";
			return false;
		}

		// Stage 1: Slice (computed once, shared by tracer and rebuilder)
		var sliced = BlockSlicer.SliceAll(model, null,
			blockToCase, patternMatcher, constantDiscovery);
		if (sliced == null) {
			newPipeStage = "slice-null";
			return false;
		}

		// Stage 2: Trace (propagates dispatch vals through the state machine)
		var traced = StateTracer.Trace(model, caseToDispatchVals,
			blockToCase, sliced);
		// traced may be null if no cases could be traced, but the Rebuilder
		// can still rewrite Constant blocks (which don't need entry dispatch vals).

		// Stage 3: Rebuild (uses per-block slice data for exits, not per-case traced exits)
		bool result = Rebuilder.Rebuild(model, traced, sliced, blockToCase, caseToDispatchVals);
		if (!result)
			newPipeStage = "rebuild-none";
		return result;
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
