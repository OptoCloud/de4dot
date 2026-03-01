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
///     Rewrite logic for XOR-switch dispatch deobfuscation.
///     Candidate builders (TryBuild*) are pure: they compute and verify without mutation.
///     ApplyCandidate performs the actual CFG mutation.
/// </summary>
class LegacyRewriter {
	readonly ConstantDiscovery constantDiscovery;
	readonly PatternMatcher patternMatcher;
	readonly Simulator simulator;

	internal LegacyRewriter(PatternMatcher patternMatcher,
		ConstantDiscovery constantDiscovery, Simulator simulator) {
		this.patternMatcher = patternMatcher;
		this.constantDiscovery = constantDiscovery;
		this.simulator = simulator;
	}

	/// <summary>
	///     Centralized CFG mutation. Calls ReplaceLastInstrsWithBranch on the source
	///     block, optionally inserting pop;pop for cross-block XOR2 stack cleanup.
	/// </summary>
	internal static void ApplyCandidate(RewriteCandidate candidate) {
		candidate.SourceBlock.ReplaceLastInstrsWithBranch(
			candidate.InstructionsToRemove, candidate.TargetBlock);
		if (candidate.NeedStackCleanup) {
			candidate.SourceBlock.Add(new Instr(OpCodes.Pop.ToInstruction()));
			candidate.SourceBlock.Add(new Instr(OpCodes.Pop.ToInstruction()));
		}
	}

	/// <summary>
	///     Resolves a uniform target from a set of dispatch vals using a transition function.
	///     All dispatch vals must produce the same target case index (fail closed).
	///     Uses 2-sample simulation as a hard gate to verify the transition formula.
	///     transitionFn: maps a dispatch val to (caseIdx, stateVarInputForSimulation).
	///     Returns (caseIdx, targetBlock) on success, null if any check fails.
	/// </summary>
	internal (int caseIdx, Block targetBlock)? ResolveUniformTarget(
		Block switchBlock, DispatchInfo info, HashSet<uint> dispatchVals,
		Func<uint, (int caseIdx, uint stateVarInput)> transitionFn) {
		int? resolvedCaseIdx = null;
		uint firstSimInput = 0;
		uint secondSimInput = 0;
		bool hasSecond = false;

		foreach (uint dv in dispatchVals) {
			(int caseIdx, uint stateVarInput) = transitionFn(dv);

			if (resolvedCaseIdx == null) {
				resolvedCaseIdx = caseIdx;
				firstSimInput = stateVarInput;
			}
			else if (resolvedCaseIdx.Value != caseIdx) {
				return null;
			}
			else if (!hasSecond) {
				secondSimInput = stateVarInput;
				hasSecond = true;
			}
		}

		if (resolvedCaseIdx == null)
			return null;

		// Phase 2: Self-check (hard gate) on up to 2 samples
		if (!simulator.VerifyDispatch(switchBlock, info, firstSimInput, resolvedCaseIdx.Value))
			return null;
		if (hasSecond && !simulator.VerifyDispatch(switchBlock, info, secondSimInput, resolvedCaseIdx.Value))
			return null;

		var targetBlock = CfgAnalysis.VerifyAndGetTarget(switchBlock, info, resolvedCaseIdx.Value);
		if (targetBlock == null)
			return null;

		return (resolvedCaseIdx.Value, targetBlock);
	}

	/// <summary>
	///     Builds a candidate for internal constant dispatch: the dispatch block has a
	///     merged dead-code prefix that always produces the same state value.
	///     Replaces the entire switch block with a direct branch.
	/// </summary>
	internal RewriteCandidate? TryBuildInternalConstantCandidate(Block switchBlock, DispatchInfo info) {
		if (!info.InternalStateVarInput.HasValue)
			return null;

		uint stateVarInput = info.InternalStateVarInput.Value;
		uint dispatchVal = DomainMath.StateToDispatchVal(info, stateVarInput);
		int caseIdx = DomainMath.NormalizeCaseIndex(info, dispatchVal);

		int simCaseIdx = simulator.SimulateDispatchFromEmpty(switchBlock);
		if (simCaseIdx != caseIdx)
			return null;

		var targetBlock = CfgAnalysis.VerifyAndGetTarget(switchBlock, info, caseIdx);
		if (targetBlock == null)
			return null;

		return new RewriteCandidate {
			SourceBlock = switchBlock,
			TargetBlock = targetBlock,
			InstructionsToRemove = switchBlock.Instructions.Count,
			NeedStackCleanup = false
		};
	}

	/// <summary>
	///     Builds a candidate for a constant source block: stores a constant to the
	///     state variable then falls through to the dispatch.
	/// </summary>
	internal RewriteCandidate? TryBuildConstantSourceCandidate(
		Block switchBlock, DispatchInfo info, Block source) {
		if (source.Targets != null && source.Targets.Count > 0)
			return null;

		var instrs = source.Instructions;
		if (instrs.Count == 0)
			return null;

		(uint stateVal, int startIdx, int patternLen) = constantDiscovery.FindConstantForDispatch(instrs, info);
		if (startIdx < 0 || patternLen <= 0)
			return null;

		int patternEnd = startIdx + patternLen;
		if (!CfgAnalysis.IsTrailingSafe(instrs, patternEnd))
			return null;
		int numToRemove = instrs.Count - startIdx;
		if (numToRemove <= 0 || numToRemove > instrs.Count)
			return null;

		(int caseIdx, uint stateVarInput) = DomainMath.StateValToCase(info, stateVal);

		if (!simulator.VerifyDispatch(switchBlock, info, stateVarInput, caseIdx))
			return null;

		var targetBlock = CfgAnalysis.VerifyAndGetTarget(switchBlock, info, caseIdx);
		if (targetBlock == null)
			return null;

		return new RewriteCandidate {
			SourceBlock = source,
			TargetBlock = targetBlock,
			InstructionsToRemove = numToRemove,
			NeedStackCleanup = false
		};
	}

	/// <summary>
	///     Builds a candidate for a pop-through predecessor: pushes a constant via
	///     the obfuscator's dup pattern (ldc.i4 X; dup; [br pop_block]).
	/// </summary>
	internal RewriteCandidate? TryBuildPopThroughCandidate(
		Block switchBlock, DispatchInfo info, Block pred) {
		var instrs = pred.Instructions;
		if (instrs.Count == 0)
			return null;

		if (pred.Targets != null && pred.Targets.Count > 0)
			return null;

		int lastIdx = CfgAnalysis.FindEffectiveEnd(instrs);
		if (lastIdx < 1 || instrs[lastIdx].OpCode.Code != Code.Dup)
			return null;

		var result = patternMatcher.SliceBackward(instrs, lastIdx - 1);
		if (result == null)
			return null;
		uint stateVal = result.Value.value;
		int startIdx = result.Value.startIdx;

		if (!CfgAnalysis.IsTrailingSafe(instrs, lastIdx + 1))
			return null;
		int numToRemove = instrs.Count - startIdx;
		if (numToRemove <= 0 || numToRemove > instrs.Count)
			return null;

		(int caseIdx, uint stateVarInput) = DomainMath.StateValToCase(info, stateVal);

		if (!simulator.VerifyDispatch(switchBlock, info, stateVarInput, caseIdx))
			return null;

		var targetBlock = CfgAnalysis.VerifyAndGetTarget(switchBlock, info, caseIdx);
		if (targetBlock == null)
			return null;

		return new RewriteCandidate {
			SourceBlock = pred, TargetBlock = targetBlock, InstructionsToRemove = numToRemove, NeedStackCleanup = false
		};
	}

	/// <summary>
	///     Builds a candidate for a multiply-XOR transition block.
	///     Pattern: ldloc V; ldc.i4 MUL2; mul; ldc.i4 XOR3; xor; [stloc S]
	/// </summary>
	internal RewriteCandidate? TryBuildMulXorCandidate(
		Block switchBlock, DispatchInfo info, Block source,
		Dictionary<int, HashSet<uint>> caseToDispatchVals, Dictionary<Block, int> blockToCase) {
		if (!patternMatcher.TryGetMultiplyXorPattern(source, info, out uint mulConst, out uint xor2Const,
			    out int patternStart, out int patternLen))
			return null;

		int patternEnd = patternStart + patternLen;
		if (!CfgAnalysis.IsTrailingSafe(source.Instructions, patternEnd))
			return null;
		int numToRemove = source.Instructions.Count - patternStart;
		if (numToRemove <= 0 || numToRemove > source.Instructions.Count)
			return null;

		if (!blockToCase.TryGetValue(source, out int ownerCase))
			return null;
		if (!caseToDispatchVals.TryGetValue(ownerCase, out var dispatchVals))
			return null;

		var resolved = ResolveUniformTarget(switchBlock, info, dispatchVals, dv => {
			uint nextState = DomainMath.MulXorToNextState(dv, mulConst, xor2Const);
			uint svInput = DomainMath.StateValToStateVarInput(info, nextState);
			uint nextDv = DomainMath.StateToDispatchVal(info, svInput);
			int ci = DomainMath.NormalizeCaseIndex(info, nextDv);
			return (ci, svInput);
		});

		if (resolved == null)
			return null;

		return new RewriteCandidate {
			SourceBlock = source,
			TargetBlock = resolved.Value.targetBlock,
			InstructionsToRemove = numToRemove,
			NeedStackCleanup = false
		};
	}

	/// <summary>
	///     Builds a candidate for a self-loop source in embedded-mul dispatches.
	///     The dispatch block itself is the state transition (case blocks don't modify state).
	/// </summary>
	internal RewriteCandidate? TryBuildSelfLoopCandidate(
		Block switchBlock, DispatchInfo info, Block source,
		Dictionary<int, HashSet<uint>> caseToDispatchVals, Dictionary<Block, int> blockToCase) {
		if (source.Targets != null && source.Targets.Count > 0)
			return null;

		// Skip sources that have their own transition (constant or mul-xor).
		(_, int constStartIdx, _) = constantDiscovery.FindConstantForDispatch(source.Instructions, info);
		if (constStartIdx >= 0)
			return null;
		if (patternMatcher.TryGetMultiplyXorPattern(source, info, out _, out _, out _, out _))
			return null;

		if (!blockToCase.TryGetValue(source, out int ownerCase))
			return null;
		if (!caseToDispatchVals.TryGetValue(ownerCase, out var dispatchVals))
			return null;

		var resolved = ResolveUniformTarget(switchBlock, info, dispatchVals, dv => {
			uint nextDv = DomainMath.SelfLoopNext(info, dv);
			int ci = DomainMath.NormalizeCaseIndex(info, nextDv);
			// Self-loop: stateVar holds the previous dispatch val
			return (ci, dv);
		});

		if (resolved == null)
			return null;

		return new RewriteCandidate {
			SourceBlock = source,
			TargetBlock = resolved.Value.targetBlock,
			InstructionsToRemove = 0,
			NeedStackCleanup = false
		};
	}

	/// <summary>
	///     Redirects dead switch case targets to fallthrough.
	///     A case is considered dead when ALL conditions hold:
	///     1. No known dispatch val maps to it (no entry in caseToDispatchVals)
	///     2. The target block has no sources other than the switch block
	///     3. We have sufficient dispatch val coverage (>=50% of cases discovered)
	/// </summary>
	internal static bool RemoveDeadSwitchCases(Block switchBlock, DispatchInfo info,
		Dictionary<int, HashSet<uint>> caseToDispatchVals) {
		if (switchBlock.Targets == null || switchBlock.FallThrough == null)
			return false;

		int targetCount = switchBlock.Targets.Count;
		if (targetCount == 0)
			return false;

		if (info.Modulus != (uint)targetCount)
			return false;

		int coveredCases = caseToDispatchVals.Count;
		if (coveredCases * 2 < targetCount)
			return false;

		bool modified = false;
		var fallThrough = switchBlock.FallThrough;

		for (int i = 0; i < targetCount; i++) {
			var target = switchBlock.Targets[i];
			if (target == null || target == fallThrough)
				continue;

			if (caseToDispatchVals.ContainsKey(i))
				continue;

			bool hasOtherSources = false;
			foreach (var src in target.Sources) {
				if (src != switchBlock) {
					hasOtherSources = true;
					break;
				}
			}

			if (hasOtherSources)
				continue;

			switchBlock.SetNewTarget(i, fallThrough);
			modified = true;
		}

		return modified;
	}
}
