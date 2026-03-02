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

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4.cflow;

enum StateUpdateKind {
	Constant,
	MulXor,
	SelfLoop,
	None
}

/// <summary>
///     A case block sliced into payload and state-update regions, with
///     exact stack depth at the cut point.
/// </summary>
struct SlicedBlock {
	public Block Block;
	public int CaseIndex;
	public StateUpdateKind UpdateKind;
	public int PayloadEnd; // instruction index where state-update begins
	public int StackDepthAtCut; // exact stack depth at PayloadEnd
	public uint? ConstantNext; // STATE-domain value for Constant kind
	public uint MulConst; // for MulXor kind
	public uint XorConst; // for MulXor kind
	public MulXorInputDomain InputDomain; // which domain the MulXor transition loads from
}

/// <summary>
///     Slices case blocks into payload + state-update regions.
///     Reuses PatternMatcher and ConstantDiscovery for pattern detection.
/// </summary>
static class BlockSlicer {
	/// <summary>
	///     Slices all case-region blocks from switchBlock.Sources and blockToCase.
	///     Returns null if no blocks could be sliced.
	/// </summary>
	internal static Dictionary<Block, SlicedBlock> SliceAll(
		DispatchModel model, Dictionary<int, (StateValue entry, StateValue exit)> traced,
		Dictionary<Block, int> blockToCase,
		PatternMatcher matcher, ConstantDiscovery discovery) {
		var result = new Dictionary<Block, SlicedBlock>();
		var switchBlock = model.SwitchBlock;
		var info = model.Info;

		// Scan direct sources of the switch that are case blocks
		foreach (var source in switchBlock.Sources) {
			if (source == switchBlock)
				continue;
			if (!blockToCase.TryGetValue(source, out int caseIdx))
				continue;
			var sliced = TrySlice(source, caseIdx, info, matcher, discovery);
			if (sliced != null)
				result[source] = sliced.Value;
		}

		// Scan ALL blocks in blockToCase — not just switch sources/targets.
		// For split dispatches, case tail blocks branch to the predecessor (not
		// the switch), so they aren't in switchBlock.Sources. For multi-block
		// case bodies, the state transition pattern is typically in the tail.
		foreach (var kv in blockToCase) {
			var block = kv.Key;
			if (block == switchBlock || result.ContainsKey(block))
				continue;
			var sliced = TrySlice(block, kv.Value, info, matcher, discovery);
			if (sliced != null)
				result[block] = sliced.Value;
		}

		return result.Count > 0 ? result : null;
	}

	// Diagnostic counters for slice analysis
	internal static int DiagSliceAttempts, DiagSliceMulXor, DiagSliceConst, DiagSliceNone;

	/// <summary>
	///     Attempts to slice a single block into payload + state-update.
	/// </summary>
	static SlicedBlock? TrySlice(Block block, int caseIndex, DispatchInfo info,
		PatternMatcher matcher, ConstantDiscovery discovery) {
		var instrs = block.Instructions;
		if (instrs.Count == 0)
			return null;

		DiagSliceAttempts++;

		// Try multiply-XOR pattern first (it's longer and more specific)
		if (matcher.TryGetMultiplyXorPattern(block, info,
			    out uint mulConst, out uint xorConst, out int patStart, out int patLen,
			    out var loadedVar)) {
			if (CfgAnalysis.IsTrailingSafe(instrs, patStart + patLen)) {
				int depth = StackAnalyzer.DepthAt(instrs, patStart);
				if (depth >= 0) {
					DiagSliceMulXor++;
					var inputDomain = DomainMath.ClassifyMulXorInput(info, loadedVar);
					return new SlicedBlock {
						Block = block,
						CaseIndex = caseIndex,
						UpdateKind = StateUpdateKind.MulXor,
						PayloadEnd = patStart,
						StackDepthAtCut = depth,
						MulConst = mulConst,
						XorConst = xorConst,
						InputDomain = inputDomain
					};
				}
			}
		}

		// Try constant store pattern
		(uint stateVal, int startIdx, int patternLen) = discovery.FindConstantForDispatch(instrs, info);
		if (startIdx >= 0 && patternLen > 0) {
			int patternEnd = startIdx + patternLen;
			if (CfgAnalysis.IsTrailingSafe(instrs, patternEnd)) {
				int depth = StackAnalyzer.DepthAt(instrs, startIdx);
				if (depth >= 0) {
					DiagSliceConst++;
					return new SlicedBlock {
						Block = block,
						CaseIndex = caseIndex,
						UpdateKind = StateUpdateKind.Constant,
						PayloadEnd = startIdx,
						StackDepthAtCut = depth,
						ConstantNext = stateVal
					};
				}
			}
		}

		// Self-loop: no state update in the block itself
		if (info.SelfLoopEligible) {
			return new SlicedBlock {
				Block = block,
				CaseIndex = caseIndex,
				UpdateKind = StateUpdateKind.SelfLoop,
				PayloadEnd = instrs.Count,
				StackDepthAtCut = 0
			};
		}

		// No recognized state update — mark as None
		DiagSliceNone++;
		return new SlicedBlock {
			Block = block,
			CaseIndex = caseIndex,
			UpdateKind = StateUpdateKind.None,
			PayloadEnd = instrs.Count,
			StackDepthAtCut = 0
		};
	}
}
