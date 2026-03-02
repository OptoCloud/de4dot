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

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4.cflow;

/// <summary>
///     Normalized dispatch view. Absorbs all domain math so callers
///     never call DomainMath directly. Provides simulation verification
///     and uniform target resolution.
/// </summary>
class DispatchModel {
	readonly Simulator simulator;

	DispatchModel(Block switchBlock, DispatchInfo info, Simulator simulator) {
		SwitchBlock = switchBlock;
		Info = info;
		this.simulator = simulator;
		EntryStackDepth = info.StateVar != null ? 0 : 1;
	}

	public DispatchInfo Info { get; private set; }
	public Block SwitchBlock { get; }
	public int EntryStackDepth { get; }

	/// <summary>
	///     Maps (caseIdx, dispatchVal) → StateVar value for split-embedded-mul dispatches.
	///     Enables forward propagation without needing modular inverse of EmbeddedMul.
	///     Null when not applicable (non-split dispatches).
	/// </summary>
	public Dictionary<(int caseIdx, uint dv), uint> DvToSv { get; set; }

	/// <summary>
	///     Updates the Info field (needed when OriginalStateVar is discovered after construction).
	/// </summary>
	internal void SetInfo(DispatchInfo updatedInfo) => Info = updatedInfo;

	/// <summary>
	///     Full chain: stateVarValue → dispatchVal → caseIndex.
	///     Returns null if modulus would be zero.
	/// </summary>
	public int? EvalState(uint stateVarValue) {
		if (Info.Modulus == 0)
			return null;
		uint dv = DomainMath.StateToDispatchVal(Info, stateVarValue);
		return DomainMath.NormalizeCaseIndex(Info, dv);
	}

	/// <summary>
	///     Converts a STATE-domain value through StateValToStateVarInput, then
	///     evaluates to a case index.
	/// </summary>
	public int? EvalStateVar(uint stateVal) {
		uint svInput = DomainMath.StateValToStateVarInput(Info, stateVal);
		return EvalState(svInput);
	}

	/// <summary>
	///     Returns the target block for a case index, with bounds checking.
	/// </summary>
	public Block GetTarget(int caseIndex) => CfgAnalysis.VerifyAndGetTarget(SwitchBlock, Info, caseIndex);

	/// <summary>
	///     Simulation hard gate: verifies stateVarInput produces expectedCase.
	/// </summary>
	public bool Verify(uint stateVarInput, int expectedCase) =>
		simulator.VerifyDispatch(SwitchBlock, Info, stateVarInput, expectedCase);

	/// <summary>
	///     All dispatch vals must resolve to the same target via the given
	///     state-to-stateVar conversion. Returns null if any fail or disagree.
	///     stateToStateVar: converts a state-domain value to stateVar-domain.
	///     If null, identity is used.
	/// </summary>
	public (int caseIdx, Block target)? ResolveUniform(
		HashSet<uint> stateValues, Func<uint, uint> stateToStateVar) {
		int? resolvedCase = null;
		uint firstSvInput = 0;
		uint secondSvInput = 0;
		bool hasSecond = false;

		foreach (uint sv in stateValues) {
			uint svInput = stateToStateVar != null ? stateToStateVar(sv) : sv;
			uint dv = DomainMath.StateToDispatchVal(Info, svInput);
			int ci = DomainMath.NormalizeCaseIndex(Info, dv);

			if (resolvedCase == null) {
				resolvedCase = ci;
				firstSvInput = svInput;
			}
			else if (resolvedCase.Value != ci) {
				return null;
			}
			else if (!hasSecond) {
				secondSvInput = svInput;
				hasSecond = true;
			}
		}

		if (resolvedCase == null)
			return null;

		// Hard gate: simulation must agree
		if (!Verify(firstSvInput, resolvedCase.Value))
			return null;
		if (hasSecond && !Verify(secondSvInput, resolvedCase.Value))
			return null;

		var target = GetTarget(resolvedCase.Value);
		if (target == null)
			return null;

		return (resolvedCase.Value, target);
	}

	/// <summary>
	///     Attempts to create a DispatchModel from a switch block.
	///     Returns null if the block doesn't match the XOR-switch pattern.
	///     Callers should call FoldOpaqueConstants before this method.
	/// </summary>
	public static DispatchModel TryCreate(Block switchBlock,
		PatternMatcher matcher, Simulator simulator) {
		if (!matcher.TryExtractDispatchInfo(switchBlock, out var info))
			return null;
		if (switchBlock.Targets == null || switchBlock.Targets.Count == 0)
			return null;
		if (info.Modulus != (uint)switchBlock.Targets.Count)
			return null;

		// When dispatch info was extracted from a folded constant (InternalStateVarInput),
		// verify via simulation that the constant actually produces the expected case index.
		// This rejects false positives from the relaxed expression length guard.
		if (info.InternalStateVarInput.HasValue) {
			uint svInput = info.InternalStateVarInput.Value;
			uint dv = DomainMath.StateToDispatchVal(info, svInput);
			int expectedCase = DomainMath.NormalizeCaseIndex(info, dv);
			if (!simulator.VerifyDispatch(switchBlock, info, svInput, expectedCase))
				return null;
		}

		return new DispatchModel(switchBlock, info, simulator);
	}
}
