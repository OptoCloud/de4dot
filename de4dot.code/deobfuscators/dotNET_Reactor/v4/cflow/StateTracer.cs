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
///     Worklist-based state tracer. Computes per-case entry/exit state values
///     by propagating constants through the dispatch-case-dispatch cycle.
///     Returns null if tracing fails (Unknown states or exceeds bounds).
/// </summary>
static class StateTracer {
	/// <summary>
	///     Returns per-case-index traced states, or null if tracing fails.
	///     Entry = set of dispatch vals that can reach this case.
	///     Exit = set of next-state values produced by this case's state update.
	///     Accepts pre-computed shared structures from the orchestrator.
	/// </summary>
	internal static Dictionary<int, (StateValue entry, StateValue exit)> Trace(
		DispatchModel model,
		Dictionary<int, HashSet<uint>> caseToDispatchVals,
		Dictionary<Block, int> blockToCase,
		Dictionary<Block, SlicedBlock> sliced) {
		if (caseToDispatchVals == null || caseToDispatchVals.Count == 0)
			return null;

		var info = model.Info;
		var dvToSv = model.DvToSv;

		// Build per-case entry states from collected dispatch vals
		var result = new Dictionary<int, (StateValue entry, StateValue exit)>();

		foreach (var kv in caseToDispatchVals) {
			int caseIdx = kv.Key;
			var dispatchVals = kv.Value;

			var entryState = StateValue.FromSet(dispatchVals);
			if (entryState.IsUnknown)
				continue;

			var exitState = ComputeExitState(caseIdx, dispatchVals, info, sliced, dvToSv);
			result[caseIdx] = (entryState, exitState);
		}

		// Worklist propagation: exit states feed into entry states of target cases
		bool changed = true;
		int maxIterations = Math.Max(result.Count * 4, (int)info.Modulus * 16);
		while (changed && maxIterations-- > 0) {
			changed = false;
			var updates = new Dictionary<int, StateValue>();

			foreach (var kv in result) {
				var exit = kv.Value.exit;
				if (exit.IsUnknown || exit.Values == null)
					continue;

				foreach (uint exitVal in exit.Values) {
					uint svInput = DomainMath.StateValToStateVarInput(info, exitVal);
					uint dv = DomainMath.StateToDispatchVal(info, svInput);
					int targetCase = DomainMath.NormalizeCaseIndex(info, dv);

					// Track STATEVAR-domain value for the new dispatch val
					if (dvToSv != null)
						dvToSv[(targetCase, dv)] = svInput;

					if (!updates.TryGetValue(targetCase, out var existing))
						updates[targetCase] = StateValue.Known(dv);
					else
						updates[targetCase] = existing.Join(StateValue.Known(dv));
				}
			}

			foreach (var kv in updates) {
				int targetCase = kv.Key;
				var newEntry = kv.Value;

				if (newEntry.IsUnknown)
					continue;

				if (result.TryGetValue(targetCase, out var existing)) {
					var joined = existing.entry.Join(newEntry);
					if (joined.IsUnknown)
						continue;

					if (joined.Values != null && existing.entry.Values != null &&
					    joined.Values.Count != existing.entry.Values.Count) {
						var newDispatchVals = new HashSet<uint>();
						foreach (uint v in joined.Values)
							newDispatchVals.Add(v);

						var exitState = ComputeExitState(targetCase, newDispatchVals, info, sliced, dvToSv);
						result[targetCase] = (joined, exitState);
						changed = true;
					}
				}
				else {
					var newDispatchVals = new HashSet<uint>();
					if (newEntry.Values != null) {
						foreach (uint v in newEntry.Values)
							newDispatchVals.Add(v);
					}

					var exitState = ComputeExitState(targetCase, newDispatchVals, info, sliced, dvToSv);
					result[targetCase] = (newEntry, exitState);
					changed = true;
				}
			}
		}

		return result.Count > 0 ? result : null;
	}

	static StateValue ComputeExitState(int caseIdx, HashSet<uint> dispatchVals,
		DispatchInfo info, Dictionary<Block, SlicedBlock> sliced,
		Dictionary<(int caseIdx, uint dv), uint> dvToSv = null) {
		SlicedBlock? caseSlice = null;
		if (sliced != null) {
			// Prefer blocks with actual state updates over None blocks (trampolines).
			// For split dispatches, switch targets are often br-only trampolines sliced
			// as None; the real state transition is in the case body one hop further.
			SlicedBlock? noneSlice = null;
			foreach (var kv in sliced) {
				if (kv.Value.CaseIndex == caseIdx) {
					if (kv.Value.UpdateKind != StateUpdateKind.None) {
						caseSlice = kv.Value;
						break;
					}
					noneSlice ??= kv.Value;
				}
			}
			caseSlice ??= noneSlice;
		}

		if (caseSlice == null)
			return StateValue.MakeUnknown();

		var slice = caseSlice.Value;
		switch (slice.UpdateKind) {
		case StateUpdateKind.Constant:
			if (slice.ConstantNext.HasValue)
				return StateValue.Known(slice.ConstantNext.Value);
			return StateValue.MakeUnknown();

		case StateUpdateKind.MulXor:
			var nextStates = new HashSet<uint>();
			foreach (uint dv in dispatchVals) {
				uint? mulInput = DomainMath.DispatchValToMulXorInput(
					info, dv, slice.InputDomain, caseIdx, dvToSv);
				if (mulInput == null)
					return StateValue.MakeUnknown();

				uint nextState = DomainMath.MulXorToNextState(mulInput.Value, slice.MulConst, slice.XorConst);
				nextStates.Add(nextState);
			}

			return StateValue.FromSet(nextStates);

		case StateUpdateKind.SelfLoop:
			var selfNextStates = new HashSet<uint>();
			foreach (uint dv in dispatchVals) {
				uint nextDv = DomainMath.SelfLoopNext(info, dv);
				selfNextStates.Add(nextDv);
			}

			return StateValue.FromSet(selfNextStates);

		default:
			return StateValue.MakeUnknown();
		}
	}
}
