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
///     Property-based self-check: forward-evaluates dispatch block IL with a concrete
///     uint stack. Used to independently verify domain math before rewrites.
/// </summary>
class Simulator {
	readonly IList<Local> locals;

	internal Simulator(IList<Local> locals) => this.locals = locals;

	internal int SimulateDispatch(Block switchBlock, Local stateVarLocal, uint stateVarInput) {
		var stack = new List<uint>();
		var localValues = new Dictionary<Local, uint>();

		if (stateVarLocal != null)
			localValues[stateVarLocal] = stateVarInput;
		else
			stack.Add(stateVarInput);

		return SimulateDispatchCore(switchBlock, stack, localValues);
	}

	internal int SimulateDispatchForInfo(Block switchBlock, DispatchInfo info, uint stateVarInput) {
		if (info.SplitEmbeddedMul) {
			uint xor2 = unchecked(info.XorKey ^ info.OriginalXorKey);
			uint stackInput = unchecked((stateVarInput * info.EmbeddedMul) ^ xor2);
			return SimulateDispatch(switchBlock, null, stackInput);
		}

		return SimulateDispatch(switchBlock, info.StateVar, stateVarInput);
	}

	internal int SimulateDispatchFromEmpty(Block switchBlock) =>
		SimulateDispatchCore(switchBlock, new List<uint>(), new Dictionary<Local, uint>());

	/// <summary>
	///     Centralizes the "simulate then compare" pattern used in every rewrite method.
	///     Returns true if simulation succeeds and the simulated case index matches the expected one.
	/// </summary>
	internal bool VerifyDispatch(Block switchBlock, DispatchInfo info, uint stateVarInput, int expectedCaseIdx) {
		int simCaseIdx = SimulateDispatchForInfo(switchBlock, info, stateVarInput);
		return simCaseIdx == expectedCaseIdx;
	}

	int SimulateDispatchCore(Block switchBlock, List<uint> stack, Dictionary<Local, uint> localValues) {
		var instrs = switchBlock.Instructions;

		for (int i = 0; i < instrs.Count; i++) {
			var instr = instrs[i];
			var code = instr.OpCode.Code;

			if (instr.IsLdcI4()) {
				stack.Add((uint)instr.GetLdcI4Value());
				continue;
			}

			if (instr.IsLdloc()) {
				var local = Instr.GetLocalVar(locals, instr);
				if (local != null && localValues.TryGetValue(local, out uint val))
					stack.Add(val);
				else
					return -1;
				continue;
			}

			if (instr.IsStloc()) {
				if (stack.Count < 1) return -1;
				var local = Instr.GetLocalVar(locals, instr);
				uint val = stack[stack.Count - 1];
				stack.RemoveAt(stack.Count - 1);
				if (local != null)
					localValues[local] = val;
				continue;
			}

			if (code == Code.Xor || code == Code.Mul || code == Code.Add || code == Code.Sub) {
				if (stack.Count < 2) return -1;
				uint r = stack[stack.Count - 1];
				stack.RemoveAt(stack.Count - 1);
				uint l = stack[stack.Count - 1];
				stack.RemoveAt(stack.Count - 1);
				stack.Add(DomainMath.ApplyBinaryOp(code, l, r));
				continue;
			}

			if (code == Code.Rem_Un) {
				if (stack.Count < 2) return -1;
				uint r = stack[stack.Count - 1];
				stack.RemoveAt(stack.Count - 1);
				uint l = stack[stack.Count - 1];
				stack.RemoveAt(stack.Count - 1);
				if (r == 0) return -1;
				stack.Add(l % r);
				continue;
			}

			if (code == Code.Dup) {
				if (stack.Count < 1) return -1;
				stack.Add(stack[stack.Count - 1]);
				continue;
			}

			if (code == Code.Conv_I4 || code == Code.Conv_U4)
				continue;
			if (code == Code.Nop)
				continue;
			if (code == Code.Pop) {
				if (stack.Count < 1) return -1;
				stack.RemoveAt(stack.Count - 1);
				continue;
			}

			if (code == Code.Switch) {
				if (stack.Count < 1) return -1;
				return (int)stack[stack.Count - 1];
			}

			return -1;
		}

		return -1;
	}
}
