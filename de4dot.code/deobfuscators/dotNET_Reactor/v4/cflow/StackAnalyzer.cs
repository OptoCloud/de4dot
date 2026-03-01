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

/// <summary>
///     Computes exact stack depths per instruction using dnlib's UpdateStack.
///     Replaces the heuristic NeedStackCleanup / pop;pop pattern with precise
///     depth computation for correct stack cleanup during rewrites.
/// </summary>
static class StackAnalyzer {
	/// <summary>
	///     Returns stack depth BEFORE each instruction, plus one entry for depth
	///     after the last instruction. Returns null if the stack underflows
	///     (malformed IL).
	///     Uses the same Instruction.UpdateStack API as ForwardScanOrder.
	/// </summary>
	internal static int[] ComputeDepths(List<Instr> instructions, int entryDepth = 0) {
		int[] depths = new int[instructions.Count + 1];
		int stack = entryDepth;

		for (int i = 0; i < instructions.Count; i++) {
			if (stack < 0)
				return null;
			depths[i] = stack;
			instructions[i].Instruction.UpdateStack(ref stack, false);
		}

		if (stack < 0)
			return null;
		depths[instructions.Count] = stack;
		return depths;
	}

	/// <summary>
	///     Returns the stack depth BEFORE the instruction at the given index,
	///     or -1 on failure (underflow or out-of-range index).
	/// </summary>
	internal static int DepthAt(List<Instr> instructions, int index, int entryDepth = 0) {
		if (index < 0 || index > instructions.Count)
			return -1;

		int[] depths = ComputeDepths(instructions, entryDepth);
		if (depths == null)
			return -1;

		return depths[index];
	}
}
