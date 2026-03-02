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

struct DispatchNode {
	public Block SwitchBlock;
	public Local StateVar;
	public IList<Block> CaseTargets;
	public Dictionary<Block, int> BlockToCase;
}

/// <summary>
///     Detects whether a switch block is a flattened dispatch using abstract interpretation.
/// </summary>
static class DispatchDetector {
	const int MaxBfsBlocks = 5000;

	public static DispatchNode? TryDetect(Block switchBlock, Blocks blocks) {
		if (switchBlock.Targets == null || switchBlock.Targets.Count < 2)
			return null;

		var stateVar = FindStateVar(switchBlock, blocks);
		// stateVar may be null for stack-based state

		// Validate: emulate with a probe value and check that we get a definite case index
		if (!ValidateDispatch(switchBlock, stateVar, blocks))
			return null;

		var blockToCase = BuildBlockToCase(switchBlock);

		// Heuristic gate: require that at least some predecessors are case targets,
		// indicating a state machine (cycle exists) rather than a legitimate switch
		if (!HasCyclicPredecessors(switchBlock, blockToCase))
			return null;

		return new DispatchNode {
			SwitchBlock = switchBlock,
			StateVar = stateVar,
			CaseTargets = switchBlock.Targets,
			BlockToCase = blockToCase,
		};
	}

	/// <summary>
	///     Finds the state variable by looking for stloc in the switch block (the local that
	///     stores the XOR result). Also handles the case where a local is loaded as input.
	/// </summary>
	static Local FindStateVar(Block switchBlock, Blocks blocks) {
		var instrs = switchBlock.Instructions;

		// Strategy 1: Look for stloc in the switch block — in the pattern
		// ldc.i4 K; xor; dup; stloc.N; ldc.i4 M; rem.un; switch
		// the stloc.N local is the state variable
		foreach (var instr in instrs) {
			if (instr.IsStloc()) {
				var local = instr.Instruction.GetLocal(blocks.Locals);
				if (local != null)
					return local;
			}
		}

		// Strategy 2: For each local L, emulate the switch block with L set to a known
		// probe value. If the top of stack is AllBitsValid, L is the state var.
		const int probeValue = 0x12345678;
		var method = blocks.Method;
		foreach (var local in blocks.Locals) {
			var emu = new InstructionEmulator();
			emu.Initialize(method, false);
			emu.SetLocal(local, new Int32Value(probeValue));

			try {
				emu.Emulate(instrs, 0, instrs.Count - 1);
			}
			catch {
				continue;
			}

			if (emu.StackSize() < 1)
				continue;

			var tos = emu.Pop();
			if (tos is Int32Value iv && iv.AllBitsValid())
				return local;
		}

		return null;
	}

	/// <summary>
	///     Determines the number of stack values the switch block expects at entry.
	/// </summary>
	static int ComputeStackInput(Block switchBlock) {
		// Walk the instructions and track the minimum stack depth
		int depth = 0;
		int minDepth = 0;
		var instrs = switchBlock.Instructions;
		for (int i = 0; i < instrs.Count - 1; i++) { // exclude the switch itself
			var instr = instrs[i].Instruction;
			instr.CalculateStackUsage(out int pushes, out int pops);
			depth -= pops;
			if (depth < minDepth)
				minDepth = depth;
			depth += pushes;
		}
		return -minDepth; // how many items must be pre-pushed
	}

	/// <summary>
	///     Emulate the switch block with probe values and verify that TOS
	///     produces a known (AllBitsValid) switch index.
	/// </summary>
	static bool ValidateDispatch(Block switchBlock, Local stateVar, Blocks blocks) {
		var method = blocks.Method;
		var instrs = switchBlock.Instructions;
		var emu = new InstructionEmulator();
		emu.Initialize(method, false);

		if (stateVar != null)
			emu.SetLocal(stateVar, new Int32Value(0));

		// Push probe values for any stack inputs the switch block expects
		int stackInputs = ComputeStackInput(switchBlock);
		for (int i = 0; i < stackInputs; i++)
			emu.Push(new Int32Value(0));

		try {
			emu.Emulate(instrs, 0, instrs.Count - 1);
		}
		catch {
			return false;
		}

		if (emu.StackSize() < 1)
			return false;

		var tos = emu.Pop();
		return tos is Int32Value iv && iv.AllBitsValid();
	}

	/// <summary>
	///     BFS from each case target, mapping reachable blocks to their case index.
	///     Blocks reachable from multiple case indices are excluded (ambiguous).
	/// </summary>
	static Dictionary<Block, int> BuildBlockToCase(Block switchBlock) {
		var result = new Dictionary<Block, int>();
		var ambiguous = new HashSet<Block>();
		var targets = switchBlock.Targets;

		for (int caseIdx = 0; caseIdx < targets.Count; caseIdx++) {
			var queue = new Queue<Block>();
			var visited = new HashSet<Block>();
			queue.Enqueue(targets[caseIdx]);
			visited.Add(targets[caseIdx]);
			int count = 0;

			while (queue.Count > 0 && count < MaxBfsBlocks) {
				var block = queue.Dequeue();
				count++;

				if (block == switchBlock)
					continue;

				if (ambiguous.Contains(block))
					continue;

				if (result.TryGetValue(block, out int existingCase)) {
					if (existingCase != caseIdx) {
						result.Remove(block);
						ambiguous.Add(block);
					}
					continue;
				}

				result[block] = caseIdx;

				foreach (var succ in block.GetTargets()) {
					if (visited.Add(succ))
						queue.Enqueue(succ);
				}
			}
		}

		return result;
	}

	/// <summary>
	///     Check that at least one predecessor of the switch block is also a case target
	///     or owned by a case, indicating a state machine cycle.
	/// </summary>
	static bool HasCyclicPredecessors(Block switchBlock, Dictionary<Block, int> blockToCase) {
		foreach (var source in switchBlock.Sources) {
			if (blockToCase.ContainsKey(source))
				return true;
		}
		// Also check if any case target directly feeds back to the switch
		if (switchBlock.Targets != null) {
			foreach (var target in switchBlock.Targets) {
				foreach (var succ in target.GetTargets()) {
					if (succ == switchBlock)
						return true;
				}
			}
		}
		return false;
	}
}
