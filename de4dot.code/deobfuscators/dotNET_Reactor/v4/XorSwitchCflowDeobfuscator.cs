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

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4 {
	/// <summary>
	/// Deobfuscates XOR-switch state machines produced by .NET Reactor v6.x.
	///
	/// The dispatch pattern is:
	///   [ldc.i4 XOR_KEY, xor, [dup, stloc dispatch_var,] ldc.i4 MODULUS, rem.un, switch]
	/// with the state value arriving on the stack from source blocks.
	///
	/// Source blocks either push a constant (ldc.i4 CONST) or compute a multiply-XOR
	/// transition (ldloc dispatch_var; ldc.i4 MUL; mul; ldc.i4 XOR2; xor).
	/// </summary>
	class XorSwitchCflowDeobfuscator : IBlocksDeobfuscator {
		Blocks blocks;
		IList<Local> locals;
		List<Block> allBlocks;

		public bool ExecuteIfNotModified { get; }

		public void DeobfuscateBegin(Blocks blocks) {
			this.blocks = blocks;
			locals = blocks.Locals;
		}

		public bool Deobfuscate(List<Block> allBlocks) {
			this.allBlocks = allBlocks;
			bool modified = false;
			foreach (var block in allBlocks) {
				if (block.LastInstr.OpCode.Code != Code.Switch)
					continue;
				if (TryDeobfuscateDispatch(block))
					modified = true;
			}
			return modified;
		}

		bool TryDeobfuscateDispatch(Block switchBlock) {
			if (!TryExtractDispatchInfo(switchBlock, out var info))
				return false;
			if (switchBlock.Targets == null || switchBlock.Targets.Count == 0)
				return false;

			bool modified = false;

			// Collect dispatch values from constant sources BEFORE rewriting them,
			// because RewriteConstantSources removes them from switchBlock.Sources.
			var caseToDispatchVals = CollectAllDispatchVals(switchBlock, info);

			// Rewrite sources that push a constant state onto the stack
			modified |= RewriteConstantSources(switchBlock, info);

			// Rewrite multiply-XOR sources (uses pre-collected dispatch vals)
			modified |= RewriteMultiplyXorSources(switchBlock, info, caseToDispatchVals);

			return modified;
		}

		struct DispatchInfo {
			public Local DispatchVar;   // may be null if no dup+stloc
			public Local StateVar;      // may be null if state arrives on stack (not from local)
			public uint XorKey;
			public uint Modulus;
			public uint EmbeddedMul;    // multiply constant embedded in the dispatch block
			public bool HasEmbeddedMul; // true if dispatch block contains multiply-XOR before dispatch
		}

		bool TryExtractDispatchInfo(Block switchBlock, out DispatchInfo info) {
			info = default;
			var instrs = switchBlock.Instructions;
			int switchIdx = instrs.Count - 1;

			// Minimum: ldc.i4 XOR_KEY, xor, ldc.i4 MODULUS, rem.un, switch = 5
			if (switchIdx < 4)
				return false;

			int idx = switchIdx - 1;

			// rem.un
			if (instrs[idx].OpCode.Code != Code.Rem_Un)
				return false;
			idx--;

			// ldc.i4 MODULUS
			if (!instrs[idx].IsLdcI4())
				return false;
			uint modulus = (uint)instrs[idx].GetLdcI4Value();
			if (modulus == 0)
				return false;
			idx--;

			// Optional: stloc dispatch_var + dup
			Local dispatchVar = null;
			if (idx >= 1 && instrs[idx].IsStloc()) {
				dispatchVar = Instr.GetLocalVar(locals, instrs[idx]);
				idx--;
				if (instrs[idx].OpCode.Code != Code.Dup)
					return false;
				idx--;
			}

			if (idx < 1)
				return false;

			// xor
			if (instrs[idx].OpCode.Code != Code.Xor)
				return false;
			idx--;

			// ldc.i4 XOR_KEY
			if (!instrs[idx].IsLdcI4())
				return false;
			uint xorKey = (uint)instrs[idx].GetLdcI4Value();

			// Determine how the state value arrives:
			// 1. idx == 0: state arrives on stack from predecessor block
			// 2. instrs[idx-1] is ldloc: state loaded from a local variable
			// 3. Multiply-XOR embedded in dispatch: ldloc V; ldc.i4 MUL; mul; ldc.i4 XOR2; xor; ldc.i4 XOR_KEY; xor; ...
			//    In this case, we fold the two XOR constants: effective_XOR_KEY = XOR2 ^ XOR_KEY
			// 4. Otherwise: reject
			Local stateVar = null;
			if (idx == 0) {
				// State arrives on stack — original pattern
			}
			else if (idx >= 1 && instrs[idx - 1].IsLdloc()) {
				stateVar = Instr.GetLocalVar(locals, instrs[idx - 1]);
			}
			else if (idx >= 5 && instrs[idx - 1].OpCode.Code == Code.Xor
			         && instrs[idx - 2].IsLdcI4()
			         && instrs[idx - 3].OpCode.Code == Code.Mul
			         && instrs[idx - 4].IsLdcI4()
			         && instrs[idx - 5].IsLdloc()) {
				// Multiply-XOR embedded in dispatch block:
				// ldloc V; ldc.i4 MUL; mul; ldc.i4 XOR2; xor; ldc.i4 XOR_KEY; xor; ...
				// Fold: effective XOR_KEY = XOR2 ^ XOR_KEY
				uint xor2 = (uint)instrs[idx - 2].GetLdcI4Value();
				xorKey = unchecked(xor2 ^ xorKey);
				stateVar = Instr.GetLocalVar(locals, instrs[idx - 5]);

				info = new DispatchInfo {
					DispatchVar = dispatchVar,
					XorKey = xorKey,
					Modulus = modulus,
					StateVar = stateVar,
					EmbeddedMul = (uint)instrs[idx - 4].GetLdcI4Value(),
					HasEmbeddedMul = true,
				};
				return true;
			}
			else {
				return false;
			}

			info = new DispatchInfo {
				DispatchVar = dispatchVar,
				XorKey = xorKey,
				Modulus = modulus,
				StateVar = stateVar,
			};
			return true;
		}

		Block GetCaseBlock(Block switchBlock, int caseIndex) {
			if (switchBlock.Targets == null)
				return null;
			if (caseIndex < 0 || caseIndex >= switchBlock.Targets.Count)
				return switchBlock.FallThrough;
			return switchBlock.Targets[caseIndex];
		}

		bool RewriteConstantSources(Block switchBlock, DispatchInfo info) {
			bool modified = false;

			foreach (var source in new List<Block>(switchBlock.Sources)) {
				if (source == switchBlock)
					continue;

				var instrs = source.Instructions;
				if (instrs.Count == 0)
					continue;

				int constIdx = FindConstantForDispatch(instrs, info);
				if (constIdx < 0)
					continue;

				uint stateVal = (uint)instrs[constIdx].GetLdcI4Value();
				uint dispatchVal;
				if (info.HasEmbeddedMul)
					dispatchVal = unchecked(stateVal * info.EmbeddedMul ^ info.XorKey);
				else
					dispatchVal = unchecked(stateVal ^ info.XorKey);
				int caseIdx = (int)(dispatchVal % info.Modulus);

				var targetBlock = GetCaseBlock(switchBlock, caseIdx);
				if (targetBlock == null)
					continue;

				int numToRemove = instrs.Count - constIdx;
				if (numToRemove <= 0 || numToRemove > instrs.Count)
					continue;

				source.ReplaceLastInstrsWithBranch(numToRemove, targetBlock);
				modified = true;
			}

			return modified;
		}

		/// <summary>
		/// Finds a constant that feeds the dispatch, handling both stack-based and
		/// local-variable-based state patterns.
		/// </summary>
		int FindConstantForDispatch(List<Instr> instrs, DispatchInfo info) {
			if (info.StateVar != null)
				return FindLocalStoreConstant(instrs, info.StateVar);
			return FindStackTopConstant(instrs);
		}

		/// <summary>
		/// Find a ldc.i4 + stloc pattern where the value is stored to the given local.
		/// Returns the index of the ldc.i4 instruction, or -1 if not found.
		/// </summary>
		int FindLocalStoreConstant(List<Instr> instrs, Local stateVar) {
			for (int i = instrs.Count - 1; i >= 1; i--) {
				if (!instrs[i].IsStloc())
					continue;
				var local = Instr.GetLocalVar(locals, instrs[i]);
				if (local != stateVar)
					continue;
				if (instrs[i - 1].IsLdcI4())
					return i - 1;
			}
			return -1;
		}

		/// <summary>
		/// Collect dispatch vals from multiple sources:
		/// 1. Direct constant sources of the dispatch block
		/// 2. Constants in blocks reachable from case blocks that flow to dispatch
		/// 3. Propagation through multiply-XOR chains
		/// </summary>
		Dictionary<int, HashSet<uint>> CollectAllDispatchVals(Block switchBlock, DispatchInfo info) {
			var caseToDispatchVals = new Dictionary<int, HashSet<uint>>();

			// 1. Direct constant sources
			foreach (var source in switchBlock.Sources) {
				if (source == switchBlock)
					continue;
				int constIdx = FindConstantForDispatch(source.Instructions, info);
				if (constIdx < 0)
					continue;
				uint stateVal = (uint)source.Instructions[constIdx].GetLdcI4Value();
				AddDispatchVal(caseToDispatchVals, info, stateVal);
			}

			// 2. Search ALL blocks for constants that flow toward the dispatch
			foreach (var block in allBlocks) {
				if (block == switchBlock)
					continue;
				if (!BlockReachesDispatch(block, switchBlock, 3))
					continue;
				int ci = FindConstantForDispatch(block.Instructions, info);
				if (ci >= 0) {
					uint sv = (uint)block.Instructions[ci].GetLdcI4Value();
					AddDispatchVal(caseToDispatchVals, info, sv);
				}
			}

			// 3. Build blockToCase map (needed for propagation)
			var blockToCase = BuildBlockToCase(switchBlock);

			// 4. Propagate multiply-XOR to discover more dispatch_vals
			PropagateMultiplyXor(switchBlock, info, caseToDispatchVals, blockToCase);

			return caseToDispatchVals;
		}

		void AddDispatchVal(Dictionary<int, HashSet<uint>> caseToDispatchVals, DispatchInfo info, uint stateVal) {
			uint dv;
			if (info.HasEmbeddedMul)
				dv = unchecked(stateVal * info.EmbeddedMul ^ info.XorKey);
			else
				dv = unchecked(stateVal ^ info.XorKey);
			int ci = (int)(dv % info.Modulus);
			if (!caseToDispatchVals.TryGetValue(ci, out var set))
				caseToDispatchVals[ci] = set = new HashSet<uint>();
			set.Add(dv);
		}

		bool BlockReachesDispatch(Block block, Block switchBlock, int maxHops) {
			var current = block;
			for (int i = 0; i < maxHops; i++) {
				if (current.FallThrough == switchBlock)
					return true;
				if (current.Targets != null) {
					foreach (var t in current.Targets) {
						if (t == switchBlock)
							return true;
					}
				}
				if (current.FallThrough == null || current.FallThrough == current)
					break;
				current = current.FallThrough;
			}
			return false;
		}

		Dictionary<Block, int> BuildBlockToCase(Block switchBlock) {
			var blockToCase = new Dictionary<Block, int>();
			var ambiguousBlocks = new HashSet<Block>();
			if (switchBlock.Targets == null)
				return blockToCase;

			for (int i = 0; i < switchBlock.Targets.Count; i++) {
				var caseBlock = switchBlock.Targets[i];
				if (caseBlock == null)
					continue;

				var visited = new HashSet<Block> { switchBlock };
				visited.Add(caseBlock);
				var worklist = new Queue<Block>();
				worklist.Enqueue(caseBlock);

				while (worklist.Count > 0) {
					var block = worklist.Dequeue();

					if (ambiguousBlocks.Contains(block))
						continue;
					if (blockToCase.TryGetValue(block, out int existingCase)) {
						if (existingCase != i) {
							ambiguousBlocks.Add(block);
							blockToCase.Remove(block);
						}
					}
					else {
						blockToCase[block] = i;
					}

					foreach (var succ in block.GetTargets()) {
						if (succ != null && visited.Add(succ))
							worklist.Enqueue(succ);
					}
				}
			}
			return blockToCase;
		}

		bool RewriteMultiplyXorSources(Block switchBlock, DispatchInfo info,
			Dictionary<int, HashSet<uint>> caseToDispatchVals) {
			if (info.DispatchVar == null)
				return false;
			if (switchBlock.Targets == null)
				return false;

			bool modified = false;

			var blockToCase = BuildBlockToCase(switchBlock);

			foreach (var source in new List<Block>(switchBlock.Sources)) {
				if (source == switchBlock)
					continue;

				if (!TryGetMultiplyXorPattern(source, info, out uint mulConst, out uint xor2Const, out int patternLen))
					continue;

				if (!blockToCase.TryGetValue(source, out int ownerCase))
					continue;

				if (!caseToDispatchVals.TryGetValue(ownerCase, out var dispatchVals))
					continue;

				// Try all dispatch vals — if they all produce the same target, we can resolve
				int? resolvedCaseIdx = null;
				bool allSame = true;
				foreach (var dispatchVal in dispatchVals) {
					uint newState = unchecked((uint)(dispatchVal * mulConst) ^ xor2Const);
					uint newDispatchVal = unchecked(newState ^ info.XorKey);
					int targetCaseIdx = (int)(newDispatchVal % info.Modulus);
					if (resolvedCaseIdx == null)
						resolvedCaseIdx = targetCaseIdx;
					else if (resolvedCaseIdx.Value != targetCaseIdx) {
						allSame = false;
						break;
					}
				}

				if (!allSame || resolvedCaseIdx == null)
					continue;

				var targetBlock = GetCaseBlock(switchBlock, resolvedCaseIdx.Value);
				if (targetBlock == null)
					continue;

				if (patternLen <= 0 || patternLen > source.Instructions.Count)
					continue;

				source.ReplaceLastInstrsWithBranch(patternLen, targetBlock);
				modified = true;
			}

			return modified;
		}

		void PropagateMultiplyXor(Block switchBlock, DispatchInfo info,
			Dictionary<int, HashSet<uint>> caseToDispatchVals, Dictionary<Block, int> blockToCase) {

			if (switchBlock.Targets == null)
				return;

			bool changed = true;
			int maxIter = 100;
			while (changed && maxIter-- > 0) {
				changed = false;

				foreach (var source in switchBlock.Sources) {
					if (source == switchBlock)
						continue;

					if (!TryGetMultiplyXorPattern(source, info, out uint mulConst, out uint xor2Const, out _))
						continue;

					if (!blockToCase.TryGetValue(source, out int ownerCase))
						continue;

					if (!caseToDispatchVals.TryGetValue(ownerCase, out var dispatchVals))
						continue;

					foreach (var dispatchVal in new List<uint>(dispatchVals)) {
						uint newState = unchecked((uint)(dispatchVal * mulConst) ^ xor2Const);
						uint newDv = unchecked(newState ^ info.XorKey);
						int newCase = (int)(newDv % info.Modulus);

						if (!caseToDispatchVals.TryGetValue(newCase, out var newSet)) {
							caseToDispatchVals[newCase] = newSet = new HashSet<uint>();
						}
						if (newSet.Add(newDv))
							changed = true;
					}
				}
			}
		}

		/// <summary>
		/// Find the index of a ldc.i4 instruction whose value ends up on top of
		/// the stack when the block exits (falls through to the dispatch).
		/// Handles patterns:
		///   1. [..., ldc.i4 CONST]  (direct push)
		///   2. [..., ldc.i4 CONST, stloc V, ldloc V] (push via local)
		///   3. [..., ldc.i4 CONST, stloc V] where V is later loaded in dispatch
		/// </summary>
		int FindStackTopConstant(List<Instr> instrs) {
			if (instrs.Count == 0)
				return -1;

			int lastIdx = instrs.Count - 1;

			// Case 1: last instruction is ldc.i4
			if (instrs[lastIdx].IsLdcI4())
				return lastIdx;

			// Case 2: stloc V; ldloc V where ldloc is last
			if (lastIdx >= 1 && instrs[lastIdx].IsLdloc() && instrs[lastIdx - 1].IsStloc()) {
				var stLocal = Instr.GetLocalVar(locals, instrs[lastIdx - 1]);
				var ldLocal = Instr.GetLocalVar(locals, instrs[lastIdx]);
				if (stLocal != null && stLocal == ldLocal && lastIdx >= 2 && instrs[lastIdx - 2].IsLdcI4())
					return lastIdx - 2;
			}

			// Case 3: last instruction is stloc, preceded by ldc.i4
			if (lastIdx >= 1 && instrs[lastIdx].IsStloc() && instrs[lastIdx - 1].IsLdcI4())
				return lastIdx - 1;

			return -1;
		}

		bool TryGetMultiplyXorPattern(Block block, DispatchInfo info,
			out uint mulConst, out uint xor2Const, out int patternLen) {

			mulConst = 0;
			xor2Const = 0;
			patternLen = 0;
			var instrs = block.Instructions;

			// Pattern A (stack-based): ldloc dispatch_var; ldc.i4 MUL; mul; ldc.i4 XOR2; xor
			// Pattern B (local-based): ldloc dispatch_var; ldc.i4 MUL; mul; ldc.i4 XOR2; xor; stloc state_var
			if (instrs.Count < 5)
				return false;

			for (int end = instrs.Count - 1; end >= 4; end--) {
				int i = end;

				// Optional trailing stloc state_var (local-based pattern)
				if (info.StateVar != null && instrs[i].IsStloc()) {
					var storeVar = Instr.GetLocalVar(locals, instrs[i]);
					if (storeVar == info.StateVar)
						i--;
				}

				if (instrs[i].OpCode.Code != Code.Xor)
					continue;
				i--;

				if (!instrs[i].IsLdcI4())
					continue;
				xor2Const = (uint)instrs[i].GetLdcI4Value();
				i--;

				if (instrs[i].OpCode.Code != Code.Mul)
					continue;
				i--;

				if (!instrs[i].IsLdcI4())
					continue;
				mulConst = (uint)instrs[i].GetLdcI4Value();
				i--;

				if (!instrs[i].IsLdloc())
					continue;
				var loadedVar = Instr.GetLocalVar(locals, instrs[i]);
				if (loadedVar == null)
					continue;
				if (info.DispatchVar != null && loadedVar != info.DispatchVar)
					continue;

				patternLen = instrs.Count - i;
				return true;
			}
			return false;
		}
	}
}
