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
using de4dot.code;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4 {
	/// <summary>
	/// Deobfuscates XOR-switch state machines produced by .NET Reactor v6.x.
	///
	/// ## Value domains
	///
	/// Four distinct 32-bit unsigned integer domains exist in the dispatch:
	///
	/// - **state**: the raw value stored by case blocks via
	///   ldc.i4 CONST; stloc OriginalStateVar (or StateVar if no OriginalStateVar).
	///   Converted to stateVar domain via StateValToStateVarInput() before dispatch.
	///
	/// - **stateVar**: the value held in info.StateVar at dispatch time
	///   (= what the dispatch block's ldloc loads). For embedded-mul with
	///   OriginalStateVar, stateVar = state ^ OriginalXorKey. Otherwise = state.
	///
	/// - **dispatchVal**: the value computed by the dispatch block.
	///   For standard dispatch: dispatchVal = stateVar ^ XorKey.
	///   For embedded-mul: dispatchVal = stateVar * EmbeddedMul ^ XorKey.
	///
	/// - **caseIndex**: dispatchVal % Modulus — indexes into the switch targets.
	///
	/// All conversions between domains go through the centralized helpers
	/// StateToDispatchVal, MulXorToNextState, SelfLoopNext, NormalizeCaseIndex.
	///
	/// ## Embedded-mul
	///
	/// When de4dot's block merging folds a multiply-XOR transition into the
	/// dispatch block, the dispatch becomes:
	///   ldloc V; ldc.i4 MUL; mul; ldc.i4 XOR2; xor; ldc.i4 XOR_KEY; xor;
	///   [dup; stloc;] ldc.i4 MOD; rem.un; switch
	/// Here XOR2 and XOR_KEY are folded into a single effective XorKey.
	/// The OriginalXorKey (= XOR_KEY before folding) and EmbeddedMul are
	/// saved so that state→dispatchVal conversion can reverse the fold.
	///
	/// ## Safety rules
	///
	/// - A source is only rewritten when its target can be **proven** correct:
	///   all dispatch vals for its owning case must resolve to the same target.
	/// - If domain conversion is ambiguous, the source is skipped (fail closed).
	/// - Instruction removal uses **backward slicing** (D) to identify the exact
	///   instruction range; only trailing nop/br may be additionally removed.
	/// - Before every rewrite, VerifyAndGetTarget (F) checks: modulus matches
	///   switch target count, case index is in bounds, target block exists.
	/// - A property-based self-check independently re-simulates the dispatch
	///   block's IL with a concrete uint stack.  If the simulated case index
	///   disagrees with the computed one, the rewrite is skipped.
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
			int totalDispatches = 0, embeddedMulDispatches = 0, rewrittenDispatches = 0;
			foreach (var block in allBlocks) {
				if (block.LastInstr.OpCode.Code != Code.Switch)
					continue;
				if (TryExtractDispatchInfo(block, out var probe)) {
					totalDispatches++;
					if (probe.HasEmbeddedMul)
						embeddedMulDispatches++;
				}
				if (TryDeobfuscateDispatch(block)) {
					modified = true;
					rewrittenDispatches++;
				}
			}
			if (totalDispatches > 0)
				Logger.v("  XOR-switch: {0} dispatches ({1} embedded-mul), {2} rewritten",
					totalDispatches, embeddedMulDispatches, rewrittenDispatches);
			return modified;
		}

		bool TryDeobfuscateDispatch(Block switchBlock) {
			if (!TryExtractDispatchInfo(switchBlock, out var info))
				return false;
			if (switchBlock.Targets == null || switchBlock.Targets.Count == 0)
				return false;

			// Safety (F): modulus must equal the number of switch targets.
			// If not, the arithmetic would produce out-of-bounds case indices.
			if (info.Modulus != (uint)switchBlock.Targets.Count)
				return false;

			// Internal constant dispatch: the dispatch block has a merged dead-code
			// prefix that always produces the same state value, making the switch
			// always go to the same case. Simplify by replacing the entire dispatch.
			if (info.InternalStateVarInput.HasValue) {
				if (RewriteInternalConstantDispatch(switchBlock, info))
					return true;
			}

			// Precompute shared data structures once per dispatch to avoid
			// redundant O(N+E) BFS traversals in each consumer method.
			var blockToCase = BuildBlockToCase(switchBlock);
			var reverseReachable = ComputeReverseReachable(switchBlock);

			// For embedded-mul dispatches, find the original state variable that
			// case blocks write to (different from StateVar after block merging).
			if (info.HasEmbeddedMul)
				info.OriginalStateVar = FindOriginalStateVar(switchBlock, info, blockToCase);

			bool modified = false;

			// Collect dispatch values from constant sources BEFORE rewriting them,
			// because RewriteConstantSources disconnects sources from switchBlock.
			var caseToDispatchVals = CollectAllDispatchVals(switchBlock, info, reverseReachable, blockToCase);

			// Self-loop logic only applies when we can prove the mul input local
			// is truly the "previous dispatch value" — i.e., the dup+stloc in
			// the dispatch stores into the same local that the embedded-mul loads.
			// Without this evidence, SelfLoopNext() assumptions don't hold and
			// seeded dispatch vals could pollute caseToDispatchVals.
			bool selfLoopEligible = info.HasEmbeddedMul
				&& info.DispatchVar != null
				&& info.StateVar == info.DispatchVar;

			// For pure self-loop embedded-mul dispatches (case blocks don't set state),
			// seed dispatch vals by iterating from the initial StateVar value.
			if (selfLoopEligible && caseToDispatchVals.Count == 0)
				SeedSelfLoopDispatchVals(switchBlock, info, caseToDispatchVals, reverseReachable);

			modified |= RewriteConstantSources(switchBlock, info);
			modified |= RewriteMultiplyXorSources(switchBlock, info, caseToDispatchVals, blockToCase);
			if (selfLoopEligible)
				modified |= RewriteSelfLoopSources(switchBlock, info, caseToDispatchVals, blockToCase);
			modified |= RemoveDeadSwitchCases(switchBlock, info, caseToDispatchVals);

			return modified;
		}

		// ────────────────────────────────────────────────────────────────────
		//  Domain conversion helpers (C)
		//
		//  All arithmetic uses unchecked 32-bit operations matching the
		//  obfuscator's runtime behavior. Each helper documents which domain
		//  its input and output belong to.
		// ────────────────────────────────────────────────────────────────────

		/// <summary>
		/// Converts a StateVar-domain value to a dispatch value.
		/// Input:  STATEVAR domain (the value held in info.StateVar at dispatch time).
		///         For STATE-domain inputs (e.g., from FindConstantForDispatch),
		///         callers must first convert via StateValToStateVarInput().
		/// Output: DISPATCH-VAL domain (the value used before modulus).
		///
		/// Standard:     dispatchVal = stateVarValue ^ XorKey
		/// EmbeddedMul:  dispatchVal = stateVarValue * EmbeddedMul ^ XorKey
		/// </summary>
		static uint StateToDispatchVal(DispatchInfo info, uint stateVarValue) {
			if (info.HasEmbeddedMul)
				return unchecked(stateVarValue * info.EmbeddedMul ^ info.XorKey);
			return unchecked(stateVarValue ^ info.XorKey);
		}

		/// <summary>
		/// Computes the next state from a multiply-XOR transition.
		/// Input:  DISPATCH-VAL domain (current dispatch value).
		/// Output: STATE domain (needs StateToDispatchVal to become a dispatch val).
		///   nextState = (dispatchVal * mulConst) ^ xor2Const
		/// </summary>
		static uint MulXorToNextState(uint dispatchVal, uint mulConst, uint xor2Const) {
			return unchecked((uint)(dispatchVal * mulConst) ^ xor2Const);
		}

		/// <summary>
		/// Computes the next dispatch val for self-loop embedded-mul dispatches
		/// where the dispatch block itself is the transition (no case-block state store).
		/// Input:  DISPATCH-VAL domain.
		/// Output: DISPATCH-VAL domain.
		///   nextDispatchVal = currentDispatchVal * EmbeddedMul ^ XorKey
		/// </summary>
		static uint SelfLoopNext(DispatchInfo info, uint currentDispatchVal) {
			return unchecked(currentDispatchVal * info.EmbeddedMul ^ info.XorKey);
		}

		/// <summary>
		/// Converts a dispatch value to a case index via modulus.
		/// Input:  DISPATCH-VAL domain.
		/// Output: CASE-INDEX domain (0 ≤ result &lt; Modulus).
		/// </summary>
		static int NormalizeCaseIndex(DispatchInfo info, uint dispatchVal) {
			return (int)(dispatchVal % info.Modulus);
		}

		// ────────────────────────────────────────────────────────────────────
		//  Dispatch extraction
		// ────────────────────────────────────────────────────────────────────

		/// <summary>
		/// Extracted constants and locals from a dispatch block.
		///
		/// Standard:     [ldloc state] ldc.i4 XOR_KEY; xor; [dup; stloc dispatch_var;] ldc.i4 MOD; rem.un; switch
		/// Embedded-mul: ldloc V; ldc.i4 MUL; mul; ldc.i4 XOR2; xor; ldc.i4 XOR_KEY; xor; [dup; stloc;] ldc.i4 MOD; rem.un; switch
		///
		/// For embedded-mul, XOR2 and XOR_KEY are folded into XorKey = XOR2 ^ XOR_KEY.
		/// OriginalXorKey preserves the pre-fold XOR_KEY for state→dispatch conversion.
		/// </summary>
		struct DispatchInfo {
			public Local DispatchVar;      // local stored via dup+stloc after XOR (null if absent)
			public Local StateVar;         // local loaded at start of dispatch (null if state arrives on stack)
			public uint XorKey;            // XOR key (or folded XOR2^XOR_KEY for embedded-mul)
			public uint Modulus;           // switch case count (dispatch_val % Modulus)
			public uint EmbeddedMul;       // multiply constant when dispatch has embedded mul-xor
			public bool HasEmbeddedMul;    // true when a multiply-XOR transition was merged into dispatch
			public Local OriginalStateVar; // the var case blocks write to (null if not embedded-mul or not found)
			public uint OriginalXorKey;    // dispatch XOR_KEY before folding with XOR2 (0 if not embedded-mul)
			public uint? InternalStateVarInput; // STATEVAR-domain; non-null when dispatch has merged dead-code prefix
		}

		/// <summary>
		/// Scans backwards from the switch instruction to extract the dispatch pattern.
		/// Recognizes three variants:
		///   1. Stack-based: state pushed by predecessor, idx==0
		///   2. Local-based: ldloc stateVar before XOR_KEY
		///   3. Embedded multiply-XOR: ldloc V; mul; xor; before the XOR_KEY; xor;
		///      (created when block merging folds a multiply-XOR transition into dispatch)
		/// </summary>
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

			// Determine how the state value arrives
			Local stateVar = null;
			uint? internalStateVarInput = null;
			if (idx == 0) {
				// State arrives on stack — original pattern
			}
			else if (idx >= 1 && instrs[idx - 1].IsLdloc()) {
				stateVar = Instr.GetLocalVar(locals, instrs[idx - 1]);
			}
			else if (TryExtractEmbeddedMul(instrs, idx, xorKey, dispatchVar, modulus, out info)) {
				return true;
			}
			else {
				// Fallback: state may arrive on stack via earlier instructions
				// (common after MergeBlocks absorbs a dead-code predecessor
				// with the ldc.i4 X; ldc.i4 X; pop dead-code pattern).
				var stackVal = SliceBackward(instrs, idx - 1);
				if (stackVal == null)
					return false;
				// Only accept as internal constant if the resolved expression starts at or near
				// the beginning of the block (merged dead-code prefix). This prevents
				// classifying a "computed constant late in block" as "dispatch ignores sources".
				if (stackVal.Value.startIdx > 2)
					return false;
				stateVar = null;
				internalStateVarInput = stackVal.Value.value;
			}

			info = new DispatchInfo {
				DispatchVar = dispatchVar,
				XorKey = xorKey,
				Modulus = modulus,
				StateVar = stateVar,
				InternalStateVarInput = internalStateVarInput,
			};
			return true;
		}

	/// <summary>
		/// Extracts embedded multiply-XOR from dispatch, tolerating conv.i4/u4/nop
		/// between the core operations: ldloc V; [conv*;] ldc.i4 MUL; mul; [conv*;]
		/// ldc.i4 XOR2; xor. Scans backward from 'idx' (the position of ldc.i4 XOR_KEY).
		/// </summary>
		bool TryExtractEmbeddedMul(List<Instr> instrs, int idx, uint xorKey,
			Local dispatchVar, uint modulus, out DispatchInfo info) {
			info = default;

			int i = idx - 1;
			// Skip harmless ops before we expect 'xor'
			while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
			if (i < 0 || instrs[i].OpCode.Code != Code.Xor)
				return false;
			i--;

			// ldc.i4 XOR2
			while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
			if (i < 0 || !instrs[i].IsLdcI4())
				return false;
			uint xor2 = (uint)instrs[i].GetLdcI4Value();
			i--;

			// mul
			while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
			if (i < 0 || instrs[i].OpCode.Code != Code.Mul)
				return false;
			i--;

			// ldc.i4 MUL
			while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
			if (i < 0 || !instrs[i].IsLdcI4())
				return false;
			uint embeddedMul = (uint)instrs[i].GetLdcI4Value();
			i--;

			// ldloc V
			while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
			if (i < 0 || !instrs[i].IsLdloc())
				return false;
			var stateVar = Instr.GetLocalVar(locals, instrs[i]);

			uint originalXorKey = xorKey; // save XOR_KEY before folding
			xorKey = unchecked(xor2 ^ xorKey);

			info = new DispatchInfo {
				DispatchVar = dispatchVar,
				XorKey = xorKey,
				Modulus = modulus,
				StateVar = stateVar,
				EmbeddedMul = embeddedMul,
				HasEmbeddedMul = true,
				OriginalXorKey = originalXorKey,
			};
			return true;
		}

		/// <summary>
		/// Returns true for instructions that have no effect on the dispatch computation:
		/// nop, conv.i4, conv.u4. These may be sprinkled between core operations by
		/// the obfuscator or by de4dot's own transforms.
		/// </summary>
		static bool IsHarmlessOp(Instr instr) {
			var code = instr.OpCode.Code;
			return code == Code.Nop || code == Code.Conv_I4 || code == Code.Conv_U4;
		}

		// ────────────────────────────────────────────────────────────────────
		//  CFG reachability (A)
		// ────────────────────────────────────────────────────────────────────

		/// <summary>
		/// Reverse BFS from target: returns the set of all blocks that can reach 'target'
		/// by traversing the Sources (predecessor) links. O(N+E) — computed once per dispatch.
		/// </summary>
		static HashSet<Block> ComputeReverseReachable(Block target, int maxNodes = 5000) {
			var reachable = new HashSet<Block> { target };
			var queue = new Queue<Block>();
			queue.Enqueue(target);

			while (queue.Count > 0 && reachable.Count < maxNodes) {
				var block = queue.Dequeue();
				foreach (var pred in block.Sources) {
					if (pred == null)
						continue;
					if (reachable.Add(pred))
						queue.Enqueue(pred);
				}
			}
			return reachable;
		}

		// ────────────────────────────────────────────────────────────────────
		//  Original state var discovery
		// ────────────────────────────────────────────────────────────────────

		/// <summary>
		/// Scans case-region blocks (via BuildBlockToCase) to find the original state
		/// variable S that case blocks write to via ldc.i4 CONST; stloc S.
		/// Returns the most common candidate that differs from StateVar/DispatchVar.
		///
		/// Constraining to case-region blocks avoids matching loop counters, temps,
		/// and other unrelated locals from blocks outside the switch structure.
		/// Requiring IsTrailingSafe after the store ensures the pattern is a
		/// state-setting suffix (not a mid-block assignment to a temp).
		/// </summary>
		Local FindOriginalStateVar(Block switchBlock, DispatchInfo info, Dictionary<Block, int> blockToCase) {
			var candidates = new Dictionary<Local, int>();

			foreach (var kv in blockToCase) {
				var block = kv.Key;
				if (block == switchBlock)
					continue;

				var instrs = block.Instructions;
				for (int i = instrs.Count - 1; i >= 1; i--) {
					if (!instrs[i].IsStloc())
						continue;
					if (!instrs[i - 1].IsLdcI4())
						continue;
					var local = Instr.GetLocalVar(locals, instrs[i]);
					if (local == null)
						continue;
					if (local == info.StateVar || local == info.DispatchVar)
						continue;

					// Structural evidence: the store should be a state-setting suffix,
					// followed only by nop/br (not a mid-block temp assignment).
					if (!IsTrailingSafe(instrs, i + 1))
						continue;

					if (!candidates.TryGetValue(local, out int count))
						count = 0;
					candidates[local] = count + 1;
				}
			}

			Local best = null;
			int bestCount = 0;
			foreach (var kv in candidates) {
				if (kv.Value > bestCount) {
					bestCount = kv.Value;
					best = kv.Key;
				}
			}
			return best;
		}

		// ────────────────────────────────────────────────────────────────────
		//  Backward slice evaluator (D)
		//
		//  Replaces positional heuristics (FindLocalStoreConstant, etc.) with
		//  a minimal backward slice that evaluates the expression producing a
		//  stack value. Only succeeds when the expression resolves to a single
		//  compile-time constant; fails closed on any ambiguity.
		// ────────────────────────────────────────────────────────────────────

		/// <summary>
		/// Minimal backward slice: starting from instruction at 'idx', evaluates
		/// the expression that produces the top-of-stack value by walking backward
		/// through the instruction stream.
		///
		/// Supported opcodes (full constant propagation):
		///   ldc.i4*        — immediate constant, resolves directly
		///   ldloc          — resolved via intra-block store lookup (scans backward for stloc)
		///   xor, mul,      — binary ops, recursively resolves both operands
		///   add, sub         (right operand at higher index, left at lower)
		///   conv.i4/u4     — identity for 32-bit arithmetic, recurses operand
		///   nop            — skipped (no stack effect)
		///
		/// Fails closed: returns null on any unsupported instruction, stack
		/// underflow, local value set outside the block, or recursion depth exceeded.
		///
		/// Returns (value, startIdx) where startIdx is the earliest instruction
		/// index contributing to the result. Returns null on failure.
		/// </summary>
		(uint value, int startIdx)? SliceBackward(List<Instr> instrs, int idx, int depth = 0) {
			// Recursion depth limit prevents pathological chains
			if (depth > 20 || idx < 0 || idx >= instrs.Count)
				return null;

			var instr = instrs[idx];

			// Immediate constant: resolves directly
			if (instr.IsLdcI4())
				return ((uint)instr.GetLdcI4Value(), idx);

			// Load local: search backward for the most recent store to the same
			// local within this block, then recursively resolve what was stored.
			// If the local is set outside the block, we cannot resolve it — fail.
			if (instr.IsLdloc()) {
				var local = Instr.GetLocalVar(locals, instr);
				if (local == null)
					return null;
				for (int j = idx - 1; j >= 0; j--) {
					if (instrs[j].IsStloc() && Instr.GetLocalVar(locals, instrs[j]) == local)
						return SliceBackward(instrs, j - 1, depth + 1);
				}
				return null; // local value set outside this block
			}

			var code = instr.OpCode.Code;

			// Nop: no stack effect, skip and continue backward
			if (code == Code.Nop)
				return SliceBackward(instrs, idx - 1, depth + 1);

			// Unary conversions: identity for 32-bit unsigned arithmetic
			if (code == Code.Conv_I4 || code == Code.Conv_U4)
				return SliceBackward(instrs, idx - 1, depth + 1);

			// Dup: this slicer is a value-tree solver that can't model stack
			// duplication. Reject — the forward evaluator handles dup instead.
			if (code == Code.Dup)
				return null;

			// Pop: consumes top-of-stack. Skip over the popped expression
			// to find the value below it. For ldc A; ldc B; pop at [0,1,2]:
			// SliceBackward(2): pop → slice(1)=(B,1) → slice(0)=(A,0) ✓
			if (code == Code.Pop) {
				var popped = SliceBackward(instrs, idx - 1, depth + 1);
				if (popped == null)
					return null;
				return SliceBackward(instrs, popped.Value.startIdx - 1, depth + 1);
			}

			// Binary ops: in IL, left operand is pushed first (lower index),
			// right operand pushed second (higher index). Walk backward:
			// resolve right operand from idx-1, then left from before right's start.
			if (code == Code.Xor || code == Code.Mul || code == Code.Add || code == Code.Sub) {
				var right = SliceBackward(instrs, idx - 1, depth + 1);
				if (right == null)
					return null;
				var left = SliceBackward(instrs, right.Value.startIdx - 1, depth + 1);
				if (left == null)
					return null;

				uint result;
				if (code == Code.Xor)
					result = unchecked(left.Value.value ^ right.Value.value);
				else if (code == Code.Mul)
					result = unchecked(left.Value.value * right.Value.value);
				else if (code == Code.Add)
					result = unchecked(left.Value.value + right.Value.value);
				else // Sub
					result = unchecked(left.Value.value - right.Value.value);

				return (result, left.Value.startIdx);
			}

			// Unsupported instruction: fail closed — do not guess
			return null;
		}

		// ────────────────────────────────────────────────────────────────────
		//  Constant discovery (D)
		//
		//  Two strategies are attempted in order:
		//  1. Backward slice — recursive value-tree solver. Tried first to
		//     preserve established behavior and avoid polluting dispatch-val
		//     maps with extra constants that could break the "all dispatch
		//     vals produce same target" invariant in mul-xor rewrites.
		//     Explicitly rejects dup (which it can't model).
		//  2. Forward suffix evaluator — processes the block suffix with a uint
		//     stack, naturally handling dup and stack shapes. Fallback for cases
		//     the backward slicer can't resolve (e.g., dup, stloc between
		//     operands).
		// ────────────────────────────────────────────────────────────────────

		/// <summary>
		/// Finds a constant value that feeds the dispatch state variable.
		///
		/// The target variable is OriginalStateVar (for embedded-mul with known
		/// original var) or StateVar (standard dispatch).
		///
		/// Returns (stateVal, startIdx, patternLen) where:
		///   stateVal  — the constant in the STATE domain
		///   startIdx  — first instruction of the pattern (negative = not found)
		///   patternLen — exact number of instructions in the constant-producing pattern
		/// </summary>
		(uint stateVal, int startIdx, int patternLen) FindConstantForDispatch(List<Instr> instrs, DispatchInfo info) {
			Local targetVar = (info.HasEmbeddedMul && info.OriginalStateVar != null)
				? info.OriginalStateVar
				: info.StateVar;

			// Strategy 1: Backward slice (preserves established behavior)
			if (targetVar != null) {
				for (int i = instrs.Count - 1; i >= 1; i--) {
					if (!instrs[i].IsStloc())
						continue;
					var local = Instr.GetLocalVar(locals, instrs[i]);
					if (local != targetVar)
						continue;

					var result = SliceBackward(instrs, i - 1);
					if (result != null) {
						int startIdx = result.Value.startIdx;
						int patternLen = i - startIdx + 1;
						return (result.Value.value, startIdx, patternLen);
					}
					break;
				}
			}
			else {
				// Stack-based (StateVar == null): value left on top of stack.
				if (instrs.Count > 0) {
					int effectiveEnd = instrs.Count - 1;
					while (effectiveEnd >= 0) {
						var code = instrs[effectiveEnd].OpCode.Code;
						if (code != Code.Nop && code != Code.Br && code != Code.Br_S)
							break;
						effectiveEnd--;
					}
					if (effectiveEnd >= 0) {
						var result = SliceBackward(instrs, effectiveEnd);
						if (result != null) {
							int startIdx = result.Value.startIdx;
							int patternLen = effectiveEnd - startIdx + 1;
							return (result.Value.value, startIdx, patternLen);
						}
					}
				}
			}

			// Strategy 2: Forward suffix evaluator fallback (handles dup, etc.)
			var fwd = ForwardEvaluateStore(instrs, targetVar);
			if (fwd != null)
				return fwd.Value;

			return (0, -1, 0);
		}

		/// <summary>
		/// Forward-evaluates a block's instructions to find the constant stored to
		/// targetVar. Handles dup, conv, nop, and stack shapes naturally.
		///
		/// Uses per-entry provenance tracking: each stack entry and local value carries
		/// the startIdx of the earliest instruction that contributed to it. This ensures
		/// precise pattern length computation even with multiple expressions on the stack.
		///
		/// For local-based: finds the last store to targetVar that resolves to a constant.
		/// For stack-based (targetVar == null): finds the constant left on top of stack
		/// after the last non-nop/br instruction.
		///
		/// Returns (value, startIdx, patternLen) on success, null on failure.
		/// Only succeeds when all inputs resolve to compile-time constants.
		/// </summary>
		(uint stateVal, int startIdx, int patternLen)? ForwardEvaluateStore(
			List<Instr> instrs, Local targetVar) {
			var stack = new List<(uint value, int startIdx)>();
			var localValues = new Dictionary<Local, (uint value, int startIdx)>();

			// Track the last successful constant store to targetVar
			int? lastStoreIdx = null;
			uint? lastStoreVal = null;
			int lastStoreStartIdx = -1;

			for (int i = 0; i < instrs.Count; i++) {
				var instr = instrs[i];
				var code = instr.OpCode.Code;

				if (instr.IsLdcI4()) {
					stack.Add(((uint)instr.GetLdcI4Value(), i));
					continue;
				}
				if (instr.IsLdloc()) {
					var local = Instr.GetLocalVar(locals, instr);
					if (local != null && localValues.TryGetValue(local, out var entry)) {
						// Preserve provenance from the original store
						stack.Add(entry);
						continue;
					}
					// Unknown local — push a marker by clearing the stack
					stack.Clear();
					continue;
				}
				if (instr.IsStloc()) {
					var local = Instr.GetLocalVar(locals, instr);
					if (stack.Count < 1) {
						// Value is unknown — if this stores to targetVar, invalidate
						// any earlier tracked store (the earlier value is stale).
						if (local == targetVar) {
							lastStoreIdx = null;
							lastStoreVal = null;
						}
						stack.Clear();
						continue;
					}
					var top = stack[stack.Count - 1];
					stack.RemoveAt(stack.Count - 1);
					if (local != null) {
						localValues[local] = top;
						if (local == targetVar) {
							lastStoreIdx = i;
							lastStoreVal = top.value;
							lastStoreStartIdx = top.startIdx;
						}
					}
					continue;
				}

				if (code == Code.Xor || code == Code.Mul || code == Code.Add || code == Code.Sub) {
					if (stack.Count < 2) {
						stack.Clear();
						continue;
					}
					var r = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1);
					var l = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1);
					uint result;
					if (code == Code.Xor) result = unchecked(l.value ^ r.value);
					else if (code == Code.Mul) result = unchecked(l.value * r.value);
					else if (code == Code.Add) result = unchecked(l.value + r.value);
					else result = unchecked(l.value - r.value);
					stack.Add((result, System.Math.Min(l.startIdx, r.startIdx)));
					continue;
				}
				if (code == Code.Dup) {
					if (stack.Count < 1) { stack.Clear(); continue; }
					stack.Add(stack[stack.Count - 1]);
					continue;
				}
				if (code == Code.Conv_I4 || code == Code.Conv_U4 || code == Code.Nop)
					continue;
				// Unconditional branch: everything after it in this block is dead code.
				// Break to avoid simulating a path that won't execute.
				if (code == Code.Br || code == Code.Br_S)
					break;
				if (code == Code.Pop) {
					if (stack.Count >= 1)
						stack.RemoveAt(stack.Count - 1);
					else
						stack.Clear();
					continue;
				}

				// Unknown instruction: reset all tracked state. Clearing localValues
				// prevents stale constants from persisting after a local is overwritten
				// by an untracked instruction (e.g., call result stored to local).
				stack.Clear();
				localValues.Clear();
			}

			// Local-based: return the last constant store to targetVar
			if (targetVar != null && lastStoreIdx.HasValue && lastStoreVal.HasValue) {
				int patternLen = lastStoreIdx.Value - lastStoreStartIdx + 1;
				if (patternLen > 0 && patternLen <= 20) // reject pathologically long patterns
					return (lastStoreVal.Value, lastStoreStartIdx, patternLen);
			}

			// Stack-based (targetVar == null): return whatever is on top of stack
			if (targetVar == null && stack.Count >= 1) {
				var top = stack[stack.Count - 1];
				// Find effective end (skip trailing nop/br)
				int effectiveEnd = instrs.Count - 1;
				while (effectiveEnd >= 0) {
					var c = instrs[effectiveEnd].OpCode.Code;
					if (c != Code.Nop && c != Code.Br && c != Code.Br_S)
						break;
					effectiveEnd--;
				}
				if (effectiveEnd >= 0) {
					int patternLen = effectiveEnd - top.startIdx + 1;
					if (patternLen > 0 && patternLen <= 20)
						return (top.value, top.startIdx, patternLen);
				}
			}

			return null;
		}

		// ────────────────────────────────────────────────────────────────────
		//  Safety verification (F)
		// ────────────────────────────────────────────────────────────────────

		/// <summary>
		/// Centralized safety check before every rewrite (F). Verifies:
		///   1. Switch targets list exists
		///   2. Modulus == switch target count (arithmetic consistency)
		///   3. Case index is in bounds [0, Targets.Count)
		///   4. Target block is not null
		///
		/// Returns the target block on success, null on failure (skip rewrite).
		/// A null return means "fail closed — do not rewrite this source."
		/// </summary>
		static Block VerifyAndGetTarget(Block switchBlock, DispatchInfo info, int caseIdx) {
			if (switchBlock.Targets == null)
				return null;
			// Modulus must match switch target count: if not, the modulus arithmetic
			// would produce indices that don't correspond to the actual switch layout.
			if (info.Modulus != (uint)switchBlock.Targets.Count)
				return null;
			// Case index is always in [0, Modulus) due to unsigned modulus, but verify
			// explicitly as a safety net against arithmetic bugs.
			if (caseIdx < 0 || caseIdx >= switchBlock.Targets.Count)
				return null;
			return switchBlock.Targets[caseIdx]; // null if switch entry is null
		}

		// ────────────────────────────────────────────────────────────────────
		//  Property-based self-check
		//
		//  After computing a rewrite candidate via the domain helpers (C),
		//  re-derive the case index by forward-evaluating the dispatch block's
		//  actual IL instructions with a concrete uint stack.  This is an
		//  independent computation path that reads MUL, XOR2, XOR_KEY, and
		//  MOD directly from IL operands — not from DispatchInfo fields.
		//  Any domain-mapping mistake (wrong formula, wrong field extraction,
		//  embedded-mul sign error) will cause the simulated result to
		//  disagree with the computed one, and the rewrite is skipped.
		// ────────────────────────────────────────────────────────────────────

		/// <summary>
		/// Forward-evaluates the dispatch block's IL from instruction 0 with a
		/// concrete uint stack.  Returns the case index (the value on top of
		/// the stack when the switch instruction executes), or -1 if the
		/// simulation cannot complete (unsupported instruction, stack issue).
		///
		/// <paramref name="stateVarLocal"/> identifies which ldloc to substitute
		/// with <paramref name="stateVarInput"/>.  If null (stack-based dispatch),
		/// <paramref name="stateVarInput"/> is pre-seeded on the stack.
		///
		/// Supported IL: ldc.i4*, ldloc (matched local only), stloc (consume),
		/// xor, mul, add, sub, rem.un, dup, conv.i4/u4, nop, switch.
		/// All arithmetic is unchecked 32-bit, matching the CLR's semantics.
		/// </summary>
		int SimulateDispatch(Block switchBlock, Local stateVarLocal, uint stateVarInput) {
			var stack = new List<uint>();
			var localValues = new Dictionary<Local, uint>();

			// Seed the known local so ldloc resolves it; stack-based dispatch
			// pre-seeds the stack instead.
			if (stateVarLocal != null)
				localValues[stateVarLocal] = stateVarInput;
			else
				stack.Add(stateVarInput);

			return SimulateDispatchCore(switchBlock, stack, localValues);
		}

		/// <summary>
		/// Forward-evaluates the dispatch block's IL with an empty initial state.
		/// Used for internal-constant dispatches where the block's own IL provides
		/// all values (merged dead-code prefix). Returns case index or -1.
		/// </summary>
		int SimulateDispatchFromEmpty(Block switchBlock) {
			return SimulateDispatchCore(switchBlock, new List<uint>(), new Dictionary<Local, uint>());
		}

		/// <summary>
		/// Core simulation engine: forward-evaluates dispatch block IL with the
		/// given initial stack and local values. Returns case index or -1.
		/// </summary>
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
						return -1; // unknown local — can't simulate
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

				if (code == Code.Xor) {
					if (stack.Count < 2) return -1;
					uint r = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1);
					uint l = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1);
					stack.Add(unchecked(l ^ r));
					continue;
				}
				if (code == Code.Mul) {
					if (stack.Count < 2) return -1;
					uint r = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1);
					uint l = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1);
					stack.Add(unchecked(l * r));
					continue;
				}
				if (code == Code.Add) {
					if (stack.Count < 2) return -1;
					uint r = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1);
					uint l = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1);
					stack.Add(unchecked(l + r));
					continue;
				}
				if (code == Code.Sub) {
					if (stack.Count < 2) return -1;
					uint r = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1);
					uint l = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1);
					stack.Add(unchecked(l - r));
					continue;
				}
				if (code == Code.Rem_Un) {
					if (stack.Count < 2) return -1;
					uint r = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1);
					uint l = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1);
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
					continue; // identity for 32-bit
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

				return -1; // unsupported instruction
			}
			return -1; // no switch reached
		}

		/// <summary>
		/// Converts a STATE-domain value to the STATEVAR domain (what info.StateVar
		/// holds at dispatch time). This is the sole STATE→STATEVAR converter.
		///
		/// For embedded-mul with OriginalStateVar: the case block stores to
		/// OriginalStateVar and the unmerged transition applies ^ OriginalXorKey
		/// to produce the StateVar-domain value.
		/// Otherwise the state value IS what StateVar holds (identity).
		/// </summary>
		static uint StateValToStateVarInput(DispatchInfo info, uint stateVal) {
			if (info.HasEmbeddedMul && info.OriginalStateVar != null)
				return unchecked(stateVal ^ info.OriginalXorKey);
			return stateVal;
		}

		// ────────────────────────────────────────────────────────────────────
		//  Dispatch val collection
		// ────────────────────────────────────────────────────────────────────

		/// <summary>
		/// Collects dispatch vals from all discoverable sources:
		/// 1. Constant stores in switch-region blocks (case-region + direct/funnel sources)
		/// 2. Propagation through multiply-XOR chains (fixed-point)
		///
		/// Constant discovery is restricted to the intersection of reverseReachable
		/// and (blockToCase ∪ direct sources ∪ funnel sources). This prevents
		/// preheader/init code that happens to store to StateVar from polluting
		/// the dispatch val map and inflating coverage for dead-case removal.
		///
		/// Returns a map: caseIndex → set of dispatch vals that map to it.
		/// </summary>
		Dictionary<int, HashSet<uint>> CollectAllDispatchVals(Block switchBlock, DispatchInfo info,
			HashSet<Block> reverseReachable, Dictionary<Block, int> blockToCase) {
			var caseToDispatchVals = new Dictionary<int, HashSet<uint>>();

			// If the dispatch has an internal constant (merged dead-code prefix),
			// register its dispatch val. Already STATEVAR-domain — no StateValToStateVarInput.
			if (info.InternalStateVarInput.HasValue) {
				uint dv = StateToDispatchVal(info, info.InternalStateVarInput.Value);
				AddDispatchVal(caseToDispatchVals, info, dv);
			}

			// Build the set of blocks eligible for constant discovery:
			// case-region blocks + direct sources + sources behind funnels.
			var eligible = new HashSet<Block>();
			foreach (var kv in blockToCase)
				eligible.Add(kv.Key);
			foreach (var source in switchBlock.Sources) {
				if (source == switchBlock)
					continue;
				eligible.Add(source);
				// Look through funnel blocks (shared nop/br junctions)
				if (IsFunnelBlock(source)) {
					foreach (var funnelSource in source.Sources) {
						if (funnelSource != switchBlock)
							eligible.Add(funnelSource);
					}
				}
			}

			// 1. Search eligible blocks that can reach dispatch (intersection)
			foreach (var block in eligible) {
				if (block == switchBlock)
					continue;
				if (!reverseReachable.Contains(block))
					continue;
				var (stateVal, startIdx, _) = FindConstantForDispatch(block.Instructions, info);
				if (startIdx >= 0) {
					uint svInput = StateValToStateVarInput(info, stateVal);
					uint dv = StateToDispatchVal(info, svInput);
					AddDispatchVal(caseToDispatchVals, info, dv);
				}
			}

			// 1b. Discover constants from pop-through block predecessors.
			// Opaque predicate patterns: predecessors push via ldc+dup, pop block
			// relays to dispatch. Extract constants before dup in each predecessor.
			foreach (var source in switchBlock.Sources) {
				if (source == switchBlock)
					continue;
				if (!IsPopThroughBlock(source))
					continue;
				foreach (var pred in source.Sources) {
					if (pred == switchBlock || pred == source)
						continue;
					if (!reverseReachable.Contains(pred))
						continue;
					var instrs = pred.Instructions;
					int lastIdx = instrs.Count - 1;
					while (lastIdx >= 0) {
						var c = instrs[lastIdx].OpCode.Code;
						if (c != Code.Nop && c != Code.Br && c != Code.Br_S) break;
						lastIdx--;
					}
					if (lastIdx < 1 || instrs[lastIdx].OpCode.Code != Code.Dup)
						continue;
					var result = SliceBackward(instrs, lastIdx - 1);
					if (result == null)
						continue;
					uint svInput = StateValToStateVarInput(info, result.Value.value);
					uint dv = StateToDispatchVal(info, svInput);
					AddDispatchVal(caseToDispatchVals, info, dv);
				}
			}

			// 2. Fixed-point propagation through multiply-XOR chains
			PropagateMultiplyXor(switchBlock, info, caseToDispatchVals, blockToCase);

			return caseToDispatchVals;
		}

		void AddDispatchVal(Dictionary<int, HashSet<uint>> caseToDispatchVals, DispatchInfo info, uint dv) {
			int ci = NormalizeCaseIndex(info, dv);
			if (!caseToDispatchVals.TryGetValue(ci, out var set))
				caseToDispatchVals[ci] = set = new HashSet<uint>();
			set.Add(dv);
		}

		/// <summary>
		/// Seeds dispatch vals for "pure self-loop" embedded-mul dispatches where
		/// case blocks don't modify StateVar at all. The dispatch itself is the
		/// state transition:
		///   dispatchVal_next = dispatchVal_current * EmbeddedMul ^ XorKey
		///
		/// Finds the initial value of StateVar using backward slicing (D),
		/// then iterates the self-loop formula to discover all reachable dispatch vals.
		/// Stops when the sequence cycles or exceeds Modulus iterations.
		/// </summary>
		void SeedSelfLoopDispatchVals(Block switchBlock, DispatchInfo info,
			Dictionary<int, HashSet<uint>> caseToDispatchVals, HashSet<Block> reverseReachable) {
			if (!info.HasEmbeddedMul || info.StateVar == null)
				return;

			// Find initial value of StateVar using backward slice (D).
			// Search reverse-reachable blocks for a store to StateVar.
			uint initialValue = 0;
			bool foundInitial = false;
			foreach (var block in reverseReachable) {
				if (foundInitial)
					break;
				if (block == switchBlock)
					continue;
				var instrs = block.Instructions;
				for (int i = instrs.Count - 1; i >= 1; i--) {
					if (!instrs[i].IsStloc())
						continue;
					var local = Instr.GetLocalVar(locals, instrs[i]);
					if (local != info.StateVar)
						continue;
					var result = SliceBackward(instrs, i - 1);
					if (result != null && IsTrailingSafe(instrs, i + 1)) {
						// initialValue is in STATEVAR domain: it was stored to info.StateVar
						// by either (a) initial setup before the loop, or (b) a case transition
						// computing the next state. The switchBlock's own dup+stloc is excluded
						// (skipped above). StateToDispatchVal correctly converts to DISPATCH domain.
						initialValue = result.Value.value;
						foundInitial = true;
						break;
					}
				}
			}

			if (!foundInitial)
				return;

			// Compute initial dispatch val and iterate the self-loop formula.
			// Both input and output are in the DISPATCH-VAL domain.
			uint dv = StateToDispatchVal(info, initialValue);
			var seen = new HashSet<uint>();
			int maxIter = (int)info.Modulus + 1;
			while (maxIter-- > 0 && seen.Add(dv)) {
				AddDispatchVal(caseToDispatchVals, info, dv);
				dv = SelfLoopNext(info, dv);
			}
		}

		/// <summary>
		/// BFS from each switch target to map every reachable block to its owning case index.
		/// Blocks reachable from multiple cases are marked ambiguous and excluded.
		/// The switch block itself is always excluded from the map.
		/// </summary>
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

		/// <summary>
		/// Fixed-point propagation through multiply-XOR chains.
		/// For each source with a mul-xor pattern in a case with known dispatch vals,
		/// computes the next state and dispatch val to discover new cases.
		///
		/// Domain flow (C):
		///   dispatchVal (DISPATCH) → MulXorToNextState → nextState (STATE)
		///   nextState (STATE) → StateToDispatchVal → nextDispatchVal (DISPATCH)
		///   nextDispatchVal → NormalizeCaseIndex → newCaseIndex (CASE)
		/// </summary>
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

					if (!TryGetMultiplyXorPattern(source, info, out uint mulConst, out uint xor2Const, out _, out _))
						continue;

					if (!blockToCase.TryGetValue(source, out int ownerCase))
						continue;

					if (!caseToDispatchVals.TryGetValue(ownerCase, out var dispatchVals))
						continue;

					foreach (var dispatchVal in new List<uint>(dispatchVals)) {
						// DISPATCH → STATE → STATEVAR → DISPATCH (C)
						uint nextState = MulXorToNextState(dispatchVal, mulConst, xor2Const);
						uint svInput = StateValToStateVarInput(info, nextState);
						uint newDv = StateToDispatchVal(info, svInput);
						int newCase = NormalizeCaseIndex(info, newDv);

						if (!caseToDispatchVals.TryGetValue(newCase, out var newSet)) {
							caseToDispatchVals[newCase] = newSet = new HashSet<uint>();
						}
						if (newSet.Add(newDv))
							changed = true;
					}
				}
			}
		}

		// ────────────────────────────────────────────────────────────────────
		//  Rewriting
		//
		//  Each rewrite method follows the same safety protocol:
		//  1. Identify the source block and its transition pattern
		//  2. Compute the target case using domain helpers (C)
		//  3. Self-check: simulate the dispatch IL independently to verify
		//     the computed case index matches the IL's actual semantics
		//  4. Verify the target via VerifyAndGetTarget (F)
		//  5. Verify instruction removal is safe via IsTrailingSafe (B)
		//  6. Only then rewrite the source block
		// ────────────────────────────────────────────────────────────────────

		/// <summary>
		/// Simplifies a dispatch block whose state value is an internal constant
		/// (merged dead-code prefix). The dispatch always goes to the same case,
		/// so the entire switch can be replaced with a direct branch.
		///
		/// The InternalStateVarInput is already in STATEVAR domain (the pre-XOR
		/// operand), so no StateValToStateVarInput conversion is needed.
		///
		/// Replaces the dispatch block (not sources) — all sources naturally flow
		/// through the simplified dispatch. Dead case blocks are cleaned up by
		/// RemoveDeadBlocks in the next iteration.
		/// </summary>
		bool RewriteInternalConstantDispatch(Block switchBlock, DispatchInfo info) {
			if (!info.InternalStateVarInput.HasValue)
				return false;

			// Domain conversion (STATEVAR → DISPATCH → CASE):
			// InternalStateVarInput is STATEVAR-domain — skip StateValToStateVarInput
			uint stateVarInput = info.InternalStateVarInput.Value;
			uint dispatchVal = StateToDispatchVal(info, stateVarInput);
			int caseIdx = NormalizeCaseIndex(info, dispatchVal);

			// Self-check (hard gate): simulate from empty — the block's own IL
			// provides the value via the merged prefix
			int simCaseIdx = SimulateDispatchFromEmpty(switchBlock);
			if (simCaseIdx != caseIdx)
				return false;

			// (F) Safety verification
			var targetBlock = VerifyAndGetTarget(switchBlock, info, caseIdx);
			if (targetBlock == null)
				return false;

			// Replace the entire dispatch with a direct branch to the target.
			// ReplaceLastInstrsWithBranch calls DisconnectFromFallThroughAndTargets
			// first, which properly disconnects all existing switch targets.
			var instrs = switchBlock.Instructions;
			switchBlock.ReplaceLastInstrsWithBranch(instrs.Count, targetBlock);
			return true;
		}

		/// <summary>
		/// Rewrites constant sources: blocks that store a constant to the state
		/// variable then fall through to the dispatch.
		///
		/// Uses backward slicing (D) to resolve the stored constant, which handles
		/// both simple (ldc.i4 C; stloc S) and compound (ldc.i4 A; ldc.i4 B; xor; stloc S)
		/// patterns. Only removes the exact instructions identified by the slice,
		/// plus trailing nop/br (B).
		///
		/// Safety: VerifyAndGetTarget (F) validates the computed target before rewriting.
		/// </summary>
		bool RewriteConstantSources(Block switchBlock, DispatchInfo info) {
			bool modified = false;

			foreach (var source in new List<Block>(switchBlock.Sources)) {
				if (source == switchBlock)
					continue;

				// Safety: don't rewrite blocks with conditional branches.
				// ReplaceLastInstrsWithBranch calls DisconnectFromFallThroughAndTargets
				// which would corrupt the CFG for blocks that have switch/conditional targets.
				if (source.Targets != null && source.Targets.Count > 0)
					continue;

				var instrs = source.Instructions;
				if (instrs.Count == 0)
					continue;

				// (D) Use backward slice to find constant and its exact instruction range
				var (stateVal, startIdx, patternLen) = FindConstantForDispatch(instrs, info);
				if (startIdx < 0 || patternLen <= 0)
					continue;

				// (B) Only remove if trailing instructions after the pattern are dead (nop/br).
				// This ensures we never delete payload code that follows the state-setting pattern.
				int patternEnd = startIdx + patternLen;
				if (!IsTrailingSafe(instrs, patternEnd))
					continue;
				int numToRemove = instrs.Count - startIdx;
				if (numToRemove <= 0 || numToRemove > instrs.Count)
					continue;

				// (C) Domain conversion: STATE → STATEVAR → DISPATCH → CASE
				uint stateVarInput = StateValToStateVarInput(info, stateVal);
				uint dispatchVal = StateToDispatchVal(info, stateVarInput);
				int caseIdx = NormalizeCaseIndex(info, dispatchVal);

				// Property-based self-check (hard gate): simulate the dispatch IL
				// independently and require exact agreement. If simulation fails
				// (-1) or disagrees, skip the rewrite — no proof means no rewrite.
				int simCaseIdx = SimulateDispatch(switchBlock, info.StateVar, stateVarInput);
				if (simCaseIdx != caseIdx)
					continue;

				// (F) Safety verification before rewriting
				var targetBlock = VerifyAndGetTarget(switchBlock, info, caseIdx);
				if (targetBlock == null)
					continue;

				source.ReplaceLastInstrsWithBranch(numToRemove, targetBlock);
				modified = true;
			}

			// Second pass: handle pop-through blocks.
			// These are blocks containing only pop + nop/br that relay values from
			// their predecessors (via the opaque predicate dup pattern) to the dispatch.
			// Rewrite the predecessors directly to bypass the pop block and dispatch.
			foreach (var source in new List<Block>(switchBlock.Sources)) {
				if (source == switchBlock)
					continue;
				if (!IsPopThroughBlock(source))
					continue;
				modified |= RewritePopThroughPredecessors(switchBlock, info, source);
			}

			return modified;
		}

		/// <summary>
		/// Returns true if instructions from 'fromIdx' to end are safe to remove:
		/// only nop/br or nothing follows. This ensures we don't delete real code (B).
		/// </summary>
		static bool IsTrailingSafe(List<Instr> instrs, int fromIdx) {
			for (int i = fromIdx; i < instrs.Count; i++) {
				var code = instrs[i].OpCode.Code;
				if (code != Code.Nop && code != Code.Br && code != Code.Br_S)
					return false;
			}
			return true;
		}

		/// <summary>
		/// Rewrites multiply-XOR transition blocks. These have the pattern:
		///   ldloc V; ldc.i4 MUL2; mul; ldc.i4 XOR3; xor; [stloc S]
		///
		/// For each source with this pattern, looks up all dispatch vals for its
		/// owning case, computes the next state via MulXorToNextState, converts
		/// to dispatch val via StateToDispatchVal, and resolves the target case.
		///
		/// Only rewrites when ALL dispatch vals for the case produce the same target.
		/// Safety: exact pattern removal (B), verified target (F).
		/// </summary>
		bool RewriteMultiplyXorSources(Block switchBlock, DispatchInfo info,
			Dictionary<int, HashSet<uint>> caseToDispatchVals, Dictionary<Block, int> blockToCase) {
			if (info.DispatchVar == null)
				return false;
			if (switchBlock.Targets == null)
				return false;

			bool modified = false;

			foreach (var source in new List<Block>(switchBlock.Sources)) {
				if (source == switchBlock)
					continue;

				if (!TryGetMultiplyXorPattern(source, info, out uint mulConst, out uint xor2Const,
					out int patternStart, out int patternLen))
					continue;

				// (B) Only remove if pattern ends at block end or only nop/br follow
				int patternEnd = patternStart + patternLen;
				if (!IsTrailingSafe(source.Instructions, patternEnd))
					continue;
				int numToRemove = source.Instructions.Count - patternStart;
				if (numToRemove <= 0 || numToRemove > source.Instructions.Count)
					continue;

				if (!blockToCase.TryGetValue(source, out int ownerCase))
					continue;

				if (!caseToDispatchVals.TryGetValue(ownerCase, out var dispatchVals))
					continue;

				// All dispatch vals for this case must produce the same target.
				// If any produce a different target, skip (fail closed).
				// Property-based self-check: for each dispatch val, simulate the
				// dispatch IL with the computed next state and verify agreement.
				int? resolvedCaseIdx = null;
				bool allSame = true;
				foreach (var dispatchVal in dispatchVals) {
					// Domain flow (C): DISPATCH → STATE → STATEVAR → DISPATCH → CASE
					uint nextState = MulXorToNextState(dispatchVal, mulConst, xor2Const);
					uint stateVarInput = StateValToStateVarInput(info, nextState);
					uint nextDispatchVal = StateToDispatchVal(info, stateVarInput);
					int targetCaseIdx = NormalizeCaseIndex(info, nextDispatchVal);

					// Self-check (hard gate): require exact simulation agreement
					int simCaseIdx = SimulateDispatch(switchBlock, info.StateVar, stateVarInput);
					if (simCaseIdx != targetCaseIdx) {
						allSame = false;
						break;
					}

					if (resolvedCaseIdx == null)
						resolvedCaseIdx = targetCaseIdx;
					else if (resolvedCaseIdx.Value != targetCaseIdx) {
						allSame = false;
						break;
					}
				}

				if (!allSame || resolvedCaseIdx == null)
					continue;

				// (F) Safety verification
				var targetBlock = VerifyAndGetTarget(switchBlock, info, resolvedCaseIdx.Value);
				if (targetBlock == null)
					continue;

				source.ReplaceLastInstrsWithBranch(numToRemove, targetBlock);
				modified = true;
			}

			return modified;
		}

		/// <summary>
		/// Rewrites self-loop sources in embedded-mul dispatches where the dispatch
		/// block itself is the state transition (case blocks don't modify state).
		///
		/// Looks through funnel blocks (shared nop/br junctions) to find case exit
		/// blocks that unconditionally fall through to the dispatch.
		///
		/// Safety constraints:
		///   - Only redirects blocks with no conditional branches. ReplaceLastInstrsWithBranch
		///     calls DisconnectFromFallThroughAndTargets which would corrupt blocks with
		///     conditional branches by removing their branch targets.
		///   - Skips blocks that have their own transition (constant or mul-xor pattern).
		///   - All dispatch vals for the case must produce the same target (fail closed).
		///   - VerifyAndGetTarget (F) validates the computed target.
		/// </summary>
		bool RewriteSelfLoopSources(Block switchBlock, DispatchInfo info,
			Dictionary<int, HashSet<uint>> caseToDispatchVals, Dictionary<Block, int> blockToCase) {
			if (!info.HasEmbeddedMul)
				return false;
			if (switchBlock.Targets == null)
				return false;

			bool modified = false;

			// Collect sources: direct sources in blockToCase, plus look through funnels
			var sourcesToProcess = new List<Block>();

			foreach (var source in switchBlock.Sources) {
				if (source == switchBlock)
					continue;
				if (blockToCase.ContainsKey(source)) {
					sourcesToProcess.Add(source);
				} else if (IsFunnelBlock(source)) {
					// Look through: process funnel's sources that belong to a known case
					foreach (var funnelSource in source.Sources) {
						if (funnelSource != switchBlock && funnelSource != source
						    && blockToCase.ContainsKey(funnelSource))
							sourcesToProcess.Add(funnelSource);
					}
				}
			}

			foreach (var source in new List<Block>(sourcesToProcess)) {
				// Safety: only redirect blocks that unconditionally fall through.
				// Blocks with conditional branches (Targets != null) must not be
				// passed to ReplaceLastInstrsWithBranch — it would disconnect all
				// branch targets, corrupting the CFG.
				if (source.Targets != null && source.Targets.Count > 0)
					continue;

				// Skip sources that have their own transition (constant or mul-xor).
				// Those are handled by RewriteConstantSources / RewriteMultiplyXorSources.
				var (_, constStartIdx, _) = FindConstantForDispatch(source.Instructions, info);
				if (constStartIdx >= 0)
					continue;
				if (TryGetMultiplyXorPattern(source, info, out _, out _, out _, out _))
					continue;

				if (!blockToCase.TryGetValue(source, out int ownerCase))
					continue;
				if (!caseToDispatchVals.TryGetValue(ownerCase, out var dispatchVals))
					continue;

				// All dispatch vals for this case must produce the same next target.
				// Property-based self-check: in a self-loop, StateVar holds the
				// previous dispatch val (stored by the dispatch's dup+stloc).
				// Feed it into the dispatch IL and verify the simulated case index.
				int? resolvedCaseIdx = null;
				bool allSame = true;
				foreach (var dv in dispatchVals) {
					// Self-loop: DISPATCH → DISPATCH (C)
					uint nextDv = SelfLoopNext(info, dv);
					int targetCaseIdx = NormalizeCaseIndex(info, nextDv);

					// Self-check (hard gate): require exact simulation agreement
					int simCaseIdx = SimulateDispatch(switchBlock, info.StateVar, dv);
					if (simCaseIdx != targetCaseIdx) {
						allSame = false;
						break;
					}

					if (resolvedCaseIdx == null)
						resolvedCaseIdx = targetCaseIdx;
					else if (resolvedCaseIdx.Value != targetCaseIdx) {
						allSame = false;
						break;
					}
				}

				if (!allSame || resolvedCaseIdx == null)
					continue;

				// (F) Safety verification
				var targetBlock = VerifyAndGetTarget(switchBlock, info, resolvedCaseIdx.Value);
				if (targetBlock == null)
					continue;

				source.ReplaceLastInstrsWithBranch(0, targetBlock);
				modified = true;
			}

			return modified;
		}

		/// <summary>
		/// Returns true if the block is a simple pass-through (funnel): only nop/br instructions.
		/// These act as shared junction points between case exits and the dispatch.
		/// </summary>
		static bool IsFunnelBlock(Block block) {
			var instrs = block.Instructions;
			if (instrs.Count == 0)
				return true;
			for (int i = 0; i < instrs.Count; i++) {
				var code = instrs[i].OpCode.Code;
				if (code != Code.Nop && code != Code.Br && code != Code.Br_S)
					return false;
			}
			return true;
		}

		/// <summary>
		/// Returns true if the block is a pop-through relay: contains only pop + nop/br.
		/// These appear in opaque predicate patterns where two conditional paths each
		/// push a constant via dup, then merge at this pop block before the dispatch.
		/// Pattern: condition → [ldc X; dup; br pop_block] / [ldc Y; dup] → [pop] → dispatch
		/// </summary>
		static bool IsPopThroughBlock(Block block) {
			var instrs = block.Instructions;
			if (instrs.Count == 0)
				return false;
			bool hasPop = false;
			for (int i = 0; i < instrs.Count; i++) {
				var code = instrs[i].OpCode.Code;
				if (code == Code.Pop) {
					hasPop = true;
					continue;
				}
				if (code != Code.Nop && code != Code.Br && code != Code.Br_S)
					return false;
			}
			return hasPop;
		}

		/// <summary>
		/// Rewrites predecessors of a pop-through block.
		///
		/// Each predecessor pushes a constant via the obfuscator's dup pattern:
		///   ldc.i4 X; dup; [br pop_block]
		/// The dup creates an extra stack copy; the pop-through block removes one,
		/// leaving the value for the dispatch.
		///
		/// For each predecessor: extract the constant before dup, compute the
		/// dispatch target, verify via SimulateDispatch and VerifyAndGetTarget,
		/// then redirect the predecessor directly to the target case block.
		/// </summary>
		bool RewritePopThroughPredecessors(Block switchBlock, DispatchInfo info, Block popBlock) {
			bool modified = false;

			foreach (var pred in new List<Block>(popBlock.Sources)) {
				if (pred == switchBlock || pred == popBlock)
					continue;

				var instrs = pred.Instructions;
				if (instrs.Count == 0)
					continue;

				// Don't touch blocks with conditional branches — removing their
				// trailing instructions would corrupt the CFG.
				if (pred.Targets != null && pred.Targets.Count > 0)
					continue;

				// Find the last meaningful instruction (skip nop/br)
				int lastIdx = instrs.Count - 1;
				while (lastIdx >= 0) {
					var c = instrs[lastIdx].OpCode.Code;
					if (c != Code.Nop && c != Code.Br && c != Code.Br_S) break;
					lastIdx--;
				}

				// Must end with dup (obfuscator's opaque predicate pattern)
				if (lastIdx < 1 || instrs[lastIdx].OpCode.Code != Code.Dup)
					continue;

				// Resolve the value before dup — this is what survives the pop
				var result = SliceBackward(instrs, lastIdx - 1);
				if (result == null)
					continue;
				uint stateVal = result.Value.value;
				int startIdx = result.Value.startIdx;

				// (B) Verify trailing safety from after the constant+dup pattern
				if (!IsTrailingSafe(instrs, lastIdx + 1))
					continue;
				int numToRemove = instrs.Count - startIdx;
				if (numToRemove <= 0 || numToRemove > instrs.Count)
					continue;

				// (C) Domain conversion: STATE → STATEVAR → DISPATCH → CASE
				uint stateVarInput = StateValToStateVarInput(info, stateVal);
				uint dispatchVal = StateToDispatchVal(info, stateVarInput);
				int caseIdx = NormalizeCaseIndex(info, dispatchVal);

				// Property-based self-check (hard gate)
				int simCaseIdx = SimulateDispatch(switchBlock, info.StateVar, stateVarInput);
				if (simCaseIdx != caseIdx)
					continue;

				// (F) Safety verification
				var targetBlock = VerifyAndGetTarget(switchBlock, info, caseIdx);
				if (targetBlock == null)
					continue;

				pred.ReplaceLastInstrsWithBranch(numToRemove, targetBlock);
				modified = true;
			}

			return modified;
		}

		// ────────────────────────────────────────────────────────────────────
		//  Dead case removal (E)
		// ────────────────────────────────────────────────────────────────────

		/// <summary>
		/// Redirects dead switch case targets to fallthrough (E).
		///
		/// A case is considered dead when ALL conditions hold:
		///   1. No known dispatch val maps to it (no entry in caseToDispatchVals)
		///   2. The target block has no sources other than the switch block
		///      (no non-switch predecessors that could reach it)
		///   3. We have sufficient dispatch val coverage (≥50% of cases discovered)
		///      indicating good coverage of the transition graph
		///
		/// Uses SetNewTarget to properly maintain bidirectional source/target
		/// relationships (unlike ReplaceLastInstrsWithBranch which disconnects all).
		/// </summary>
		bool RemoveDeadSwitchCases(Block switchBlock, DispatchInfo info,
			Dictionary<int, HashSet<uint>> caseToDispatchVals) {
			if (switchBlock.Targets == null || switchBlock.FallThrough == null)
				return false;

			int targetCount = switchBlock.Targets.Count;
			if (targetCount == 0)
				return false;

			// (F) Modulus must match switch target count
			if (info.Modulus != (uint)targetCount)
				return false;

			// (E) Only proceed if we've recovered dispatch vals for a significant
			// fraction of cases. This guards against removing live cases when our
			// dispatch val collection was incomplete.
			int coveredCases = caseToDispatchVals.Count;
			if (coveredCases * 2 < targetCount)
				return false;

			bool modified = false;
			var fallThrough = switchBlock.FallThrough;

			for (int i = 0; i < targetCount; i++) {
				var target = switchBlock.Targets[i];
				if (target == null || target == fallThrough)
					continue;

				// Condition 1: no dispatch val maps to this case
				if (caseToDispatchVals.ContainsKey(i))
					continue;

				// Condition 2: target has no sources other than the switch block
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

		// ────────────────────────────────────────────────────────────────────
		//  Pattern matching
		// ────────────────────────────────────────────────────────────────────

		/// <summary>
		/// Searches a block for the multiply-XOR state transition pattern (B).
		/// Returns the MUL and XOR2 constants, and the exact pattern start index
		/// and length (not "everything from here to end").
		///
		/// Tolerates harmless ops (nop, conv.i4, conv.u4) between core operations,
		/// matching the tolerance in TryExtractEmbeddedMul.
		///
		/// Accepts ldloc of DispatchVar or StateVar (for embedded-mul where StateVar
		/// is the original dispatch variable before folding).
		/// Accepts stloc of StateVar or OriginalStateVar (for embedded-mul).
		/// </summary>
		bool TryGetMultiplyXorPattern(Block block, DispatchInfo info,
			out uint mulConst, out uint xor2Const, out int patternStart, out int patternLen) {

			mulConst = 0;
			xor2Const = 0;
			patternStart = 0;
			patternLen = 0;
			var instrs = block.Instructions;

			if (instrs.Count < 5)
				return false;

			for (int end = instrs.Count - 1; end >= 4; end--) {
				int i = end;
				bool hasTrailingStloc = false;

				// Optional trailing stloc state_var (local-based pattern)
				if (instrs[i].IsStloc()) {
					var storeVar = Instr.GetLocalVar(locals, instrs[i]);
					if ((info.StateVar != null && storeVar == info.StateVar) ||
					    (info.OriginalStateVar != null && storeVar == info.OriginalStateVar)) {
						hasTrailingStloc = true;
						i--;
					}
				}

				// xor (skip harmless ops)
				while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
				if (i < 0 || instrs[i].OpCode.Code != Code.Xor)
					continue;
				i--;

				// ldc.i4 XOR2
				while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
				if (i < 0 || !instrs[i].IsLdcI4())
					continue;
				xor2Const = (uint)instrs[i].GetLdcI4Value();
				i--;

				// mul
				while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
				if (i < 0 || instrs[i].OpCode.Code != Code.Mul)
					continue;
				i--;

				// ldc.i4 MUL
				while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
				if (i < 0 || !instrs[i].IsLdcI4())
					continue;
				mulConst = (uint)instrs[i].GetLdcI4Value();
				i--;

				// ldloc V
				while (i >= 0 && IsHarmlessOp(instrs[i])) i--;
				if (i < 0 || !instrs[i].IsLdloc())
					continue;
				var loadedVar = Instr.GetLocalVar(locals, instrs[i]);
				if (loadedVar == null)
					continue;
				// Accept ldloc of DispatchVar, StateVar, or OriginalStateVar only.
				// When none match, we can't identify the pattern — reject.
				bool isKnownVar = (info.DispatchVar != null && loadedVar == info.DispatchVar) ||
				                  (info.StateVar != null && loadedVar == info.StateVar) ||
				                  (info.OriginalStateVar != null && loadedVar == info.OriginalStateVar);
				if (!isKnownVar)
					continue;

				patternStart = i;
				patternLen = end - i + 1; // exact range from ldloc to end (including trailing stloc if present)
				return true;
			}
			return false;
		}
	}
}
