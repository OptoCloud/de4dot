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

using dnlib.DotNet.Emit;

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4.cflow;

/// <summary>
///     Domain conversion helpers for XOR-switch dispatch deobfuscation.
///     All arithmetic uses unchecked 32-bit operations matching the
///     obfuscator's runtime behavior. Each helper documents which domain
///     its input and output belong to.
/// </summary>
static class DomainMath {
	/// <summary>
	///     Converts a StateVar-domain value to a dispatch value.
	///     Input:  STATEVAR domain (the value held in info.StateVar at dispatch time).
	///     For STATE-domain inputs (e.g., from FindConstantForDispatch),
	///     callers must first convert via StateValToStateVarInput().
	///     Output: DISPATCH-VAL domain (the value used before modulus).
	///     Standard:     dispatchVal = stateVarValue ^ XorKey
	///     EmbeddedMul:  dispatchVal = stateVarValue * EmbeddedMul ^ XorKey
	/// </summary>
	internal static uint StateToDispatchVal(DispatchInfo info, uint stateVarValue) {
		if (info.HasEmbeddedMul)
			return unchecked((stateVarValue * info.EmbeddedMul) ^ info.XorKey);
		return unchecked(stateVarValue ^ info.XorKey);
	}

	/// <summary>
	///     Computes the next state from a multiply-XOR transition.
	///     Input:  DISPATCH-VAL domain (current dispatch value).
	///     Output: STATE domain (needs StateToDispatchVal to become a dispatch val).
	///     nextState = (dispatchVal * mulConst) ^ xor2Const
	/// </summary>
	internal static uint MulXorToNextState(uint dispatchVal, uint mulConst, uint xor2Const) =>
		unchecked(dispatchVal * mulConst ^ xor2Const);

	/// <summary>
	///     Computes the next dispatch val for self-loop embedded-mul dispatches
	///     where the dispatch block itself is the transition (no case-block state store).
	///     Input:  DISPATCH-VAL domain.
	///     Output: DISPATCH-VAL domain.
	///     nextDispatchVal = currentDispatchVal * EmbeddedMul ^ XorKey
	/// </summary>
	internal static uint SelfLoopNext(DispatchInfo info, uint currentDispatchVal) =>
		unchecked((currentDispatchVal * info.EmbeddedMul) ^ info.XorKey);

	/// <summary>
	///     Converts a dispatch value to a case index via modulus.
	///     Input:  DISPATCH-VAL domain.
	///     Output: CASE-INDEX domain (0 ≤ result &lt; Modulus).
	/// </summary>
	internal static int NormalizeCaseIndex(DispatchInfo info, uint dispatchVal) => (int)(dispatchVal % info.Modulus);

	/// <summary>
	///     Converts a STATE-domain value to the STATEVAR domain (what info.StateVar
	///     holds at dispatch time). This is the sole STATE→STATEVAR converter.
	///     For embedded-mul with OriginalStateVar: the case block stores to
	///     OriginalStateVar and the unmerged transition applies ^ OriginalXorKey
	///     to produce the StateVar-domain value.
	///     Otherwise the state value IS what StateVar holds (identity).
	/// </summary>
	internal static uint StateValToStateVarInput(DispatchInfo info, uint stateVal) {
		if (info.HasEmbeddedMul && info.OriginalStateVar != null)
			return unchecked(stateVal ^ info.OriginalXorKey);
		return stateVal;
	}

	/// <summary>
	///     Full chain: STATE → STATEVAR → DISPATCH-VAL → CASE-INDEX.
	///     Returns (caseIdx, stateVarInput) so callers can pass stateVarInput
	///     to simulation verification.
	/// </summary>
	internal static (int caseIdx, uint stateVarInput) StateValToCase(DispatchInfo info, uint stateVal) {
		uint svInput = StateValToStateVarInput(info, stateVal);
		uint dv = StateToDispatchVal(info, svInput);
		int ci = NormalizeCaseIndex(info, dv);
		return (ci, svInput);
	}

	/// <summary>
	///     Inverse of StateToDispatchVal: converts a dispatch value back to a
	///     StateVar-domain value.
	///     Input:  DISPATCH-VAL domain.
	///     Output: STATEVAR domain.
	///     Standard:     stateVarValue = dispatchVal ^ XorKey
	///     EmbeddedMul:  stateVarValue = (dispatchVal ^ XorKey) * inverse(EmbeddedMul)
	///     Returns null if EmbeddedMul has no inverse (even multiplier).
	/// </summary>
	internal static uint? DispatchValToStateVar(DispatchInfo info, uint dispatchVal) {
		uint xored = unchecked(dispatchVal ^ info.XorKey);
		if (!info.HasEmbeddedMul)
			return xored;
		uint? inv = ModularInverse32(info.EmbeddedMul);
		if (inv == null)
			return null;
		return unchecked(xored * inv.Value);
	}

	/// <summary>
	///     Computes the multiplicative inverse of 'a' modulo 2^32.
	///     Only odd numbers have an inverse; returns null for even 'a'.
	///     Uses Newton's method: x_{n+1} = x_n * (2 - a * x_n).
	/// </summary>
	internal static uint? ModularInverse32(uint a) {
		if ((a & 1) == 0)
			return null;
		uint x = a; // initial guess (a is its own inverse mod 2^2 when odd)
		for (int i = 0; i < 5; i++) // 5 iterations: doubles correct bits each time → 2→4→8→16→32
			x = unchecked(x * (2 - a * x));
		return x;
	}

	/// <summary>
	///     Applies a binary arithmetic opcode to two uint operands.
	///     Supports Xor, Mul, Add, Sub.
	/// </summary>
	internal static uint ApplyBinaryOp(Code code, uint left, uint right) {
		if (code == Code.Xor) return unchecked(left ^ right);
		if (code == Code.Mul) return unchecked(left * right);
		if (code == Code.Add) return unchecked(left + right);
		return unchecked(left - right);
	}
}
