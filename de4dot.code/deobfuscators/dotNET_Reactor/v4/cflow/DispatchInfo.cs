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

using de4dot.blocks;
using dnlib.DotNet.Emit;

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4.cflow;

/// <summary>
///     Extracted constants and locals from a dispatch block.
///     Standard:     [ldloc state] ldc.i4 XOR_KEY; xor; [dup; stloc dispatch_var;] ldc.i4 MOD; rem.un; switch
///     Embedded-mul: ldloc V; ldc.i4 MUL; mul; ldc.i4 XOR2; xor; ldc.i4 XOR_KEY; xor; [dup; stloc;] ldc.i4 MOD; rem.un;
///     switch
///     For embedded-mul, XOR2 and XOR_KEY are folded into XorKey = XOR2 ^ XOR_KEY.
///     OriginalXorKey preserves the pre-fold XOR_KEY for state→dispatch conversion.
/// </summary>
struct DispatchInfo {
	public Local DispatchVar; // local stored via dup+stloc after XOR (null if absent)
	public Local StateVar; // local loaded at start of dispatch (null if state arrives on stack)
	public uint XorKey; // XOR key (or folded XOR2^XOR_KEY for embedded-mul)
	public uint Modulus; // switch case count (dispatch_val % Modulus)
	public uint EmbeddedMul; // multiply constant when dispatch has embedded mul-xor
	public bool HasEmbeddedMul; // true when a multiply-XOR transition was merged into dispatch
	public bool SplitEmbeddedMul; // true when mul prefix is in a predecessor, not the switch block
	public Local OriginalStateVar; // the var case blocks write to (null if not embedded-mul or not found)
	public uint OriginalXorKey; // dispatch XOR_KEY before folding with XOR2 (0 if not embedded-mul)
	public uint? InternalStateVarInput; // STATEVAR-domain; non-null when dispatch has merged dead-code prefix

	public bool SelfLoopEligible =>
		HasEmbeddedMul && !SplitEmbeddedMul && DispatchVar != null && StateVar == DispatchVar;
}

struct RewriteCandidate {
	public Block SourceBlock;
	public Block TargetBlock;
	public int InstructionsToRemove;
	public bool NeedStackCleanup; // pop;pop for cross-block XOR2
}
