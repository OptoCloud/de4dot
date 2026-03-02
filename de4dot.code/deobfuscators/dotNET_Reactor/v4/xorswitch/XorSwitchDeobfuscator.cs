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
using dnlib.DotNet.Emit;

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4.xorswitch;

/// <summary>
///     Deobfuscates XOR-switch state machines produced by .NET Reactor v6.x.
///     Unified CFG-driven approach using abstract interpretation instead of pattern matching.
/// </summary>
class XorSwitchDeobfuscator : IBlocksDeobfuscator {
	Blocks blocks;

	public bool ExecuteIfNotModified => false;

	public void DeobfuscateBegin(Blocks blocks) => this.blocks = blocks;

	public bool Deobfuscate(List<Block> allBlocks) {
		bool modified = false;
		int totalDispatches = 0;
		int totalResolved = 0;
		int totalFailed = 0;
		int totalApplied = 0;
		int totalDead = 0;
		var modulusCounts = new Dictionary<int, int>();

		foreach (var block in allBlocks) {
			if (block.LastInstr.OpCode.Code != Code.Switch)
				continue;

			// Preprocessing: fold opaque constants
			OpaquePredicateFixer.Fold(block);
			foreach (var source in new List<Block>(block.Sources)) {
				if (source != block)
					OpaquePredicateFixer.Fold(source);
			}

			// Detect dispatch
			var dispatch = DispatchDetector.TryDetect(block, blocks);
			if (dispatch == null)
				continue;

			totalDispatches++;
			var node = dispatch.Value;

			// Step 0 diagnostic: tally modulus (CaseTargets.Count) per dispatch
			int m = node.CaseTargets.Count;
			modulusCounts.TryGetValue(m, out int cnt);
			modulusCounts[m] = cnt + 1;

			// Resolve edges
			var resolver = new EdgeResolver(node, blocks);
			var edges = resolver.ResolveAll();
			totalResolved += resolver.ResolvedCount;
			totalFailed += resolver.FailedCount;

			if (edges.Count == 0)
				continue;

			// Apply resolved edges
			int applied = SwitchRewriter.Apply(node, edges);
			totalApplied += applied;

			if (applied > 0)
				modified = true;

			// Count dead cases
			foreach (var caseTarget in node.CaseTargets) {
				if (caseTarget.Sources.Count == 0)
					totalDead++;
			}
		}

		if (totalDispatches > 0) {
			Logger.v("  XOR-switch: {0} dispatches, {1} edges resolved, {2} failed, {3} applied, {4} dead cases",
				totalDispatches, totalResolved, totalFailed, totalApplied, totalDead);

			// Step 0 diagnostic: dump modulus distribution (temporary — remove after one run)
			var sortedModuli = new List<KeyValuePair<int, int>>(modulusCounts);
			sortedModuli.Sort((a, b) => a.Key.CompareTo(b.Key));
			foreach (var kv in sortedModuli) {
				uint mu = (uint)kv.Key;
				bool isPow2 = mu != 0 && (mu & (mu - 1)) == 0;
				Logger.n("    M={0}: {1} dispatches{2}", kv.Key, kv.Value, isPow2 ? " (pow2)" : "");
			}
		}

		return modified;
	}
}
