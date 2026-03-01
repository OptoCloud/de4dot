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

namespace de4dot.code.deobfuscators.dotNET_Reactor.v4.cflow;

/// <summary>
///     Discriminated union for constrained state knowledge.
///     Lattice: KnownConst → ConstSet(max=64) → Unknown.
///     Used by the state tracer to track what values a case block's state
///     variable can hold at entry and exit.
/// </summary>
abstract class StateValue {
	const int MaxSetSize = 64;

	public abstract bool IsUnknown { get; }
	public abstract uint? SingleValue { get; }
	public abstract IReadOnlyCollection<uint> Values { get; }
	public abstract StateValue Join(StateValue other);
	public abstract StateValue Apply(Func<uint, uint> f);

	public static StateValue Known(uint value) => new KnownConstValue(value);

	public static StateValue FromSet(HashSet<uint> values) {
		if (values == null || values.Count == 0)
			return MakeUnknown();
		if (values.Count == 1) {
			foreach (uint v in values)
				return new KnownConstValue(v);
		}

		if (values.Count > MaxSetSize)
			return MakeUnknown();
		return new ConstSetValue(new HashSet<uint>(values));
	}

	public static StateValue MakeUnknown() => UnknownValue.Instance;

	sealed class KnownConstValue : StateValue {
		readonly uint value;
		internal KnownConstValue(uint value) => this.value = value;
		public override bool IsUnknown => false;
		public override uint? SingleValue => value;
		public override IReadOnlyCollection<uint> Values => new[] { value };

		public override StateValue Join(StateValue other) {
			if (other.IsUnknown)
				return other;
			if (other.SingleValue.HasValue && other.SingleValue.Value == value)
				return this;
			var merged = new HashSet<uint> { value };
			foreach (uint v in other.Values)
				merged.Add(v);
			if (merged.Count > MaxSetSize)
				return MakeUnknown();
			return new ConstSetValue(merged);
		}

		public override StateValue Apply(Func<uint, uint> f) => new KnownConstValue(f(value));
	}

	sealed class ConstSetValue : StateValue {
		readonly HashSet<uint> values;
		internal ConstSetValue(HashSet<uint> values) => this.values = values;
		public override bool IsUnknown => false;
		public override uint? SingleValue => null;
		public override IReadOnlyCollection<uint> Values => values;

		public override StateValue Join(StateValue other) {
			if (other.IsUnknown)
				return other;
			var merged = new HashSet<uint>(values);
			foreach (uint v in other.Values)
				merged.Add(v);
			if (merged.Count > MaxSetSize)
				return MakeUnknown();
			return new ConstSetValue(merged);
		}

		public override StateValue Apply(Func<uint, uint> f) {
			var mapped = new HashSet<uint>();
			foreach (uint v in values)
				mapped.Add(f(v));
			if (mapped.Count > MaxSetSize)
				return MakeUnknown();
			return new ConstSetValue(mapped);
		}
	}

	sealed class UnknownValue : StateValue {
		internal static readonly UnknownValue Instance = new();
		UnknownValue() { }
		public override bool IsUnknown => true;
		public override uint? SingleValue => null;
		public override IReadOnlyCollection<uint> Values => null;
		public override StateValue Join(StateValue other) => this;
		public override StateValue Apply(Func<uint, uint> f) => this;
	}
}
