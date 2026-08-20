using de4dot.blocks.cflow;

namespace de4dot.blocks.tests {
	/// <summary>
	/// The int32 abstract value lattice: shift counts and unsigned remainder.
	///
	/// These are pure static functions, so they are the cheapest thing in the tree to pin — and among
	/// the most valuable, because a wrong answer here is invisible until it has already chosen a
	/// switch arm or folded a branch away. The shift guards defend against a concrete failure shape:
	/// a count that is a nonzero multiple of the operand width computes its mask from
	/// <c>width - count</c>, which is a shift by zero, which reads as "every bit known" — turning an
	/// unknown operand into a known constant. Obfuscators emit oversized shift counts deliberately,
	/// so these are live inputs rather than hypotheticals.
	///
	/// Deliberately not driven through <see cref="InstructionVerification"/> against the real
	/// runtime: an out-of-range shift count is undefined in CIL, so there is no ground truth to
	/// compare against — x64 masks the count to 5 bits, and agreeing with that would be agreeing with
	/// one implementation, not with the spec. The in-range cases are covered differentially in
	/// <see cref="InstructionEmulatorTest.OperationsSmokeTest"/>; what is asserted here is what the
	/// emulator must refuse to know.
	/// </summary>
	[TestClass]
	public sealed class Int32ValueOperationsTest {
		static Int32Value Known(int value) => new Int32Value(value);
		static Int32Value Unknown() => Int32Value.CreateUnknown();

		static void AssertKnown(int expected, Int32Value actual) {
			Assert.IsTrue(actual.AllBitsValid(), $"expected the known constant {expected}, got {actual}");
			Assert.AreEqual(expected, actual.Value);
		}

		static void AssertUnknown(Int32Value actual) =>
			Assert.IsFalse(actual.AllBitsValid(), $"expected an unknown value, got the constant {actual.Value}");

		[TestMethod]
		[DataRow(0)]
		[DataRow(1)]
		[DataRow(31)]
		public void ShiftsInRangeAreComputed(int count) {
			AssertKnown(1 << count, Int32Value.Shl(Known(1), Known(count)));
			AssertKnown(unchecked((int)(0x80000000u >> count)),
				Int32Value.Shr_Un(Known(unchecked((int)0x80000000u)), Known(count)));
		}

		/// <summary>
		/// The counterpart to <see cref="ShiftsInRangeAreComputed"/>. A count at or past the operand
		/// width leaves the result unspecified in CIL, so the only answer true on every conforming
		/// runtime is to refuse. Agreeing with x64's masking would be agreeing with one
		/// implementation rather than the spec.
		/// </summary>
		[TestMethod]
		[DataRow(32)]
		[DataRow(64)]
		[DataRow(-1)]
		[DataRow(int.MinValue)]
		public void ShiftsOutOfRangeAreUnknown(int count) {
			AssertUnknown(Int32Value.Shl(Known(43), Known(count)));
			AssertUnknown(Int32Value.Shr(Known(43), Known(count)));
			AssertUnknown(Int32Value.Shr_Un(Known(43), Known(count)));
		}

		/// <summary>
		/// Why the guard is a correctness requirement and not just conservatism. Masking the count
		/// instead makes a nonzero multiple of the width shift by zero, and the mask arithmetic then
		/// evaluates <c>uint.MaxValue >> (width - 0)</c>. C# masks that count back to zero, so it
		/// yields all-ones rather than zero and every bit reads as known: an operand with unknown
		/// bits is reported as a hard constant. Both directions have a way in -- Shl through the
		/// low-bit fill, Shr through sign extension -- so both are pinned here.
		/// </summary>
		[TestMethod]
		[DataRow(32)]
		[DataRow(64)]
		public void AnOutOfRangeCountMustNotInventKnownBits(int count) {
			AssertUnknown(Int32Value.Shl(Unknown(), Known(count)));
			var signBitOnly = Int32Value.Or(Unknown(), Known(unchecked((int)0x80000000u)));
			AssertUnknown(Int32Value.Shr(signBitOnly, Known(count)));
		}

		[TestMethod]
		public void ShiftByAnUnknownCountIsUnknown() {
			AssertUnknown(Int32Value.Shl(Known(1), Unknown()));
			AssertUnknown(Int32Value.Shr(Known(1), Unknown()));
			AssertUnknown(Int32Value.Shr_Un(Known(1), Unknown()));
		}

		[TestMethod]
		public void ShiftByZeroPreservesPartialKnowledge() {
			var partial = Int32Value.Shl(Unknown(), Known(4));
			Assert.AreSame(partial, Int32Value.Shl(partial, Known(0)));
		}

		/// <summary>
		/// <c>(uint)a % (uint)b == (uint)a &amp; (uint)(b - 1)</c> when b is a power of two, which lets
		/// a partially-known operand keep the bits the mask preserves instead of collapsing to
		/// unknown. Only valid unsigned, and so only in the <c>Rem_Un</c> overload.
		/// </summary>
		[TestMethod]
		[DataRow(1)]
		[DataRow(2)]
		[DataRow(16)]
		[DataRow(256)]
		public void UnsignedRemainderByAPowerOfTwoIsComputedFromKnownOperands(int divisor) {
			for (int value = 0; value < 40; value++)
				AssertKnown(value % divisor, Int32Value.Rem_Un(Known(value), Known(divisor)));
		}

		[TestMethod]
		public void UnsignedRemainderByAPowerOfTwoNarrowsAPartiallyKnownOperand() {
			// (unknown << 8) has its low 8 bits known to be zero, so % 16 is known to be 0.
			var lowBitsZero = Int32Value.Shl(Unknown(), Known(8));
			AssertKnown(0, Int32Value.Rem_Un(lowBitsZero, Known(16)));
		}

		[TestMethod]
		public void UnsignedRemainderByANonPowerOfTwoStaysUnknown() =>
			AssertUnknown(Int32Value.Rem_Un(Int32Value.Shl(Unknown(), Known(8)), Known(24)));

		[TestMethod]
		public void UnsignedRemainderByAnUnknownDivisorStaysUnknown() =>
			AssertUnknown(Int32Value.Rem_Un(Known(100), Unknown()));

		/// <summary>
		/// The fold must not fire for a zero divisor: <c>rem.un</c> by zero throws at runtime, so
		/// there is no value to fold to, and <c>b - 1</c> would mask with all bits set.
		/// </summary>
		[TestMethod]
		public void UnsignedRemainderByZeroStaysUnknown() =>
			AssertUnknown(Int32Value.Rem_Un(Int32Value.Shl(Unknown(), Known(8)), Known(0)));

		/// <summary>
		/// 0x80000000 is a power of two when read unsigned. Reading the divisor as signed would make
		/// it negative and skip the fold, so this pins the unsigned interpretation.
		/// </summary>
		[TestMethod]
		public void UnsignedRemainderTreatsTheHighBitDivisorAsAPowerOfTwo() {
			int divisor = unchecked((int)0x80000000u);
			AssertKnown(unchecked((int)0x7FFFFFFFu),
				Int32Value.Rem_Un(Known(unchecked((int)0xFFFFFFFFu)), Known(divisor)));
			AssertKnown(3, Int32Value.Rem_Un(Known(3), Known(divisor)));
		}
	}

	/// <summary>The int64 lattice. Same guards, 64-bit widths; shift counts are still int32.</summary>
	[TestClass]
	public sealed class Int64ValueOperationsTest {
		static Int64Value Known(long value) => new Int64Value(value);
		static Int32Value Count(int value) => new Int32Value(value);
		static Int64Value Unknown() => Int64Value.CreateUnknown();
		static Int32Value Unknown32() => Int32Value.CreateUnknown();

		static void AssertKnown(long expected, Int64Value actual) {
			Assert.IsTrue(actual.AllBitsValid(), $"expected the known constant {expected}, got {actual}");
			Assert.AreEqual(expected, actual.Value);
		}

		static void AssertUnknown(Int64Value actual) =>
			Assert.IsFalse(actual.AllBitsValid(), $"expected an unknown value, got the constant {actual.Value}");

		[TestMethod]
		[DataRow(0)]
		[DataRow(1)]
		[DataRow(63)]
		public void ShiftsInRangeAreComputed(int count) =>
			AssertKnown(1L << count, Int64Value.Shl(Known(1), Count(count)));



		/// <summary>The int64 form of <see cref="Int32ValueOperationsTest.ShiftsOutOfRangeAreUnknown"/>.</summary>
		[TestMethod]
		[DataRow(64)]
		[DataRow(128)]
		public void ShiftsOutOfRangeAreUnknown(int count) {
			AssertUnknown(Int64Value.Shl(Known(43), Count(count)));
			AssertUnknown(Int64Value.Shr(Known(43), Count(count)));
			AssertUnknown(Int64Value.Shr_Un(Known(43), Count(count)));
		}

		/// <summary>
		/// The int64 form of
		/// <see cref="Int32ValueOperationsTest.AnOutOfRangeCountMustNotInventKnownBits"/>.
		/// </summary>
		[TestMethod]
		[DataRow(64)]
		[DataRow(128)]
		public void AnOutOfRangeCountMustNotInventKnownBits(int count) {
			AssertUnknown(Int64Value.Shl(Unknown(), Count(count)));
			var signBitOnly = Int64Value.Or(Unknown(), Known(unchecked((long)0x8000000000000000UL)));
			AssertUnknown(Int64Value.Shr(signBitOnly, Count(count)));
		}

		[TestMethod]
		[DataRow(-1)]
		[DataRow(int.MinValue)]
		public void ShiftsNegativeUnknown(int count) {
			AssertUnknown(Int64Value.Shl(Unknown(), Count(count)));
			AssertUnknown(Int64Value.Shr(Unknown(), Count(count)));
			AssertUnknown(Int64Value.Shr_Un(Unknown(), Count(count)));
			// Also unknown when the operand IS known: the operation itself is undefined.
			AssertUnknown(Int64Value.Shl(Known(1L), Count(count)));
		}
		[TestMethod]
		[DataRow(64)]
		[DataRow(128)]
		[DataRow(-1)]
		[DataRow(int.MinValue)]
		public void ShiftsUnknownValuesIsUnknown(int count) {
			AssertUnknown(Int64Value.Shl(Unknown(), Count(count)));
			AssertUnknown(Int64Value.Shl(Known(count), Unknown32()));
			AssertUnknown(Int64Value.Shr(Unknown(), Count(count)));
			AssertUnknown(Int64Value.Shr(Known(count), Unknown32()));
			AssertUnknown(Int64Value.Shr_Un(Unknown(), Count(count)));
			AssertUnknown(Int64Value.Shr_Un(Known(count), Unknown32()));
		}

		[TestMethod]
		public void ShiftByAnUnknownCountIsUnknown() {
			AssertUnknown(Int64Value.Shl(Known(1), Unknown32()));
			AssertUnknown(Int64Value.Shr(Known(1), Unknown32()));
			AssertUnknown(Int64Value.Shr_Un(Known(1), Unknown32()));
		}

		/// <summary>A count of 32 is in range for int64 and must be computed, not rejected.</summary>
		[TestMethod]
		public void AThirtyTwoCountIsInRangeForInt64() =>
			AssertKnown(1L << 32, Int64Value.Shl(Known(1), Count(32)));
	}
}
