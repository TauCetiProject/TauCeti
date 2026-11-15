/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Int.WithZero

/-!
# Rational realizations of `ℤᵐ⁰`

This file constructs the monoid-with-zero homomorphism from `ℤᵐ⁰` to the nonnegative rationals
that sends an integer exponent `n` to `e ^ n`. It is the rational-valued counterpart of
Mathlib's `WithZeroMulInt.toNNReal` and is useful when a discretely valued field has an
integer-valued normalization whose associated absolute value is rational.

## Main definitions

* `WithZeroMulInt.toNNRat`: sends `0` to `0` and a nonzero exponent `n` to `e ^ n`.

## Main results

* `WithZeroMulInt.toNNRat_strictMono`: the map is strictly increasing when `1 < e`.

The statements follow Mathlib's `WithZeroMulInt.toNNReal`, with codomain `ℚ≥0` instead of
`ℝ≥0`; the map itself is built from Mathlib's `WithZero.lift'` and `zpowersHom`.
-/

public section
noncomputable section

open Multiplicative WithZero
open scoped NNRat

namespace WithZeroMulInt

/-- The monoid-with-zero homomorphism `ℤᵐ⁰ → ℚ≥0` sending a nonzero exponent `n` to `e ^ n`.

This is the nonnegative-rational counterpart of Mathlib's `WithZeroMulInt.toNNReal`. -/
def toNNRat {e : ℚ≥0} (he : e ≠ 0) : ℤᵐ⁰ →*₀ ℚ≥0 where
  __ := WithZero.lift' <|
    (Units.coeHom ℚ≥0).comp <| zpowersHom ℚ≥0ˣ (Units.mk0 e he)

/-- On a finite exponent, `toNNRat` is the corresponding integer power of its base. -/
@[simp]
theorem toNNRat_coe {e : ℚ≥0} (he : e ≠ 0) (n : Multiplicative ℤ) :
    toNNRat he (n : ℤᵐ⁰) = e ^ n.toAdd := by
  simp [toNNRat]

/-- The value of `toNNRat` at a nonzero element `x` is `e ^ WithZero.log x`. -/
theorem toNNRat_apply_of_ne_zero {e : ℚ≥0} (he : e ≠ 0) {x : ℤᵐ⁰} (hx : x ≠ 0) :
    toNNRat he x = e ^ log x := by
  rw [← toAdd_unzero_eq_log hx, ← toNNRat_coe, coe_unzero]

/-- The map `toNNRat` is strictly increasing when its base is greater than one. -/
theorem toNNRat_strictMono {e : ℚ≥0} (he : 1 < e) :
    StrictMono (toNNRat he.ne_zero) := by
  simp [StrictMono, WithZero.forall, zpow_pos he.pos, he]

/-- For a base different from zero and one, `toNNRat` takes the value one only at exponent
one, which represents the integer exponent zero in `ℤᵐ⁰`. -/
theorem toNNRat_eq_one_iff {e : ℚ≥0} (x : ℤᵐ⁰) (he0 : e ≠ 0) (he1 : e ≠ 1) :
    toNNRat he0 x = 1 ↔ x = 1 := by
  cases x <;> simp [zpow_eq_one_iff_right₀ bot_le he1, ← coe_one]

/-- For a base greater than one, strict comparison with one in `ℚ≥0` is strict comparison with
one in `ℤᵐ⁰`. -/
theorem toNNRat_lt_one_iff {e : ℚ≥0} {x : ℤᵐ⁰} (he : 1 < e) :
    toNNRat he.ne_zero x < 1 ↔ x < 1 := by
  rw [← (toNNRat_strictMono he).lt_iff_lt, map_one]

/-- For a base greater than one, comparison with one in `ℚ≥0` is comparison with one in
`ℤᵐ⁰`. -/
theorem toNNRat_le_one_iff {e : ℚ≥0} {x : ℤᵐ⁰} (he : 1 < e) :
    toNNRat he.ne_zero x ≤ 1 ↔ x ≤ 1 := by
  rw [← (toNNRat_strictMono he).le_iff_le, map_one]

end WithZeroMulInt
