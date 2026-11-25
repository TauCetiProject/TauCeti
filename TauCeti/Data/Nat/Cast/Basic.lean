/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Cast.Basic

/-!
# Casting natural remainders and vanishing numerals

The remainder identity `n = c * (n / c) + n % c` can be rearranged using subtraction
after casting to a ring, including when `c = 0`. In a semiring without zero divisors, the numeral
`4 = 2 * 2` vanishes exactly when `2` does.

## Main results

* `Nat.cast_mod_eq_sub_mul_div`: `((n % c : ℕ) : R) = n - c * (n / c : ℕ)`.
* `TauCeti.four_eq_zero_iff_two_eq_zero`: without zero divisors, `4 = 0` if and only if `2 = 0`.
* `TauCeti.add_natCast_ne_neg_natCast`: an element off `−ℕ` stays off `−ℕ` after adding a
  natural number.
-/

public section

namespace Nat

/-- A natural remainder cast into a ring is the dividend minus the divisor times the quotient. -/
theorem cast_mod_eq_sub_mul_div {R : Type*} [NonAssocRing R] (n c : ℕ) :
    ((n % c : ℕ) : R) = n - c * (n / c : ℕ) := by
  rw [eq_sub_iff_add_eq, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]

end Nat

namespace TauCeti

/-- In a semiring without zero divisors, such as a field, `4 = 2 * 2` vanishes exactly when `2`
does. -/
@[simp]
theorem four_eq_zero_iff_two_eq_zero {R : Type*} [NonAssocSemiring R] [NoZeroDivisors R] :
    (4 : R) = 0 ↔ (2 : R) = 0 := by
  rw [← two_add_two_eq_four, ← two_mul, mul_self_eq_zero]

/-- In an additive commutative group with one, an element off `−ℕ` stays off `−ℕ` after adding a
natural number. -/
theorem add_natCast_ne_neg_natCast {R : Type*} [AddCommGroupWithOne R] {a : R}
    (ha : ∀ m : ℕ, a ≠ -m) (n m : ℕ) : a + n ≠ -m := fun h =>
  ha (m + n) (by rw [Nat.cast_add, neg_add, ← h, add_neg_cancel_right])

end TauCeti
