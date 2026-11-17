/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Invertible
import Mathlib.Algebra.Ring.Commute

/-!
# Invertible elements and `Ring.inverse`

This file collects elementary lemmas on units in semirings and `Ring.inverse` in monoids with zero
and distributive negation:

* `IsUnit.eq_zero_of_add_self_eq_zero`: if `2` is a unit in a semiring, zero is the only element
  that doubles to zero.
* `TauCeti.ringInverse_neg`: `Ring.inverse` commutes with negation.
* `TauCeti.ringInverse_neg_one_pow_mul`: multiplying on the left by `(-1) ^ k` commutes with
  `Ring.inverse`.
-/

public section

/-- If `2` is a unit, only zero doubles to zero. -/
theorem IsUnit.eq_zero_of_add_self_eq_zero {R : Type*} [Semiring R] (h2 : IsUnit (2 : R)) :
    ∀ x : R, x + x = 0 → x = 0 := by
  intro x hx
  exact h2.mul_right_eq_zero.mp (by rwa [two_mul])

namespace TauCeti

variable {R : Type*} [MonoidWithZero R] [HasDistribNeg R]

/-- `Ring.inverse` commutes with negation. -/
@[simp]
theorem ringInverse_neg (a : R) : Ring.inverse (-a) = -Ring.inverse a := by
  by_cases ha : IsUnit a
  · obtain ⟨ia⟩ := ha.nonempty_invertible
    let _ : Invertible (-a) := invertibleNeg a
    rw [Ring.inverse_invertible, Ring.inverse_invertible, invOf_neg]
  · rw [Ring.inverse_non_unit _ (mt (IsUnit.neg_iff a).mp ha), Ring.inverse_non_unit _ ha,
      neg_zero]

/-- Multiplying on the left by `(-1) ^ k` commutes with `Ring.inverse`. -/
@[simp]
theorem ringInverse_neg_one_pow_mul (k : ℕ) (a : R) :
    Ring.inverse ((-1 : R) ^ k * a) = (-1 : R) ^ k * Ring.inverse a := by
  rcases neg_one_pow_eq_or R k with h | h <;> simp [h]

end TauCeti
