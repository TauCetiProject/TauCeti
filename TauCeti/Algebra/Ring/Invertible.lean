/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Invertible
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Nat.Cast.Basic

/-!
# Invertible elements and `Ring.inverse`

This file collects elementary lemmas on units in semirings, `Ring.inverse` in monoids with zero
and distributive negation, and the image of `⅟2` under ring homomorphisms:

* `IsUnit.eq_zero_of_add_self_eq_zero`: if `2` is a unit in a semiring, zero is the only element
  that doubles to zero.
* `TauCeti.ringInverse_neg`: `Ring.inverse` commutes with negation.
* `TauCeti.ringInverse_neg_one_pow_mul`: multiplying on the left by `(-1) ^ k` commutes with
  `Ring.inverse`.
* `TauCeti.two_mul_map_invOf_two`: a ring homomorphism sends `⅟2` to a half of `1`.
* `Commute.ringInverse_right`: an element commuting with `b` commutes with `Ring.inverse b`.
* `Ring.inverse_one_sub_eq`: the resolvent identity
  `Ring.inverse (1 - x) = 1 + x * Ring.inverse (1 - x)` when `1 - x` is a unit.
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

namespace TauCeti

/-- A ring homomorphism sends `⅟2` to a half of `1`: `2 * f ⅟2 = 1`. -/
theorem two_mul_map_invOf_two {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [Invertible (2 : R)] [FunLike F R S] [RingHomClass F R S] (f : F) : 2 * f ⅟2 = 1 := by
  rw [← map_ofNat f 2, ← map_mul, mul_invOf_self, map_one]

end TauCeti

/-- An element commuting with `b` commutes with its ring inverse. -/
theorem Commute.ringInverse_right {M₀ : Type*} [MonoidWithZero M₀] {a b : M₀}
    (h : Commute a b) : Commute a (Ring.inverse b) := by
  by_cases hb : IsUnit b
  · obtain ⟨u, rfl⟩ := hb
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hb]
    exact Commute.zero_right a

/-- If `1 - x` is a unit, its inverse satisfies the resolvent identity
`Ring.inverse (1 - x) = 1 + x * Ring.inverse (1 - x)`. -/
theorem Ring.inverse_one_sub_eq {α : Type*} [Ring α] {x : α} (hu : IsUnit (1 - x)) :
    Ring.inverse (1 - x) = 1 + x * Ring.inverse (1 - x) := by
  have h := Ring.mul_inverse_cancel _ hu
  rw [sub_mul, one_mul] at h
  exact sub_eq_iff_eq_add.1 h
