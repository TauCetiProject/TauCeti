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

This file collects elementary lemmas on units in semirings, numeric literal invertibility, and
`Ring.inverse` in monoids with zero and distributive negation:

* `IsUnit.eq_zero_of_add_self_eq_zero`: if `2` is a unit in a semiring, zero is the only element
  that doubles to zero.
* `TauCeti.invertibleMapOfNat`: ring homomorphisms preserve `Invertible` instances on numeric
  literals `n ≥ 2`.
* `TauCeti.map_invOf_ofNat`: ring homomorphisms send `⅟(ofNat(n))` to `⅟(ofNat(n))` independently
  of the chosen `Invertible` instances.
* `TauCeti.ringInverse_neg`: `Ring.inverse` commutes with negation.
* `TauCeti.ringInverse_neg_one_pow_mul`: multiplying on the left by `(-1) ^ k` commutes with
  `Ring.inverse`.
* `Commute.ringInverse_right`: an element commuting with `b` commutes with `Ring.inverse b`.
-/

public section

/-- If `2` is a unit, only zero doubles to zero. -/
theorem IsUnit.eq_zero_of_add_self_eq_zero {R : Type*} [Semiring R] (h2 : IsUnit (2 : R)) :
    ∀ x : R, x + x = 0 → x = 0 := by
  intro x hx
  exact h2.mul_right_eq_zero.mp (by rwa [two_mul])

namespace TauCeti

/-- Ring homomorphisms preserve invertibility of numeric literals `n ≥ 2`. -/
abbrev invertibleMapOfNat {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (n : ℕ) [n.AtLeastTwo] [Invertible (ofNat(n) : R)] :
    Invertible (ofNat(n) : S) :=
  (Invertible.map f (ofNat(n) : R)).copy ofNat(n) (by exact (map_ofNat f n).symm)

/-- Ring homomorphisms send the inverse of a numeric literal `n ≥ 2` to the inverse of `n`,
independently of the choice of `Invertible` instances. -/
theorem map_invOf_ofNat {R S F : Type*} [NonAssocSemiring R] [Semiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (n : ℕ) [n.AtLeastTwo]
    [Invertible (ofNat(n) : R)] [Invertible (ofNat(n) : S)] :
    f ⅟(ofNat(n) : R) = ⅟(ofNat(n) : S) :=
  (invOf_eq_right_inv (by rw [← map_ofNat f n, ← map_mul, mul_invOf_self, map_one])).symm

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

/-- An element commuting with `b` commutes with its ring inverse. -/
theorem Commute.ringInverse_right {M₀ : Type*} [MonoidWithZero M₀] {a b : M₀}
    (h : Commute a b) : Commute a (Ring.inverse b) := by
  by_cases hb : IsUnit b
  · obtain ⟨u, rfl⟩ := hb
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hb]
    exact Commute.zero_right a
