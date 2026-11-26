/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.LinearCombination

/-!
# Primitive fourth and sixth roots of unity

In a commutative ring where `2 ≠ 0`, a square root of `-1` is a primitive fourth root of unity.
In a commutative ring where `2 ≠ 0` and `3 ≠ 0`, a root of the cyclotomic polynomial
`Φ₆ = X² - X + 1` is a primitive sixth root of unity. In an integral domain where `6 ≠ 0`,
the converse also holds. In a field where `6 ≠ 0`, for a square root `θ` of `-3` the element
`(1 + θ)/2` is a primitive sixth root of unity. These are the exceptional roots of unity of
the quadratic fields `ℚ(√-1)` and `ℚ(√-3)`.

## Main results

* `TauCeti.isPrimitiveRoot_four_of_sq_eq_neg_one`: a square root of `-1` is a primitive fourth
  root of unity.
* `TauCeti.isPrimitiveRoot_six_of_sq_sub_add_one_eq_zero`: a root of `Φ₆` is a primitive sixth
  root of unity.
* `TauCeti.isPrimitiveRoot_six_iff`: `μ` is a primitive sixth root of unity if and only if
  `μ² - μ + 1 = 0`.
* `TauCeti.isPrimitiveRoot_one_add_div_two_of_sq_eq_neg_three`: for `θ² = -3`, `(1 + θ)/2` is a
  primitive sixth root of unity.
-/

public section

open Polynomial

namespace TauCeti

/-- **The exceptional fourth root of unity.** In a commutative ring where `2 ≠ 0`, a square
root of `-1` is a primitive fourth root of unity. -/
theorem isPrimitiveRoot_four_of_sq_eq_neg_one {R : Type*} [CommRing R] [NeZero (2 : R)]
    {θ : R} (h : θ ^ 2 = -1) : IsPrimitiveRoot θ 4 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  have hnot : θ ^ (2 ^ 1) ≠ 1 := by
    intro he
    have hneg : (1 : R) = -1 := he.symm.trans h
    rw [eq_neg_iff_add_eq_zero, one_add_one_eq_two] at hneg
    exact NeZero.ne (2 : R) hneg
  have hfin : θ ^ (2 ^ (1 + 1)) = 1 := by
    rw [pow_succ (2 : ℕ) (1 : ℕ), pow_mul, pow_one, h, neg_one_sq]
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin

/-- A root of `Φ₆ = X² - X + 1` in a commutative ring where `2 ≠ 0` and `3 ≠ 0` is a
primitive sixth root of unity. -/
theorem isPrimitiveRoot_six_of_sq_sub_add_one_eq_zero {R : Type*} [CommRing R]
    [NeZero (2 : R)] [NeZero (3 : R)] {μ : R} (h : μ ^ 2 - μ + 1 = 0) :
    IsPrimitiveRoot μ 6 := by
  have hcube : μ ^ 3 = -1 := by linear_combination (μ + 1) * h
  have hsix : μ ^ 6 = 1 := by rw [show 6 = 3 * 2 by decide, pow_mul, hcube, neg_one_sq]
  apply IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_of_pow_and_pow_div_prime hsix ?_)
  intro p hp hpd
  have hpd' : p ∣ 2 * 3 := hpd
  rcases hp.dvd_mul.mp hpd' with hp₂ | hp₃
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp₂
    intro he
    have hneg : (1 : R) = -1 := he.symm.trans hcube
    rw [eq_neg_iff_add_eq_zero, one_add_one_eq_two] at hneg
    exact NeZero.ne (2 : R) hneg
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp₃
    intro he
    have htwo : μ = 2 := by linear_combination he - h
    apply NeZero.ne (3 : R)
    linear_combination (μ + 2) * htwo.symm + he

/-- In an integral domain where `6 ≠ 0`, the primitive sixth roots of unity are the roots of
`Φ₆ = X² - X + 1`. -/
theorem isPrimitiveRoot_six_iff {R : Type*} [CommRing R] [IsDomain R] [NeZero ((6 : ℕ) : R)]
    {μ : R} : IsPrimitiveRoot μ 6 ↔ μ ^ 2 - μ + 1 = 0 := by
  rw [← isRoot_cyclotomic_iff, cyclotomic_six]
  simp only [IsRoot.def, eval_add, eval_sub, eval_pow, eval_X, eval_one]

/-- **The exceptional sixth root of unity.** In a field where `6 ≠ 0`, if `θ² = -3`, then
`(1 + θ)/2` is a primitive sixth root of unity: it is a root of `Φ₆ = X² - X + 1`. -/
theorem isPrimitiveRoot_one_add_div_two_of_sq_eq_neg_three {F : Type*} [Field F]
    [NeZero ((6 : ℕ) : F)] {θ : F} (h : θ ^ 2 = -3) :
    IsPrimitiveRoot ((1 + θ) / 2) 6 := by
  have htwo : (2 : F) ≠ 0 := by
    intro he
    apply NeZero.ne ((6 : ℕ) : F)
    calc
      ((6 : ℕ) : F) = (2 : F) * 3 := by norm_num
      _ = 0 := by simp [he]
  apply (isPrimitiveRoot_six_iff (R := F)).2
  field_simp
  linear_combination h

end TauCeti
