/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.ReflectionGroup
import Mathlib.NumberTheory.Real.Irrational

/-!
# Checks for reflection groups

The side directions of a table are written `exp(kθ)` for integers `k`; the squares of their
quotients are then the powers of `exp(2θ)`, which generate the rotation subgroup
(`TauCeti.Billiard.rotationSubgroup_reflectionGroup_exp`).

* **Unit square** (directions `1` and `i = exp(π/2)`): the reflection group `{±1, ±conj}` has
  order `4`, `N = 2` (`natCard_reflectionGroup_square`).
* **Equilateral triangle** (directions `1`, `exp(π/3)`, `exp(2π/3)`): order `6`, `N = 3`
  (`natCard_reflectionGroup_equilateral`).
* **A triangle with an angle `π/√2`** (two sides of directions `1` and `exp(π/√2)`): the
  reflection group is infinite (`infinite_reflectionGroup_pi_div_sqrt_two`), since the rotation
  by `exp(√2 π)` has infinite order.
-/

open Real Set

public noncomputable section

namespace TauCeti.Examples.ReflectionGroup

open TauCeti.Billiard TauCeti.Complex

/-- The directions `1` and `i` of the sides of the unit square. -/
def squareDirections : Set Circle :=
  (fun k : ℤ => Circle.exp (k * (π / 2))) '' {0, 1}

/-- **Unit square**: the reflection group has order `4`. -/
theorem natCard_reflectionGroup_square : Nat.card (reflectionGroup squareDirections) = 4 := by
  have h : orderOf (Circle.exp (2 * (π / 2))) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact_mod_cast Circle.exp_two_mul_pi_div_pow 2
    · rw [mul_div_cancel₀ _ two_ne_zero]; exact Circle.exp_pi_ne_one
  rw [squareDirections, natCard_reflectionGroup_exp _ (by simp) (by simp)
    (orderOf_pos_iff.1 (by rw [h]; norm_num)), h]

/-- The directions `1`, `exp(π/3)`, `exp(2π/3)` of the sides of an equilateral triangle. -/
def equilateralDirections : Set Circle :=
  (fun k : ℤ => Circle.exp (k * (π / 3))) '' {0, 1, 2}

/-- **Equilateral triangle**: the reflection group has order `6`. -/
theorem natCard_reflectionGroup_equilateral :
    Nat.card (reflectionGroup equilateralDirections) = 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : orderOf (Circle.exp (2 * (π / 3))) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · exact_mod_cast Circle.exp_two_mul_pi_div_pow 3
    · rw [Ne, Circle.exp_eq_one]
      rintro ⟨n, hn⟩
      have : (3 * n : ℝ) = 1 := by nlinarith [pi_pos]
      have : 3 * n = 1 := by exact_mod_cast this
      omega
  rw [equilateralDirections, natCard_reflectionGroup_exp _ (by simp) (by simp)
    (orderOf_pos_iff.1 (by rw [h]; norm_num)), h]

/-- The directions `1` and `exp(π/√2)` of two sides of a triangle with an angle `π/√2`. -/
def irrationalDirections : Set Circle :=
  (fun k : ℤ => Circle.exp (k * (π / √2))) '' {0, 1}

/-- **A triangle with an angle `π/√2`**: the reflection group is infinite. -/
theorem infinite_reflectionGroup_pi_div_sqrt_two :
    Infinite (reflectionGroup irrationalDirections) := by
  rw [← not_finite_iff_infinite, irrationalDirections,
    finite_iff_finite_rotationSubgroup,
    rotationSubgroup_reflectionGroup_exp _ (by simp) (by simp)]
  intro hfin
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 (finite_zpowers.1 hfin)
  rw [← Circle.exp_natCast_mul, Circle.exp_eq_one] at hpow
  obtain ⟨m, hm⟩ := hpow
  have key : (n : ℝ) = m * √2 := by
    have h2 : (n : ℝ) * (2 * (π / √2)) * √2 = m * (2 * π) * √2 := by rw [hm]
    field_simp at h2
    linear_combination h2
  have hm0 : (m : ℝ) ≠ 0 := by
    rintro h
    rw [h, zero_mul, Nat.cast_eq_zero] at key
    exact hn.ne' key
  refine irrational_sqrt_two.ne_rational n m ?_
  rw [Int.cast_natCast, key]
  field_simp

end TauCeti.Examples.ReflectionGroup
