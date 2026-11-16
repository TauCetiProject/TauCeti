/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.LinearCombination

/-!
# Basic facts about the Hamilton quaternions

This file collects elementary facts about the Hamilton quaternions `ℍ[R]`, and more generally the
quaternion algebras `ℍ[R,c₁,c₂,c₃]`, over a commutative ring `R` that depend on nothing beyond
Mathlib's `Mathlib.Algebra.Quaternion`.

## Main results

* `QuaternionAlgebra.instStarModule`: scalars from a ring with trivial star commute with the
  quaternion conjugation, so for example `ℍ` is a real star module.
* `Quaternion.isLeftRegular_two`: if `ℍ[R]` has no zero divisors then `2` is left regular in `R`,
  because the quaternion `r + r i` squares to `2 r² i`.
* `Quaternion.sq_eq_two_re_smul_sub_normSq` and `Quaternion.pow_three_eq_smul_sub`:
  Cayley–Hamilton identities `q² = (2 q.re) • q - normSq q` and
  `q³ = ((2 q.re)² - normSq q) • q - 2 q.re * normSq q`, together with
  `Quaternion.pow_four_eq_one_of_normSq_eq_one_of_re_eq_zero`,
  `Quaternion.pow_six_eq_one_of_normSq_eq_one_of_two_mul_re_sq_eq_one` and
  `Quaternion.pow_eight_eq_one_of_normSq_eq_one_of_two_mul_re_sq_eq_two` giving `q⁴ = 1`,
  `q⁶ = 1` and `q⁸ = 1` for quaternions of norm one with `q.re = 0`, `(2 q.re)² = 1` and
  `(2 q.re)² = 2`.
* `Quaternion.normSq_mk_div` and `Quaternion.normSq_mk_div_two`: the norm of
  `(a + b i + c j + d k) / s` is `(a² + b² + c² + d²) / s²`.
-/

public section

open scoped Quaternion

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R] [Star R] [TrivialStar R] {c₁ c₂ c₃ : R}

/-- Quaternion conjugation commutes with scalars from a ring with trivial star. -/
instance : StarModule R ℍ[R,c₁,c₂,c₃] where
  star_smul r a := by rw [QuaternionAlgebra.star_smul, star_trivial r]

end QuaternionAlgebra

namespace Quaternion

variable {R : Type*} [CommRing R]

/-- If `ℍ[R]` has no zero divisors then `2` is left regular in `R`: for `2 * r = 0` the quaternion
`r + r i` squares to `2 r² i = 0`. -/
theorem isLeftRegular_two [NoZeroDivisors ℍ[R]] : IsLeftRegular (2 : R) := by
  intro a b (h : 2 * a = 2 * b)
  have hsq : (⟨a - b, a - b, 0, 0⟩ : ℍ[R]) * ⟨a - b, a - b, 0, 0⟩ = 0 := by
    ext <;> simp only [re_mul, imI_mul, imJ_mul, imK_mul, re_zero, imI_zero, imJ_zero, imK_zero]
    · ring
    · linear_combination (a - b) * h
    all_goals ring
  exact sub_eq_zero.mp (congrArg QuaternionAlgebra.re (mul_self_eq_zero.mp hsq))

/-- **Cayley–Hamilton for Hamilton quaternions**: `q² = (2 q.re) • q - normSq q`. -/
theorem sq_eq_two_re_smul_sub_normSq (q : ℍ[R]) :
    q ^ 2 = (2 * q.re) • q - normSq q := by
  ext <;> simp [sq, normSq_def'] <;> ring

/-- Cube of a Hamilton quaternion in terms of its real part and norm:
`q³ = ((2 q.re)² - normSq q) • q - 2 q.re * normSq q`. -/
theorem pow_three_eq_smul_sub (q : ℍ[R]) :
    q ^ 3 = ((2 * q.re) ^ 2 - normSq q) • q - ↑(2 * q.re * normSq q) := by
  ext <;> simp [pow_succ, normSq_def'] <;> ring

/-- A Hamilton quaternion of norm one with vanishing real part satisfies `q⁴ = 1`. -/
theorem pow_four_eq_one_of_normSq_eq_one_of_re_eq_zero {q : ℍ[R]}
    (hq : normSq q = 1) (hre : q.re = 0) : q ^ 4 = 1 := by
  have hq2 : q ^ 2 = -1 := by
    simpa [hq, hre] using sq_eq_two_re_smul_sub_normSq q
  calc q ^ 4 = (q ^ 2) ^ 2 := by rw [← pow_mul]
    _ = (-1) ^ 2 := by rw [hq2]
    _ = 1 := by rw [neg_one_sq]

/-- A Hamilton quaternion of norm one with `(2 q.re)² = 1` satisfies `q⁶ = 1`. -/
theorem pow_six_eq_one_of_normSq_eq_one_of_two_mul_re_sq_eq_one {q : ℍ[R]}
    (hq : normSq q = 1) (hre : (2 * q.re) ^ 2 = 1) : q ^ 6 = 1 := by
  have hq3 : q ^ 3 = -↑(2 * q.re) := by
    simpa [hq, hre] using pow_three_eq_smul_sub q
  calc q ^ 6 = (q ^ 3) ^ 2 := by rw [← pow_mul]
    _ = (-↑(2 * q.re)) ^ 2 := by rw [hq3]
    _ = 1 := by rw [neg_sq, ← coe_pow, hre, coe_one]

/-- A Hamilton quaternion of norm one with `(2 q.re)² = 2` satisfies `q⁸ = 1`. -/
theorem pow_eight_eq_one_of_normSq_eq_one_of_two_mul_re_sq_eq_two {q : ℍ[R]}
    (hq : normSq q = 1) (hre : (2 * q.re) ^ 2 = 2) : q ^ 8 = 1 := by
  have hsq : q ^ 2 = (2 * q.re) • q - 1 := by
    simpa [hq] using sq_eq_two_re_smul_sub_normSq q
  have hq3 : q ^ 3 = q - ↑(2 * q.re) := by
    have h21 : (2 : R) - 1 = 1 := by ring
    have h := pow_three_eq_smul_sub q
    rwa [hq, hre, h21, one_smul, mul_one] at h
  have hq4 : q ^ 4 = -1 := by
    calc q ^ 4 = q * q ^ 3 := by rw [pow_succ']
      _ = q * (q - ↑(2 * q.re)) := by rw [hq3]
      _ = q ^ 2 - (2 * q.re) • q := by rw [mul_sub, ← sq, ← coe_commutes, coe_mul_eq_smul]
      _ = -1 := by rw [hsq, sub_right_comm, sub_self, zero_sub]
  calc q ^ 8 = (q ^ 4) ^ 2 := by rw [← pow_mul]
    _ = (-1) ^ 2 := by rw [hq4]
    _ = 1 := by rw [neg_one_sq]

/-- The norm of the quaternion `(a + b i + c j + d k) / s` is `(a² + b² + c² + d²) / s²`. -/
theorem normSq_mk_div {K : Type*} [Field K] (a b c d s : K) :
    normSq (⟨a / s, b / s, c / s, d / s⟩ : ℍ[K]) = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / s ^ 2 := by
  simp only [normSq_def', div_pow, add_div]

/-- The norm of the quaternion `(a + b i + c j + d k) / 2` is `(a² + b² + c² + d²) / 4`. -/
theorem normSq_mk_div_two {K : Type*} [Field K] (a b c d : K) :
    normSq (⟨a / 2, b / 2, c / 2, d / 2⟩ : ℍ[K]) = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4 := by
  rw [normSq_mk_div]
  norm_num

end Quaternion
