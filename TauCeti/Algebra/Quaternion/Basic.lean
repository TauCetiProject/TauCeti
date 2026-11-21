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
* `Quaternion.normSq_mk_div`: the norm of `(a + b i + c j + d k) / e` is
  `(a² + b² + c² + d²) / e²`.
* `Quaternion.normSq_mk_div_two`: the norm of `(a + b i + c j + d k) / 2` is
  `(a² + b² + c² + d²) / 4`, as used for quaternions with half-integer coordinates.
* `Quaternion.sq_eq_two_mul_re_smul_sub_normSq` and `Quaternion.sq_eq_two_mul_re_smul_sub_one`:
  the quadratic identity `q² = (2 * q.re) • q - (normSq q) • 1` and its specialization for unit
  quaternions.
* `Quaternion.pow_three_eq_of_sq_eq`, `Quaternion.pow_six_eq_one_of_sq_eq`, and
  `Quaternion.pow_eight_eq_one_of_sq_eq`: power identities for quaternions satisfying
  `q² = r • q - 1`.
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

/-- The norm of the quaternion `(a + b i + c j + d k) / e` is `(a² + b² + c² + d²) / e²`. -/
theorem normSq_mk_div {K : Type*} [Field K] (a b c d e : K) :
    normSq (⟨a / e, b / e, c / e, d / e⟩ : ℍ[K]) = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / e ^ 2 := by
  simp only [normSq_def', div_pow, add_div]

/-- The norm of the quaternion `(a + b i + c j + d k) / 2` is `(a² + b² + c² + d²) / 4`. -/
theorem normSq_mk_div_two {K : Type*} [Field K] (a b c d : K) :
    normSq (⟨a / 2, b / 2, c / 2, d / 2⟩ : ℍ[K]) = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4 := by
  rw [normSq_mk_div]
  norm_num

/-- Every quaternion `q` satisfies the quadratic identity `q² = (2 * q.re) • q - (normSq q) • 1`. -/
theorem sq_eq_two_mul_re_smul_sub_normSq (q : ℍ[R]) :
    q ^ 2 = (2 * q.re) • q - (normSq q : R) • 1 := by
  have h1 : q * (q + star q) = (2 * q.re) • q := by
    rw [self_add_star', mul_coe_eq_smul]
  rw [mul_add, self_mul_star, ← sq, ← one_mul (↑(normSq q) : ℍ[R]), mul_coe_eq_smul] at h1
  exact eq_sub_of_add_eq h1

/-- Every unit quaternion `q` satisfies the quadratic identity `q² = (2 * q.re) • q - 1`. -/
theorem sq_eq_two_mul_re_smul_sub_one {q : ℍ[R]} (hq : normSq q = 1) :
    q ^ 2 = (2 * q.re) • q - 1 := by
  rw [sq_eq_two_mul_re_smul_sub_normSq, hq, one_smul]

/-- Cubic identity for a quaternion satisfying `q ^ 2 = r • q - 1`. -/
theorem pow_three_eq_of_sq_eq {q : ℍ[R]} {r : R} (hq : q ^ 2 = r • q - 1) :
    q ^ 3 = (r ^ 2 - 1) • q - r • 1 := by
  calc q ^ 3 = q ^ 2 * q := pow_succ q 2
    _ = (r • q - 1) * q := by rw [hq]
    _ = r • q ^ 2 - q := by rw [sub_mul, one_mul, smul_mul_assoc, sq]
    _ = r • (r • q - 1) - q := by rw [hq]
    _ = (r ^ 2 - 1) • q - r • 1 := by
        rw [smul_sub, smul_smul, ← sq, sub_smul, one_smul]
        abel

/-- A quaternion satisfying `q ^ 2 = r • q - 1` with `r ^ 2 = 1` has `q ^ 6 = 1`. -/
theorem pow_six_eq_one_of_sq_eq {q : ℍ[R]} {r : R}
    (hq : q ^ 2 = r • q - 1) (hr : r ^ 2 = 1) : q ^ 6 = 1 := by
  have h3 : q ^ 3 = -(r • 1) := by simp [pow_three_eq_of_sq_eq hq, hr]
  calc q ^ 6 = (q ^ 3) ^ 2 := by rw [← pow_mul]
    _ = (-(r • (1 : ℍ[R]))) ^ 2 := by rw [h3]
    _ = (r ^ 2) • (1 : ℍ[R]) := by rw [neg_sq, sq, smul_mul_smul_comm, mul_one, ← sq]
    _ = 1 := by rw [hr, one_smul]

/-- A quaternion satisfying `q ^ 2 = r • q - 1` with `r ^ 2 = 2` has `q ^ 8 = 1`. -/
theorem pow_eight_eq_one_of_sq_eq {q : ℍ[R]} {r : R}
    (hq : q ^ 2 = r • q - 1) (hr : r ^ 2 = 2) : q ^ 8 = 1 := by
  have h3 : q ^ 3 = q - r • 1 := by norm_num [pow_three_eq_of_sq_eq hq, hr]
  have h4 : q ^ 4 = -1 := by
    calc q ^ 4 = q ^ 3 * q := pow_succ q 3
      _ = (q - r • 1) * q := by rw [h3]
      _ = q ^ 2 - r • q := by rw [sub_mul, smul_mul_assoc, one_mul, sq]
      _ = -1 := by rw [hq]; abel
  calc q ^ 8 = (q ^ 4) ^ 2 := by rw [← pow_mul]
    _ = (-1 : ℍ[R]) ^ 2 := by rw [h4]
    _ = 1 := neg_one_sq

end Quaternion
