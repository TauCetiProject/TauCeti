/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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
* `Quaternion.exists_pure_neg_conj`: pure imaginary `r` admits nonzero pure `q` with
  `star q * r * q = -(normSq q • r)`.
* `Quaternion.linearMap_apply_eq_map_one_mul_re_of_cyclic`, `Quaternion.re_mul_comm`,
  `Quaternion.re_mul_star_pos`: cyclic real functionals, real-part commutativity, and positivity
  of `(a * star a).re`.
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

/-- Every pure imaginary quaternion `r` admits a nonzero pure imaginary quaternion `q` satisfying
`star q * r * q = -(q.normSq • r)`. -/
theorem exists_pure_neg_conj (r : ℍ[ℝ]) (hr : r.re = 0) :
    ∃ q : ℍ[ℝ], q ≠ 0 ∧ q.re = 0 ∧ star q * r * q = -(normSq q • r) := by
  by_cases h : r.imI = 0 ∧ r.imJ = 0
  · refine ⟨⟨0, 1, 0, 0⟩, fun h0 ↦ by simpa using congrArg QuaternionAlgebra.imI h0, rfl, ?_⟩
    ext <;> simp [normSq_def', hr, h.1, h.2]
  · refine ⟨⟨0, -r.imJ, r.imI, 0⟩, fun h0 ↦ h ⟨congrArg QuaternionAlgebra.imJ h0,
      neg_eq_zero.mp (congrArg QuaternionAlgebra.imI h0)⟩, rfl, ?_⟩
    ext <;> simp [normSq_def', hr] <;> ring

/-- The real part of a product of Hamilton quaternions is commutative. -/
theorem re_mul_comm (a b : ℍ[R]) : (a * b).re = (b * a).re := by simp only [re_mul]; ring

/-- Every cyclic `ℝ`-linear functional on `ℍ[ℝ]` is a scalar multiple of
`QuaternionAlgebra.re`. -/
theorem linearMap_apply_eq_map_one_mul_re_of_cyclic (τ : ℍ[ℝ] →ₗ[ℝ] ℝ)
    (hcyc : ∀ a b : ℍ[ℝ], τ (a * b) = τ (b * a)) (q : ℍ[ℝ]) : τ q = τ 1 * q.re := by
  let qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩; let qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩; let qk : ℍ[ℝ] := ⟨0, 0, 0, 1⟩
  have hzero (x y z : ℍ[ℝ]) (h : (2 : ℝ) • x = y * z - z * y) : τ x = 0 := by
    have h0 : 2 * τ x = 0 := by simpa [map_smul, smul_eq_mul, map_sub, hcyc y z] using congrArg τ h
    linarith
  conv_lhs => rw [show q = q.re • 1 + q.imI • qi + q.imJ • qj + q.imK • qk by
    ext <;> simp [qi, qj, qk]]
  simp [hzero qi qj qk (by ext <;> norm_num [qi, qj, qk]),
    hzero qj qk qi (by ext <;> norm_num [qi, qj, qk]),
    hzero qk qi qj (by ext <;> norm_num [qi, qj, qk]), mul_comm]

/-- For a nonzero real quaternion `a`, `(a * star a).re > 0`. -/
theorem re_mul_star_pos {a : ℍ[ℝ]} (ha : a ≠ 0) : 0 < (a * star a).re := by
  rw [self_mul_star, re_coe]; exact lt_of_not_ge fun h ↦ ha (normSq_le_zero.mp h)

end Quaternion
