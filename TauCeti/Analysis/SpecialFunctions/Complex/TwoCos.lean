/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Quadratic and rational identities relating `exp (2 z i)` and `2 cos z`

Writing `μ = exp (z i)` so that `μ + μ⁻¹ = 2 cos z` (`Complex.two_cos`), the square `ζ = μ ^ 2 =
exp (2 z i)` satisfies `(1 + ζ) ^ 2 / ζ = (2 cos z) ^ 2` and both `ζ` and `ζ⁻¹` satisfy the
quadratic equation `w ^ 2 + (2 - (2 cos z) ^ 2) * w + 1 = 0`.

## Main results

* `Complex.one_add_exp_two_mul_mul_I_sq_div`:
  `(1 + exp (2 * z * I)) ^ 2 / exp (2 * z * I) = (2 * cos z) ^ 2`.
* `Complex.exp_two_mul_mul_I_sq_add_sub_mul_add_one`:
  `exp (2 * z * I) ^ 2 + (2 - (2 * cos z) ^ 2) * exp (2 * z * I) + 1 = 0`.
* `Complex.inv_exp_two_mul_mul_I_sq_add_sub_mul_add_one`:
  `(exp (2 * z * I))⁻¹ ^ 2 + (2 - (2 * cos z) ^ 2) * (exp (2 * z * I))⁻¹ + 1 = 0`.
-/

public section

namespace Complex

/-- For `z : ℂ`, `(1 + exp (2 * z * I)) ^ 2 / exp (2 * z * I) = (2 * cos z) ^ 2`. -/
theorem one_add_exp_two_mul_mul_I_sq_div (z : ℂ) :
    (1 + exp (2 * z * I)) ^ 2 / exp (2 * z * I) = (2 * cos z) ^ 2 := by
  set ξ : ℂ := exp (z * I)
  have hω : exp (2 * z * I) = ξ ^ 2 := by
    simp only [ξ, sq, ← exp_add]
    congr 1
    ring
  have hdiv : (1 + ξ ^ 2) ^ 2 / ξ ^ 2 = (ξ + ξ⁻¹) ^ 2 := by
    field_simp [exp_ne_zero _]
    ring
  rw [hω, hdiv]
  dsimp only [ξ]
  rw [← exp_neg, ← neg_mul, ← two_cos]

/-- For `z : ℂ`, `exp (2 * z * I)` is a root of `w ^ 2 + (2 - (2 * cos z) ^ 2) * w + 1 = 0`. -/
theorem exp_two_mul_mul_I_sq_add_sub_mul_add_one (z : ℂ) :
    exp (2 * z * I) ^ 2 + (2 - (2 * cos z) ^ 2) * exp (2 * z * I) + 1 = 0 := by
  set μ : ℂ := exp (z * I)
  have hμ_ne : μ ≠ 0 := exp_ne_zero _
  have hμ_sum : μ + μ⁻¹ = 2 * cos z := by
    rw [show μ⁻¹ = exp (-z * I) by simp [μ, ← exp_neg, neg_mul], ← two_cos]
  have hζ_eq : exp (2 * z * I) = μ ^ 2 := by
    simp only [μ, sq, ← exp_add]
    congr 1
    ring
  have hζ_ne : μ ^ 2 ≠ 0 := pow_ne_zero 2 hμ_ne
  have hsum : μ ^ 2 + (μ ^ 2)⁻¹ = (2 * cos z) ^ 2 - 2 := by
    have h1 : μ ^ 2 + (μ⁻¹) ^ 2 = (μ + μ⁻¹) ^ 2 - 2 := by
      field_simp [hμ_ne]
      ring
    rw [hμ_sum] at h1
    simpa [inv_pow] using h1
  rw [hζ_eq]
  have h := congrArg (· * μ ^ 2) hsum
  rw [add_mul, inv_mul_cancel₀ hζ_ne, ← sq] at h
  linear_combination h

/-- For `z : ℂ`, `(exp (2 * z * I))⁻¹` is a root of
`w ^ 2 + (2 - (2 * cos z) ^ 2) * w + 1 = 0`. -/
theorem inv_exp_two_mul_mul_I_sq_add_sub_mul_add_one (z : ℂ) :
    (exp (2 * z * I))⁻¹ ^ 2 + (2 - (2 * cos z) ^ 2) * (exp (2 * z * I))⁻¹ + 1 = 0 := by
  have hne : exp (2 * z * I) ≠ 0 := exp_ne_zero _
  have h := exp_two_mul_mul_I_sq_add_sub_mul_add_one z
  field_simp
  linear_combination h

end Complex
