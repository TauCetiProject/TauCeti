/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.EqOne

/-!
# Quadratic and rational identities relating `exp (2 z i)` and `2 cos z`

Writing `μ = exp (z i)` so that `μ + μ⁻¹ = 2 cos z` (`Complex.two_cos`), the square `ζ = μ ^ 2 =
exp (2 z i)` satisfies `(1 + ζ) ^ 2 / ζ = (2 cos z) ^ 2` and both `ζ` and `ζ⁻¹` satisfy the
quadratic equation `w ^ 2 + (2 - (2 cos z) ^ 2) * w + 1 = 0`.

## Main results

* `Complex.one_add_exp_two_mul_mul_I_sq_div`:
  `(1 + exp (2 * z * I)) ^ 2 / exp (2 * z * I) = (2 * cos z) ^ 2`.
* `Complex.norm_one_add_exp_two_mul_mul_I_sq_div`:
  `‖(1 + exp (2 * x * I)) ^ 2 / exp (2 * x * I)‖ = (2 * Real.cos x) ^ 2` for `x : ℝ`.
* `Complex.exp_two_mul_mul_I_sq_add_sub_mul_add_one`:
  `exp (2 * z * I) ^ 2 + (2 - (2 * cos z) ^ 2) * exp (2 * z * I) + 1 = 0`.
* `Complex.inv_exp_two_mul_mul_I_sq_add_sub_mul_add_one`:
  `(exp (2 * z * I))⁻¹ ^ 2 + (2 - (2 * cos z) ^ 2) * (exp (2 * z * I))⁻¹ + 1 = 0`.
* `Complex.eq_pi_div_of_exp_ofReal_mul_I_pow_eq_one_of_cos_le`:
  if `0 < θ ≤ π`, `exp (θ * I) ^ (2 * n) = 1`, and `Real.cos (π / n) ≤ Real.cos θ`, then
  `θ = π / n`.
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

/-- For `x : ℝ`, `‖(1 + exp (2 * x * I)) ^ 2 / exp (2 * x * I)‖ = (2 * Real.cos x) ^ 2`. -/
theorem norm_one_add_exp_two_mul_mul_I_sq_div (x : ℝ) :
    ‖(1 + exp (2 * (x : ℂ) * I)) ^ 2 / exp (2 * (x : ℂ) * I)‖ = (2 * Real.cos x) ^ 2 := by
  rw [one_add_exp_two_mul_mul_I_sq_div, ← ofReal_cos]
  norm_cast
  exact Real.norm_of_nonneg (sq_nonneg _)

/-- For `z : ℂ`, `exp (2 * z * I)` is a root of `w ^ 2 + (2 - (2 * cos z) ^ 2) * w + 1 = 0`. -/
theorem exp_two_mul_mul_I_sq_add_sub_mul_add_one (z : ℂ) :
    exp (2 * z * I) ^ 2 + (2 - (2 * cos z) ^ 2) * exp (2 * z * I) + 1 = 0 := by
  set μ : ℂ := exp (z * I)
  have hμ_ne : μ ≠ 0 := exp_ne_zero _
  have hμ_sum : μ + μ⁻¹ = 2 * cos z := by
    dsimp only [μ]
    rw [← exp_neg, ← neg_mul, ← two_cos]
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

/-- An angle `θ ∈ (0, π]` with `exp (θ * I) ^ (2 * n) = 1` (`0 < n`) and
`Real.cos (π / n) ≤ Real.cos θ` equals `π / n`. -/
theorem eq_pi_div_of_exp_ofReal_mul_I_pow_eq_one_of_cos_le {θ : ℝ} {n : ℕ}
    (hθ0 : 0 < θ) (hθpi : θ ≤ Real.pi) (hn : 0 < n)
    (hpow : exp ((θ : ℂ) * I) ^ (2 * n) = 1) (hcos : Real.cos (Real.pi / n) ≤ Real.cos θ) :
    θ = Real.pi / n := by
  have hpi_le : Real.pi / n ≤ θ := by
    have h2 := two_mul_pi_div_le_of_exp_ofReal_mul_I_pow_eq_one hθ0 (by positivity : 0 < 2 * n) hpow
    rwa [Nat.cast_mul, Nat.cast_ofNat, mul_div_mul_left _ _ two_ne_zero] at h2
  have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi_mem : Real.pi / n ∈ Set.Icc 0 Real.pi :=
    ⟨div_nonneg Real.pi_pos.le (by linarith), div_le_self Real.pi_pos.le hn_real⟩
  have hcos_eq : Real.cos θ = Real.cos (Real.pi / n) :=
    le_antisymm (Real.strictAntiOn_cos.antitoneOn hpi_mem ⟨hθ0.le, hθpi⟩ hpi_le) hcos
  exact Real.strictAntiOn_cos.injOn ⟨hθ0.le, hθpi⟩ hpi_mem hcos_eq

end Complex
