/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The sinc function: nonnegativity and the scaled function `t ↦ t sinc (ω t)`

`sinc` is nonnegative on `[-π, π]`, complementing Mathlib's `Real.sinc_pos` on `(-π, π)`.

Since `cos (π x / 2)` vanishes at `x = ±1`, `sin (π x / 2)² - 1 = -cos (π x / 2)²` is the product
of `x² - 1` with the continuous function `(π / 2)² sinc (π (1 - x) / 2) sinc (π (1 + x) / 2)`
(`Real.mul_self_sin_pi_mul_div_two_sub_one`).

For `ω ≠ 0` the function `t ↦ t sinc (ω t)` is `t ↦ sin (ω t) / ω`, and for `ω = 0` it is the
identity. Either way its derivative is `t ↦ cos (ω t)`, so it is the solution of
`f'' = -ω² f` with `f 0 = 0` and `f' 0 = 1`, uniformly in the frequency `ω`, including the
degenerate frequency `0`.
-/

public section

namespace Real

/-- `x sinc x = sin x` for every real `x`, including `x = 0`. -/
@[simp]
theorem mul_sinc (x : ℝ) : x * sinc x = sin x := by
  simpa [sinc_eq_dslope] using sub_smul_dslope sin 0 x

/-- For `ω ≠ 0`, `t sinc (ω t) = sin (ω t) / ω`. -/
theorem mul_sinc_mul_of_ne_zero {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    t * sinc (ω * t) = sin (ω * t) / ω := by
  rw [eq_div_iff hω, ← mul_sinc]
  ring

/-- The derivative of `t ↦ t sinc (ω t)` is `cos (ω t)`, for every frequency `ω`. -/
theorem hasDerivAt_mul_sinc_mul (ω t : ℝ) :
    HasDerivAt (fun s ↦ s * sinc (ω * s)) (cos (ω * t)) t := by
  rcases eq_or_ne ω 0 with rfl | hω
  · simpa using hasDerivAt_id' t
  · simp_rw [mul_sinc_mul_of_ne_zero hω]
    convert ((hasDerivAt_id' t).const_mul ω).sin.div_const ω using 1
    field_simp

/-- `sin (π x / 2)² - 1 = (π / 2)² sinc (π (1 - x) / 2) sinc (π (1 + x) / 2) (x² - 1)`: the defect
`sin (π x / 2)² - 1` is a continuous function of `x` times `x² - 1`, because `cos (π x / 2)` is
both `sin (π (1 - x) / 2)` and `sin (π (1 + x) / 2)`. -/
theorem mul_self_sin_pi_mul_div_two_sub_one (x : ℝ) :
    sin (π * x / 2) * sin (π * x / 2) - 1 =
      (π / 2) ^ 2 * sinc (π * (1 - x) / 2) * sinc (π * (1 + x) / 2) * (x * x - 1) := by
  have h₁ : π * (1 - x) / 2 * sinc (π * (1 - x) / 2) = cos (π * x / 2) := by
    rw [mul_sinc, ← sin_pi_div_two_sub]; ring_nf
  have h₂ : π * (1 + x) / 2 * sinc (π * (1 + x) / 2) = cos (π * x / 2) := by
    rw [mul_sinc, ← sin_add_pi_div_two]; ring_nf
  linear_combination sin_sq_add_cos_sq (π * x / 2) +
    π * (1 + x) / 2 * sinc (π * (1 + x) / 2) * h₁ + cos (π * x / 2) * h₂

/-- The function `sinc` is nonnegative on `[-π, π]`. -/
theorem sinc_nonneg {x : ℝ} (hx : |x| ≤ π) : 0 ≤ sinc x := by
  wlog hx₀ : 0 ≤ x generalizing x
  · rw [← sinc_neg]
    exact this (by rwa [abs_neg]) (by linarith)
  rcases hx₀.eq_or_lt with rfl | hx₀
  · simp
  rw [sinc_of_ne_zero hx₀.ne']
  exact div_nonneg (sin_nonneg_of_nonneg_of_le_pi hx₀.le (abs_le.1 hx).2) hx₀.le

end Real
