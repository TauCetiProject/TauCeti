/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The scaled sinc function `t ↦ t sinc (ω t)`

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

/-- The double-angle formula `sinc (2x) = sinc x * cos x`, including at `x = 0`. -/
theorem sinc_two_mul (x : ℝ) : sinc (2 * x) = sinc x * cos x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [sinc_of_ne_zero (mul_ne_zero two_ne_zero hx), sinc_of_ne_zero hx, sin_two_mul]
  field_simp

/-- The bound `sinc² x ≤ 2 / (1 + x²)`, from `sinc² ≤ 1` and `x² sinc² x = sin² x ≤ 1`. -/
theorem sinc_sq_le_two_div_one_add_sq (x : ℝ) : sinc x ^ 2 ≤ 2 / (1 + x ^ 2) := by
  have h1 : sinc x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (abs_sinc_le_one x)
  have h2 : (x * sinc x) ^ 2 ≤ 1 := by rw [mul_sinc]; exact sin_sq_le_one x
  rw [le_div_iff₀ (by positivity)]
  nlinarith

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

end Real
