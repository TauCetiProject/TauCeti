/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The sinc function: nonnegativity and the scaled function `t ↦ t sinc (ω t)`

`sinc` is nonnegative on `[-π, π]`, complementing Mathlib's `Real.sinc_pos` on `(-π, π)`. Near
zero it is quadratically close to one, `|sinc x - 1| ≤ x² / 6`, and it factors the remainder of
the cosine, `1 - cos x = (x² / 2) sinc (x / 2)²`. Consequently `sinc x` is at least `23 / 24`
while `|x| ≤ 1 / 2` (`TauCeti.le_sinc_of_abs_le_half`).

For `ω ≠ 0` the function `t ↦ t sinc (ω t)` is `t ↦ sin (ω t) / ω`, and for `ω = 0` it is the
identity. Either way its derivative is `t ↦ cos (ω t)`, so it is the solution of
`f'' = -ω² f` with `f 0 = 0` and `f' 0 = 1`, uniformly in the frequency `ω`, including the
degenerate frequency `0`. Together with `t ↦ cos (ω t)` it satisfies the subtraction formulas of
`sin` and `cos` (`Real.sub_mul_sinc_sub_mul`, `Real.cos_sub_mul`), again for every `ω`.
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

/-- The subtraction formula for `t ↦ t sinc (t a)`, which is `sin (t a) / a` for `a ≠ 0`:
`(t - s) sinc ((t - s) a) = t sinc (t a) cos (s a) - cos (t a) s sinc (s a)`. -/
theorem sub_mul_sinc_sub_mul (a s t : ℝ) :
    (t - s) * sinc ((t - s) * a) =
      t * sinc (t * a) * cos (s * a) - cos (t * a) * (s * sinc (s * a)) := by
  rcases eq_or_ne a 0 with rfl | h
  · simp
  · rw [mul_comm (t - s) a, mul_comm t a, mul_comm s a, mul_sinc_mul_of_ne_zero h,
      mul_sinc_mul_of_ne_zero h, mul_sinc_mul_of_ne_zero h, mul_sub, sin_sub]
    ring

/-- The subtraction formula for `cos (t a)`, in terms of `t ↦ t sinc (t a)`:
`cos ((t - s) a) = cos (s a) cos (t a) + a² s sinc (s a) t sinc (t a)`. -/
theorem cos_sub_mul (a s t : ℝ) :
    cos ((t - s) * a) =
      cos (s * a) * cos (t * a) + s * sinc (s * a) * (t * sinc (t * a)) * a ^ 2 := by
  rw [sub_mul, cos_sub, ← mul_sinc (s * a), ← mul_sinc (t * a)]
  ring

/-- The function `sinc` is nonnegative on `[-π, π]`. -/
theorem sinc_nonneg {x : ℝ} (hx : |x| ≤ π) : 0 ≤ sinc x := by
  wlog hx₀ : 0 ≤ x generalizing x
  · rw [← sinc_neg]
    exact this (by rwa [abs_neg]) (by linarith)
  rcases hx₀.eq_or_lt with rfl | hx₀
  · simp
  rw [sinc_of_ne_zero hx₀.ne']
  exact div_nonneg (sin_nonneg_of_nonneg_of_le_pi hx₀.le (abs_le.1 hx).2) hx₀.le

/-- `|sinc x - 1| ≤ x² / 6` for every real `x`. -/
theorem abs_sinc_sub_one_le (x : ℝ) : |sinc x - 1| ≤ x ^ 2 / 6 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : 0 < |x| := abs_pos.2 hx
  rw [sinc_of_ne_zero hx, div_sub_one hx, abs_div, div_le_iff₀ hx', abs_sub_comm]
  calc |x - sin x| ≤ |x| ^ 3 / 6 := abs_sub_sin_le x
    _ = x ^ 2 / 6 * |x| := by rw [← sq_abs x]; ring

/-- `1 - cos x = (x² / 2) sinc (x / 2)²` for every real `x`. -/
theorem one_sub_cos_eq_sq_div_two_mul_sinc_sq (x : ℝ) :
    1 - cos x = x ^ 2 / 2 * sinc (x / 2) ^ 2 := by
  have h₁ := cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h₁
  have h₂ := sin_sq_add_cos_sq (x / 2)
  rw [← mul_sinc (x / 2)] at h₂
  linear_combination -h₁ - 2 * h₂

end Real

namespace TauCeti

open Real

/-- On `[-1 / 2, 1 / 2]`, `sinc x` is at least `23 / 24`, since `|sinc x - 1| ≤ x² / 6`. -/
theorem le_sinc_of_abs_le_half {x : ℝ} (hx : |x| ≤ 1 / 2) : 23 / 24 ≤ sinc x := by
  have hsq : x ^ 2 ≤ (1 / 2) ^ 2 := sq_le_sq.2 (hx.trans (le_abs_self _))
  linarith [(abs_le.1 (abs_sinc_sub_one_le x)).1]

end TauCeti
