/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The cosine transform of the triangle function

The triangle function `θ ↦ (1 - |θ|)` on `[-1, 1]` has cosine transform
`∫_{-1}^{1} (1 - |θ|) cos (x θ) dθ = sinc (x / 2)²`, the Fejér kernel on the real line.
The right side is nonnegative, equals one at `x = 0`, and is at least `(23 / 24)²` for
`|x| ≤ 1`. Bounding the indicator of an interval by this kernel turns a probability into an
integral of a characteristic function, as in Esseen's concentration inequality.
-/

public section

open Real

namespace TauCeti

/-- On `[0, 1]`, `∫ (1 - θ) cos (x θ) dθ = (1 - cos x) / x²` for `x ≠ 0`; we state it as
half the squared `sinc`, which also covers `x = 0`. -/
private theorem integral_zero_one_one_sub_mul_cos_mul (x : ℝ) :
    ∫ θ in (0 : ℝ)..1, (1 - θ) * cos (x * θ) = sinc (x / 2) ^ 2 / 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [zero_mul, cos_zero, mul_one, zero_div, sinc_zero]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    norm_num [integral_id]
  -- the antiderivative `(1 - θ) sin (x θ) / x + (1 - cos (x θ)) / x²`
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun θ ↦ (1 - θ) * (sin (x * θ) / x) + (1 - cos (x * θ)) / x ^ 2)
        ((1 - θ) * cos (x * θ)) θ := by
    intro θ _
    have hs : HasDerivAt (fun θ ↦ sin (x * θ)) (cos (x * θ) * x) θ := by
      simpa using ((hasDerivAt_id θ).const_mul x).sin
    have hc : HasDerivAt (fun θ ↦ cos (x * θ)) (-sin (x * θ) * x) θ := by
      simpa using ((hasDerivAt_id θ).const_mul x).cos
    refine ((((hasDerivAt_id' θ).const_sub 1).mul (hs.div_const x)).add
      ((hc.const_sub 1).div_const (x ^ 2))).congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [sub_self, zero_mul, zero_add, mul_one, mul_zero, sin_zero, zero_div, cos_zero,
    add_zero, sub_zero]
  rw [one_sub_cos_eq_sq_div_two_mul_sinc_sq x]
  field_simp

/-- **The cosine transform of the triangle function**: for every real `x`,
`∫_{-1}^{1} (1 - |θ|) cos (x θ) dθ = sinc (x / 2)²`. -/
theorem integral_one_sub_abs_mul_cos_mul (x : ℝ) :
    ∫ θ in (-1 : ℝ)..1, (1 - |θ|) * cos (x * θ) = sinc (x / 2) ^ 2 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ ↦ (1 - |θ|) * cos (x * θ))
      MeasureTheory.volume a b := fun a b ↦ by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-1) 0) (hint 0 1)]
  have hneg : ∫ θ in (-1 : ℝ)..0, (1 - |θ|) * cos (x * θ) =
      ∫ θ in (0 : ℝ)..1, (1 - |θ|) * cos (x * θ) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := 1)
      (fun θ : ℝ ↦ (1 - |θ|) * cos (x * θ))
    simp only [neg_zero, abs_neg, mul_neg, cos_neg] at h
    exact h.symm
  have hpos : ∫ θ in (0 : ℝ)..1, (1 - |θ|) * cos (x * θ) =
      ∫ θ in (0 : ℝ)..1, (1 - θ) * cos (x * θ) := by
    refine intervalIntegral.integral_congr fun θ hθ ↦ ?_
    rw [Set.uIcc_of_le zero_le_one] at hθ
    simp [abs_of_nonneg hθ.1]
  rw [hneg, hpos, integral_zero_one_one_sub_mul_cos_mul]
  ring

/-- The Fejér kernel `sinc (x / 2)²` is at least `(23 / 24)²` on `[-1, 1]`. -/
theorem sq_le_sinc_div_two_sq {x : ℝ} (hx : |x| ≤ 1) :
    (23 / 24 : ℝ) ^ 2 ≤ sinc (x / 2) ^ 2 := by
  have h := abs_sinc_sub_one_le (x / 2)
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  have hlow : 23 / 24 ≤ sinc (x / 2) := by
    have := (abs_le.1 h).1
    nlinarith
  exact pow_le_pow_left₀ (by norm_num) hlow 2

end TauCeti
