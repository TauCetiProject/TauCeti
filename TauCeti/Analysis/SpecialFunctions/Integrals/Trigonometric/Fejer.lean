/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The cosine transform of the triangular weight

The decreasing triangular weight `1 - t / T` on `[0, T]` has cosine transform
`T / 2 * sinc (T * y / 2) ^ 2` (`TauCeti.integral_one_sub_div_mul_cos_mul`). Up to
normalization, this is the Fejér kernel of the real line. The identity holds for all real `T`
and `y`. For `T ≥ 0` the transform is nonnegative, being `T / 2` times a square, and at most
`T / 2` (`TauCeti.mul_sinc_sq_le_div_two`). It is at least `T / 4` while `|y| ≤ T⁻¹`
(`TauCeti.div_four_le_mul_sinc_sq`). For `T > 0`, a weight with these properties turns an
integral of a characteristic function over `[0, T]` into a bound for the mass of a ball of radius
of order `1 / T`.
-/

public section

open Real intervalIntegral

namespace TauCeti

/-- The cosine transform of the triangular weight `1 - t / T` on `[0, T]` is
`T / 2 * sinc (T * y / 2) ^ 2`. This holds for all real `T` and `y`. -/
theorem integral_one_sub_div_mul_cos_mul (T y : ℝ) :
    ∫ t in 0..T, (1 - t / T) * cos (t * y) = T / 2 * sinc (T * y / 2) ^ 2 := by
  rcases eq_or_ne T 0 with rfl | hT
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp [integral_sub intervalIntegrable_const (intervalIntegrable_id.div_const T), integral_id]
    field_simp
    ring
  -- Integrate by parts against the antiderivative `t * sinc (y * t)` of `cos (t * y)`.
  have hu (t : ℝ) : HasDerivAt (fun s ↦ 1 - s / T) (-(1 / T)) t := by
    simpa using ((hasDerivAt_id t).div_const T).const_sub 1
  have hv (t : ℝ) : HasDerivAt (fun s ↦ s * sinc (y * s)) (cos (t * y)) t :=
    (hasDerivAt_mul_sinc_mul y t).congr_deriv (by rw [mul_comm])
  have hparts : ∫ t in 0..T, (1 - t / T) * cos (t * y) =
      T⁻¹ * ∫ t in 0..T, sin (y * t) / y := by
    rw [integral_mul_deriv_eq_deriv_mul (fun t _ ↦ hu t) (fun t _ ↦ hv t) intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp [hT, mul_sinc_mul_of_ne_zero hy]
  have hsin : ∫ t in 0..T, sin (y * t) / y = (1 - cos (T * y)) / y ^ 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_mul_left sin hy,
      integral_sin]
    simp [mul_comm y T]
    field_simp
  rw [hparts, hsin, one_sub_cos_eq_sq_div_two_mul_sinc_sq]
  field_simp

/-- The kernel `T / 2 * sinc (T * y / 2) ^ 2` is at least `T / 4` when `|y| ≤ T⁻¹`. -/
theorem div_four_le_mul_sinc_sq {T y : ℝ} (hy : |y| ≤ T⁻¹) :
    T / 4 ≤ T / 2 * sinc (T * y / 2) ^ 2 := by
  rcases le_or_gt T 0 with hT | hT
  · -- For `T ≤ 0` the hypothesis forces `T⁻¹ = 0`, hence `T = 0`.
    have hT₀ : T = 0 := inv_eq_zero.1 (le_antisymm (inv_nonpos.2 hT) ((abs_nonneg y).trans hy))
    simp [hT₀]
  -- Multiplying `|y| ≤ T⁻¹` by `T > 0` gives `T * |y| ≤ 1`.
  have hTy₁ : T * |y| ≤ 1 := by
    simpa [hT.ne'] using mul_le_mul_of_nonneg_left hy hT.le
  have hTy : |T * y / 2| ≤ 1 / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hT, abs_two]
    linarith
  have hsq : (T * y / 2) ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (T * y / 2)]
  -- Since `|T * y / 2| ≤ 1 / 2`, `sinc (T * y / 2)` is at least `3 / 4`.
  have hlow : 3 / 4 ≤ sinc (T * y / 2) := by
    linarith [(abs_le.1 (Real.abs_sinc_sub_one_le (T * y / 2))).1]
  have hsinc : 1 / 2 ≤ sinc (T * y / 2) ^ 2 := by nlinarith
  calc T / 4 = T / 2 * (1 / 2) := by ring
    _ ≤ T / 2 * sinc (T * y / 2) ^ 2 := by gcongr

/-- The kernel `T / 2 * sinc (T * y / 2) ^ 2` is at most `T / 2` for `T ≥ 0`. -/
theorem mul_sinc_sq_le_div_two {T : ℝ} (hT : 0 ≤ T) (y : ℝ) :
    T / 2 * sinc (T * y / 2) ^ 2 ≤ T / 2 := by
  have hsq : sinc (T * y / 2) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _)
  exact mul_le_of_le_one_right (by positivity) hsq

end TauCeti
