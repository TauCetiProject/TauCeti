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
and `y`. For `T ≥ 0` the transform is nonnegative, being `T / 2` times a square, and it stays
close to `T / 2` while `|T * y|` is small. For `T > 0`, a weight with both properties turns an
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
  · simp only [mul_zero, cos_zero, mul_one, zero_div, sinc_zero, one_pow]
    rw [integral_sub intervalIntegrable_const (intervalIntegrable_id.div_const T),
      intervalIntegral.integral_div, integral_id, integral_const]
    field_simp
    ring
  -- Integrate by parts against the antiderivative `sin (t * y) / y` of `cos (t * y)`.
  have hu (t : ℝ) : HasDerivAt (fun s ↦ 1 - s / T) (-(1 / T)) t := by
    simpa using ((hasDerivAt_id t).div_const T).const_sub 1
  have hv (t : ℝ) : HasDerivAt (fun s ↦ sin (s * y) / y) (cos (t * y)) t := by
    simpa [hy] using ((hasDerivAt_mul_const y).sin).div_const y
  have hsin : ∫ t in 0..T, sin (t * y) = (1 - cos (T * y)) / y := by
    rw [intervalIntegral.integral_comp_mul_right sin hy, integral_sin, zero_mul, cos_zero,
      smul_eq_mul, inv_mul_eq_div]
  rw [integral_mul_deriv_eq_deriv_mul (fun t _ ↦ hu t) (fun t _ ↦ hv t) intervalIntegrable_const
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_div, hsin, one_sub_cos_eq_sq_div_two_mul_sinc_sq]
  simp only [div_self hT, sub_self, zero_mul, zero_div, sin_zero, sub_zero]
  field_simp
  ring

end TauCeti
