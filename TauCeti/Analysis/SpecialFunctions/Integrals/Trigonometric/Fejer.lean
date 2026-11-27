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

For `T > 0`, the decreasing triangular weight `1 - t / T` on `[0, T]` has cosine transform
`T / 2 * sinc (T * y / 2) ^ 2` (`TauCeti.integral_one_sub_div_mul_cos_mul`). Up to
normalization, this is the Fejér kernel of the real line. Stated with the oriented interval
integral `∫ t in 0..T`, the identity holds for all real `T` and `y`. For `T > 0` the kernel is
nonnegative, being `T / 2` times a square, and at most `T / 2` since `|sinc| ≤ 1`. It is at
least `T / 2 * (23 / 24) ^ 2` while `|y| ≤ T⁻¹`, since then `sinc (T * y / 2) ≥ 23 / 24`
(`TauCeti.le_sinc_of_abs_le_half`). Integrated against a finite measure, the kernel centred at
`v` becomes the integral over `[0, T]`, weighted by `1 - t / T`, of the real part of the
characteristic function rotated by the phase `-t * v`. Since the kernel is at least
`T / 2 * (23 / 24) ^ 2` on the ball of radius `T⁻¹` about `v`, the mass of that ball is then at
most `2 * (24 / 23) ^ 2 / T` times the integral of the modulus of the characteristic function over
`[0, T]`.
-/

public section

open Real intervalIntegral

namespace TauCeti

/-- For `T > 0`, the cosine transform of the triangular weight `1 - t / T` on `[0, T]` is
`T / 2 * sinc (T * y / 2) ^ 2`. Stated with the oriented interval integral `∫ t in 0..T`, the
identity holds for all real `T` and `y`. -/
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

end TauCeti
