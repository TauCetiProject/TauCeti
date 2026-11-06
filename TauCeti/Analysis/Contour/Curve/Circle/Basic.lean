/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Traces of full circular traversals

The trace of a circular parametrization over `[0,2π]` is the sphere, for arbitrary signed radii.
Consequently the exponential `t ↦ exp (2π i t / L)` and its conjugate cover the unit circle over
`[0, L]` (`Complex.image_exp_two_pi_I_div_Icc`, `Complex.image_exp_neg_two_pi_I_div_Icc`).
-/

public section

open Set Metric
open scoped Real

namespace Complex

/-- The full circular trace over `[0,2π]` is exactly the circle. -/
theorem image_circleMap_uIcc (c : ℂ) (R : ℝ) :
    circleMap c R '' uIcc 0 (2 * Real.pi) = sphere c |R| := by
  rw [uIcc_of_le Real.two_pi_pos.le]
  simpa only [zero_add, range_circleMap] using
    (periodic_circleMap c R).image_Icc (a := 0) Real.two_pi_pos

/-- One turn of a unit circular exponential, rescaled to the interval `[0, L]` of positive length
`L`, covers the unit circle, including both endpoints. -/
theorem image_exp_two_pi_I_div_Icc {L : ℝ} (hL : 0 < L) :
    (fun t : ℝ ↦ exp (2 * π * I * t / L)) '' Icc 0 L = sphere (0 : ℂ) 1 := by
  -- Rescaling a full length interval gives a full angular period, including both endpoints.
  have hangle : (fun t : ℝ ↦ 2 * π * t / L) '' Icc 0 L = uIcc 0 (2 * π) := by
    rw [← uIcc_of_le hL.le]
    have hscale : (fun t : ℝ ↦ 2 * π * t / L) = fun t ↦ t * (2 * π / L) := by
      funext t
      ring
    rw [hscale, image_mul_const_uIcc]
    congr 1
    · simp
    · field_simp
  calc
    _ = circleMap 0 1 '' ((fun t : ℝ ↦ 2 * π * t / L) '' Icc 0 L) := by
      rw [image_image]
      congr 1
      funext t
      simp only [circleMap, ofReal_one, one_mul, zero_add, ofReal_div, ofReal_mul,
        ofReal_ofNat]
      congr 1
      ring
    _ = sphere (0 : ℂ) 1 := by rw [hangle, image_circleMap_uIcc]; simp

/-- The conjugate circular exponential `t ↦ exp (-(2π i t / L))` also covers the unit circle over
`[0, L]`. -/
theorem image_exp_neg_two_pi_I_div_Icc {L : ℝ} (hL : 0 < L) :
    (fun t : ℝ ↦ exp (-(2 * π * I * t / L))) '' Icc 0 L = sphere (0 : ℂ) 1 := by
  calc
    _ = conjLIE '' ((fun t : ℝ ↦ exp (2 * π * I * t / L)) '' Icc 0 L) := by
      rw [image_image]
      congr 1
      funext t
      simp [conjLIE_apply, ← exp_conj, map_ofNat, neg_div]
    _ = sphere (0 : ℂ) 1 := by
      rw [image_exp_two_pi_I_div_Icc hL, conjLIE.image_sphere]
      simp

end Complex
