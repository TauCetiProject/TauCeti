/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.CurveArea.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# A circle traversed twice

Traversing `circleMap` over `[0,4π]` doubles the actual generalized winding number off the circle,
and hence doubles its integrable winding weight. Both signed-area integrals have value `2π R²`.
-/

public section

noncomputable section

open MeasureTheory Set Metric

namespace TauCeti.Green.Examples

/-- A double traversal has the same circular trace as a single traversal. -/
theorem image_circleMap_twice_uIcc (c : ℂ) (R : ℝ) :
    circleMap c R '' uIcc 0 (4 * Real.pi) = sphere c |R| := by
  apply Subset.antisymm
  · exact (image_subset_range _ _).trans_eq (range_circleMap c R)
  · rw [← Complex.image_circleMap_uIcc c R]
    apply image_mono
    rw [uIcc_of_le Real.two_pi_pos.le, uIcc_of_le (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]
    exact Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])

/-- The double angular traversal is closed. -/
theorem circleMap_twice_closed (c : ℂ) (R : ℝ) :
    circleMap c R 0 = circleMap c R (4 * Real.pi) := by
  rw [show 4 * Real.pi = 2 * Real.pi + 2 * Real.pi by ring,
    periodic_circleMap c R (2 * Real.pi)]
  simpa only [zero_add] using (periodic_circleMap c R 0).symm

/-- The actual generalized index doubles under a second circular traversal. -/
theorem windingNumber_circleMap_twice {c z : ℂ} {R : ℝ}
    (hz : z ∉ sphere c |R|) :
    Contour.windingNumber (circleMap c R) 0 (4 * Real.pi) z =
      2 * Contour.windingNumber (circleMap c R) 0 (2 * Real.pi) z := by
  have ha : ∀ t, circleMap c R t ≠ z := fun t h ↦ hz (h ▸ circleMap_mem_sphere' c R t)
  have hd : Continuous (deriv (circleMap c R)) := by
    have heq : deriv (circleMap c R) = fun t ↦ circleMap 0 R t * Complex.I :=
      funext (deriv_circleMap c R)
    rw [heq]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hi : Continuous (fun t ↦ (circleMap c R t - z)⁻¹ * deriv (circleMap c R) t) :=
    ((continuous_circleMap c R).sub continuous_const).inv₀
      (fun t ↦ sub_ne_zero.mpr (ha t)) |>.mul hd
  have hp : Function.Periodic
      (fun t ↦ (circleMap c R t - z)⁻¹ * deriv (circleMap c R) t) (2 * Real.pi) := by
    intro t
    simp only [deriv_circleMap, periodic_circleMap c R t, periodic_circleMap 0 R t]
  have he := hp.intervalIntegral_add_zsmul_eq 2 0 (fun a b ↦ hi.intervalIntegrable a b)
  have he' : (∫ t in (0 : ℝ)..(4 * Real.pi),
      (circleMap c R t - z)⁻¹ * deriv (circleMap c R) t) =
      2 * ∫ t in (0 : ℝ)..(2 * Real.pi),
        (circleMap c R t - z)⁻¹ * deriv (circleMap c R) t := by
    have hspan : (0 : ℝ) + (2 : ℤ) • (2 * Real.pi) = 4 * Real.pi := by simp; ring
    rw [hspan, zero_add] at he
    simpa only [zsmul_eq_mul, Int.cast_ofNat] using he
  rw [Contour.windingNumber_eq_integral_of_avoidance
    (continuous_circleMap c R).continuousOn (fun t _ ↦ ha t) (hi.intervalIntegrable _ _),
    Contour.windingNumber_eq_integral_of_avoidance
      (continuous_circleMap c R).continuousOn (fun t _ ↦ ha t) (hi.intervalIntegrable _ _), he']
  ring

/-- The winding weight of an actual double traversal is twice the single-traversal weight. -/
theorem windingWeight_circleMap_twice (R : ℝ) (z : ℂ) :
    windingWeight (circleMap 0 R) 0 (4 * Real.pi) z =
      2 * windingWeight (circleMap 0 R) 0 (2 * Real.pi) z := by
  by_cases hz : z ∈ sphere (0 : ℂ) |R|
  · rw [windingWeight_eq_zero_of_mem (by rwa [image_circleMap_twice_uIcc]),
      windingWeight_eq_zero_of_mem (by rwa [Complex.image_circleMap_uIcc]), mul_zero]
  · rw [windingWeight_eq_of_notMem (by rwa [image_circleMap_twice_uIcc]),
      windingWeight_eq_of_notMem (by rwa [Complex.image_circleMap_uIcc]),
      windingNumber_circleMap_twice hz]
    simp

/-- Twice around a circle doubles the actual circulation. -/
theorem integral_circulationFun_area_circleMap_twice (R : ℝ) :
    (∫ t in (0 : ℝ)..(4 * Real.pi), circulationFun areaP areaQ (circleMap 0 R) t) =
      2 * Real.pi * R ^ 2 := by
  simp_rw [circulationFun_area_circleMap]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The area weight of a double traversal integrates to twice the disc area. -/
theorem integral_windingWeight_circleMap_twice {R : ℝ} (hR : 0 < R) :
    (∫ z : ℂ, windingWeight (circleMap 0 R) 0 (4 * Real.pi) z) =
      2 * Real.pi * R ^ 2 := by
  simp_rw [windingWeight_circleMap_twice]
  rw [integral_const_mul, integral_windingWeight_circleMap hR]
  ring

end TauCeti.Green.Examples
