/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.CurveArea.Basic
public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Reparam
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The two boundary components of an annulus

An outer counterclockwise circle and an inner clockwise circle have total index zero in the
hole. Their actual circulation and total weighted area are `π(R²-r²)`. Localization requires
vanishing of the total index; the individual indices do not vanish in the hole.
-/

public section

noncomputable section

open MeasureTheory Set Metric Filter

namespace TauCeti.Green.Examples

/-- A circle with its angular orientation reversed. -/
def clockwiseCircle (R : ℝ) : ℝ → ℂ := circleMap 0 R ∘ fun t ↦ 2 * Real.pi - t

/-- Evaluation of the clockwise angular traversal. -/
theorem clockwiseCircle_apply (R t : ℝ) :
    clockwiseCircle R t = circleMap 0 R (2 * Real.pi - t) := (rfl)

private theorem absolutelyContinuous_reverseAngle :
    AbsolutelyContinuousOnInterval (fun t : ℝ ↦ 2 * Real.pi - t) 0 (2 * Real.pi) :=
  (contDiff_const.sub contDiff_id).contDiffOn.absolutelyContinuousOnInterval

/-- The clockwise circle is absolutely continuous, with the same angular interval as the
outer circle. -/
theorem absolutelyContinuous_clockwiseCircle (R : ℝ) :
    AbsolutelyContinuousOnInterval (clockwiseCircle R) 0 (2 * Real.pi) := by
  have hγ := absolutelyContinuous_circleMap 0 R (2 * Real.pi - 0) (2 * Real.pi - 2 * Real.pi)
  have hanti : AntitoneOn (fun t : ℝ ↦ 2 * Real.pi - t) (uIcc 0 (2 * Real.pi)) :=
    fun _ _ _ _ h ↦ sub_le_sub_left h _
  exact hγ.comp_antitoneOn absolutelyContinuous_reverseAngle hanti hanti.mapsTo_uIcc

/-- Reversal retains the same circular trace. -/
theorem image_clockwiseCircle_uIcc (R : ℝ) :
    clockwiseCircle R '' uIcc 0 (2 * Real.pi) = sphere (0 : ℂ) |R| := by
  rw [clockwiseCircle, image_comp, image_const_sub_uIcc, sub_zero, sub_self, uIcc_comm,
    image_circleMap_uIcc]

/-- The clockwise circular traversal is closed. -/
theorem clockwiseCircle_closed (R : ℝ) :
    clockwiseCircle R 0 = clockwiseCircle R (2 * Real.pi) := by
  rw [clockwiseCircle_apply, clockwiseCircle_apply, sub_zero, sub_self]
  exact (circleMap_closed 0 R).symm

/-- The actual clockwise circulation is the negative of the disc area. -/
theorem integral_circulationFun_area_clockwiseCircle (R : ℝ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), circulationFun areaP areaQ (clockwiseCircle R) t) =
      -(Real.pi * R ^ 2) := by
  have heq (t : ℝ) : circulationFun areaP areaQ (clockwiseCircle R) t = -(R ^ 2 / 2) := by
    have hd : deriv (clockwiseCircle R) t = -deriv (circleMap 0 R) (2 * Real.pi - t) :=
      deriv_comp_const_sub (circleMap 0 R) (2 * Real.pi) t
    have h := circulationFun_area_circleMap R (2 * Real.pi - t)
    rw [circulationFun_def] at h ⊢
    rw [clockwiseCircle_apply, hd, Complex.neg_re, Complex.neg_im]
    linarith
  simp_rw [heq]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- Reversing the circle negates its actual generalized winding number off the trace. -/
theorem windingNumber_clockwiseCircle (R : ℝ) {z : ℂ} (hz : z ∉ sphere (0 : ℂ) |R|) :
    Contour.windingNumber (clockwiseCircle R) 0 (2 * Real.pi) z =
      -Contour.windingNumber (circleMap 0 R) 0 (2 * Real.pi) z := by
  exact Contour.windingNumber_comp_of_antitoneOn_of_absolutelyContinuousOnInterval
    (absolutelyContinuous_circleMap 0 R 0 (2 * Real.pi)) absolutelyContinuous_reverseAngle
    Real.two_pi_pos.le (fun _ _ _ _ h ↦ sub_le_sub_left h _)
    (by simp) (by simp) (by rwa [image_circleMap_uIcc])

/-- The prescribed zero-on-trace weights also negate under clockwise reversal. -/
theorem windingWeight_clockwiseCircle (R : ℝ) (z : ℂ) :
    windingWeight (clockwiseCircle R) 0 (2 * Real.pi) z =
      -windingWeight (circleMap 0 R) 0 (2 * Real.pi) z := by
  by_cases hz : z ∈ sphere (0 : ℂ) |R|
  · rw [windingWeight_eq_zero_of_mem (by rwa [image_clockwiseCircle_uIcc]),
      windingWeight_eq_zero_of_mem (by rwa [image_circleMap_uIcc]), neg_zero]
  · rw [windingWeight_eq_of_notMem (by rwa [image_clockwiseCircle_uIcc]),
      windingWeight_eq_of_notMem (by rwa [image_circleMap_uIcc]),
      windingNumber_clockwiseCircle R hz]
    simp

/-- The actual two-component signed-area circulation is the annular area. -/
theorem integral_circulationFun_area_annulus (r R : ℝ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), circulationFun areaP areaQ (circleMap 0 R) t) +
      (∫ t in (0 : ℝ)..(2 * Real.pi), circulationFun areaP areaQ (clockwiseCircle r) t) =
      Real.pi * (R ^ 2 - r ^ 2) := by
  rw [integral_circulationFun_area_circleMap, integral_circulationFun_area_clockwiseCircle]
  ring

/-- The total winding weight of both annular boundary components integrates to the annular area. -/
theorem integral_windingWeight_annulus {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (∫ z : ℂ, windingWeight (circleMap 0 R) 0 (2 * Real.pi) z +
      windingWeight (clockwiseCircle r) 0 (2 * Real.pi) z) = Real.pi * (R ^ 2 - r ^ 2) := by
  simp_rw [windingWeight_clockwiseCircle]
  rw [integral_add (f := fun z ↦ windingWeight (circleMap 0 R) 0 (2 * Real.pi) z)
    (g := fun z ↦ -windingWeight (circleMap 0 r) 0 (2 * Real.pi) z)
    (integrable_windingWeight (absolutelyContinuous_circleMap 0 R 0 (2 * Real.pi))
      (circleMap_closed 0 R))
    (integrable_windingWeight (absolutelyContinuous_circleMap 0 r 0 (2 * Real.pi))
      (circleMap_closed 0 r)).neg,
    integral_neg, integral_windingWeight_circleMap hR, integral_windingWeight_circleMap hr]
  ring

/-- The total index vanishes in the hole although both individual circles have nonzero index. -/
theorem windingNumber_annulus_hole {r R : ℝ} (hr : 0 < r) (hrR : r < R) {z : ℂ}
    (hz : ‖z‖ < r) :
    Contour.windingNumber (circleMap 0 R) 0 (2 * Real.pi) z +
      Contour.windingNumber (clockwiseCircle r) 0 (2 * Real.pi) z = 0 := by
  have hzR : dist z 0 < R := by simpa only [dist_zero_right] using hz.trans hrR
  have hzr : dist z 0 < r := by simpa only [dist_zero_right] using hz
  rw [windingNumber_clockwiseCircle r (by
    simpa only [mem_sphere, dist_zero_right, abs_of_pos hr] using hzr.ne),
    Contour.windingNumber_circleMap_eq_one_of_dist_lt hzR,
    Contour.windingNumber_circleMap_eq_one_of_dist_lt hzr]
  simp

/-- An open field domain around the two boundary components which excludes the central hole. -/
def annulusDomain (r R : ℝ) : Set ℂ := {z | r / 2 < ‖z‖ ∧ ‖z‖ < R + 1}

/-- This domain is open. -/
theorem isOpen_annulusDomain (r R : ℝ) : IsOpen (annulusDomain r R) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

/-- Both circular traces lie in the annular field domain. -/
theorem traces_subset_annulusDomain {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    circleMap 0 R '' uIcc 0 (2 * Real.pi) ⊆ annulusDomain r R ∧
      clockwiseCircle r '' uIcc 0 (2 * Real.pi) ⊆ annulusDomain r R := by
  rw [image_circleMap_uIcc, image_clockwiseCircle_uIcc]
  constructor
  · intro z hz
    have hn : ‖z‖ = R := by
      simpa only [mem_sphere, dist_zero_right, abs_of_pos (hr.trans hrR)] using hz
    change r / 2 < ‖z‖ ∧ ‖z‖ < R + 1
    rw [hn]
    constructor <;> linarith
  · intro z hz
    have hn : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right, abs_of_pos hr] using hz
    change r / 2 < ‖z‖ ∧ ‖z‖ < R + 1
    rw [hn]
    constructor <;> linarith

/-- Only the total index vanishes outside the annular field domain. This includes cancellation
in the hole, where each individual boundary component has nonzero index. -/
theorem windingNumber_annulus_zero_on_compl {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {z : ℂ} (hz : z ∉ annulusDomain r R) :
    Contour.windingNumber (circleMap 0 R) 0 (2 * Real.pi) z +
      Contour.windingNumber (clockwiseCircle r) 0 (2 * Real.pi) z = 0 := by
  by_cases hs : ‖z‖ < r
  · exact windingNumber_annulus_hole hr hrR hs
  · have hl : R < ‖z‖ := by
      by_contra h
      apply hz
      change r / 2 < ‖z‖ ∧ ‖z‖ < R + 1
      constructor <;> linarith [le_of_not_gt hs, le_of_not_gt h]
    rw [windingNumber_clockwiseCircle r (by
      simpa only [mem_sphere, dist_zero_right, abs_of_pos hr] using (hrR.trans hl).ne'),
      Contour.windingNumber_circleMap_eq_zero_of_lt_dist (hr.trans hrR).le
        (by simpa only [dist_zero_right] using hl),
      Contour.windingNumber_circleMap_eq_zero_of_lt_dist hr.le
        (by simpa only [dist_zero_right] using hrR.trans hl)]
    simp

end TauCeti.Green.Examples
