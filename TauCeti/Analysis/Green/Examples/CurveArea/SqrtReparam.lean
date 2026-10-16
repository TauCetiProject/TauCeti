/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.CurveArea.Basic
public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Reparam
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Rpow
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A circle traversed with unbounded speed

The parameter `2π √t` is absolutely continuous on `[0,1]`, with integrable derivative singular
at zero. The resulting unit circle has the same circulation and winding number as the smooth
circle, even though its speed has no finite bound.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace TauCeti.Green.Examples

/-- The increasing parameter traversing the full circle in unit time. -/
def sqrtAngle (t : ℝ) : ℝ := 2 * Real.pi * Real.sqrt t

/-- Evaluation of the square-root angular parameter. -/
theorem sqrtAngle_apply (t : ℝ) : sqrtAngle t = 2 * Real.pi * Real.sqrt t := (rfl)

/-- This angular parameter is absolutely continuous with no Lipschitz assumption. -/
theorem absolutelyContinuous_sqrtAngle : AbsolutelyContinuousOnInterval sqrtAngle 0 1 :=
  (Real.absolutelyContinuousOnInterval_sqrt 0 1).const_mul (2 * Real.pi)

/-- The square-root angle is increasing. -/
theorem monotone_sqrtAngle : Monotone sqrtAngle := by
  intro s t hst
  rw [sqrtAngle_apply, sqrtAngle_apply]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hst) Real.two_pi_pos.le

/-- The unbounded-speed unit-circle parameterization. -/
def sqrtCircle : ℝ → ℂ := circleMap 0 1 ∘ sqrtAngle

/-- Evaluation of the square-root circle parameterization. -/
theorem sqrtCircle_apply (t : ℝ) : sqrtCircle t = circleMap 0 1 (sqrtAngle t) := (rfl)

/-- The square-root parameter traverses a closed circle. -/
theorem sqrtCircle_closed : sqrtCircle 0 = sqrtCircle 1 := by
  rw [sqrtCircle_apply, sqrtCircle_apply, sqrtAngle_apply, sqrtAngle_apply]
  simpa using (periodic_circleMap 0 1 0).symm

/-- The parameterized circle is absolutely continuous on the whole unit interval. -/
theorem absolutelyContinuous_sqrtCircle : AbsolutelyContinuousOnInterval sqrtCircle 0 1 := by
  apply ((lipschitzWith_circleMap 0 1).lipschitzOnWith.absolutelyContinuousOnInterval
    (a := 0) (b := 2 * Real.pi)).comp_monotoneOn
    absolutelyContinuous_sqrtAngle
  · exact monotone_sqrtAngle.monotoneOn _
  · intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [uIcc_of_le Real.two_pi_pos.le]
    refine ⟨by dsimp [sqrtAngle]; positivity, ?_⟩
    have hs : Real.sqrt t ≤ 1 := (Real.sqrt_le_one).mpr ht.2
    simpa only [sqrtAngle, mul_one] using mul_le_mul_of_nonneg_left hs Real.two_pi_pos.le

/-- The square-root circle retains the actual circulation value `π`. -/
theorem integral_circulationFun_area_sqrtCircle :
    (∫ t in (0 : ℝ)..1, circulationFun areaP areaQ sqrtCircle t) = Real.pi := by
  have ha : sqrtAngle 0 = 0 := by simp [sqrtAngle]
  have hb : sqrtAngle 1 = 2 * Real.pi := by simp [sqrtAngle]
  have hγ : AbsolutelyContinuousOnInterval (circleMap 0 1) (sqrtAngle 0) (sqrtAngle 1) := by
    rw [ha, hb]
    exact (lipschitzWith_circleMap 0 1).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := 0) (b := 2 * Real.pi)
  have hi := ((lipschitzWith_circleMap 0 1).lipschitzOnWith.absolutelyContinuousOnInterval
    (a := 0) (b := 2 * Real.pi)).intervalIntegrable_circulationFun
    (contDiff_areaP (n := 1)).continuous.continuousOn
    (contDiff_areaQ (n := 1)).continuous.continuousOn
  have hint : IntervalIntegrable
      (fun t ↦ oneForm areaP areaQ (circleMap 0 1 t) (deriv (circleMap 0 1) t)) volume
      (sqrtAngle 0) (sqrtAngle 1) := by
    simpa only [ha, hb, ← circulationFun_eq_oneForm] using hi
  have he := hγ.integral_oneForm_comp absolutelyContinuous_sqrtAngle zero_le_one
    (Or.inl (monotone_sqrtAngle.monotoneOn _)) hint
  rw [ha, hb] at he
  simpa only [← circulationFun_eq_oneForm, sqrtCircle, integral_circulationFun_area_circleMap,
    one_pow, mul_one] using he

/-- The square-root circle has the same exact trace as the ordinary circle. -/
theorem image_sqrtCircle_uIcc : sqrtCircle '' uIcc 0 1 = Metric.sphere (0 : ℂ) 1 := by
  have hi := absolutelyContinuous_sqrtAngle.continuousOn.image_uIcc_of_monotoneOn
    (monotone_sqrtAngle.monotoneOn (uIcc 0 1))
  rw [sqrtCircle, image_comp, hi]
  simp only [sqrtAngle_apply, Real.sqrt_zero, Real.sqrt_one, mul_zero, mul_one,
    Complex.image_circleMap_uIcc, abs_one]

/-- The actual generalized index of the square-root circle agrees everywhere off the circle
with that of the ordinary angular traversal. -/
theorem windingNumber_sqrtCircle {z : ℂ} (hz : z ∉ Metric.sphere (0 : ℂ) 1) :
    Contour.windingNumber sqrtCircle 0 1 z =
      Contour.windingNumber (circleMap 0 1) 0 (2 * Real.pi) z := by
  exact AbsolutelyContinuousOnInterval.windingNumber_comp_of_monotoneOn
    ((lipschitzWith_circleMap 0 1).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := 0) (b := 2 * Real.pi))
    absolutelyContinuous_sqrtAngle zero_le_one
    (monotone_sqrtAngle.monotoneOn (Icc 0 1))
    (by simp [sqrtAngle]) (by simp [sqrtAngle]) (by simpa [Complex.image_circleMap_uIcc] using hz)

/-- The existing generalized winding number remains one at the center. -/
theorem windingNumber_sqrtCircle_center : Contour.windingNumber sqrtCircle 0 1 0 = 1 := by
  rw [windingNumber_sqrtCircle (by simp)]
  exact Contour.windingNumber_circleMap_center_eq_one one_ne_zero

/-- The integrable winding weight remains the unit-disc indicator despite the unbounded speed. -/
theorem windingWeight_sqrtCircle (z : ℂ) :
    windingWeight sqrtCircle 0 1 z = (Metric.ball (0 : ℂ) 1).indicator 1 z := by
  by_cases hz : z ∈ Metric.sphere (0 : ℂ) 1
  · rw [windingWeight_eq_zero_of_mem (by rwa [image_sqrtCircle_uIcc])]
    have hn : dist z 0 = 1 := Metric.mem_sphere.mp hz
    simp [Metric.mem_ball, hn]
  · rw [windingWeight_eq_of_notMem (by rwa [image_sqrtCircle_uIcc]), windingNumber_sqrtCircle hz]
    rw [← windingWeight_eq_of_notMem (γ := circleMap 0 1) (a := 0) (b := 2 * Real.pi)
      (by simpa [Complex.image_circleMap_uIcc] using hz)]
    exact windingWeight_circleMap zero_lt_one z

/-- Away from zero the actual speed is `π/√t`. -/
theorem norm_deriv_sqrtCircle {t : ℝ} (ht : 0 < t) :
    ‖deriv sqrtCircle t‖ = Real.pi / Real.sqrt t := by
  have hθ : HasDerivAt sqrtAngle (2 * Real.pi * (1 / (2 * Real.sqrt t))) t :=
    (Real.hasDerivAt_sqrt ht.ne').const_mul (2 * Real.pi)
  have hγ : HasDerivAt sqrtCircle
      ((2 * Real.pi * (1 / (2 * Real.sqrt t))) •
        (circleMap 0 1 (sqrtAngle t) * Complex.I)) t :=
    (hasDerivAt_circleMap 0 1 (sqrtAngle t)).scomp t hθ
  rw [hγ.deriv]
  have hs := Real.sqrt_pos.mpr ht
  simp only [norm_smul, norm_mul, norm_circleMap_zero, Complex.norm_I,
    abs_one, mul_one, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity), abs_of_pos (by positivity)]
  field_simp

/-- The speed is unbounded on the open unit interval. -/
theorem sqrtCircle_speed_unbounded (M : ℝ) :
    ∃ t ∈ Ioo (0 : ℝ) 1, M < ‖deriv sqrtCircle t‖ := by
  let d := |M| + Real.pi + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hpd : Real.pi < d := by dsimp [d]; linarith [abs_nonneg M]
  let t := (Real.pi / d) ^ 2
  have hrat : 0 < Real.pi / d := div_pos Real.pi_pos hd
  have hrat1 : Real.pi / d < 1 := (div_lt_one hd).mpr hpd
  have ht : 0 < t := sq_pos_of_pos hrat
  have ht1 : t < 1 := by dsimp [t]; nlinarith
  refine ⟨t, ⟨ht, ht1⟩, ?_⟩
  have hsqrt : Real.sqrt t = Real.pi / d := Real.sqrt_sq hrat.le
  rw [norm_deriv_sqrtCircle ht, hsqrt]
  have hval : Real.pi / (Real.pi / d) = d := by field_simp
  rw [hval]
  dsimp [d]
  linarith [le_abs_self M, Real.pi_pos]

end TauCeti.Green.Examples
