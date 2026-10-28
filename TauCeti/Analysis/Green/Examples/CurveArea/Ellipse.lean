/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.CurveArea.Basic
public import TauCeti.Analysis.Green.Affine.Basic
public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Proximity
public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.LocallyConstant
import TauCeti.LinearAlgebra.Complex.Module
import TauCeti.Analysis.Contour.Winding.StarConvex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Signed ellipse area

The ellipse `(a cos t,b sin t)` has signed-area circulation `πab`. Nonzero axes identify it
with the invertible affine image of the unit circle, whose determinant is `ab`.
-/

public section

noncomputable section

open MeasureTheory Set Metric

namespace TauCeti.Green.Examples

/-- The angular parameterization of a real-axis ellipse, retaining signed axis lengths. -/
def ellipse (a b : ℝ) (t : ℝ) : ℂ := (a * Real.cos t : ℝ) + (b * Real.sin t : ℝ) * Complex.I

/-- The real and imaginary coordinate formula for the ellipse. -/
theorem ellipse_apply (a b t : ℝ) :
    ellipse a b t = (a * Real.cos t : ℝ) + (b * Real.sin t : ℝ) * Complex.I := (rfl)

/-- Ellipses are real smooth, including degenerate axes. -/
theorem contDiff_ellipse (a b : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (ellipse a b) := by
  exact (Complex.ofRealCLM.contDiff.comp
    ((contDiff_const (c := a)).mul Real.contDiff_cos)).add
      ((Complex.ofRealCLM.contDiff.comp
        ((contDiff_const (c := b)).mul Real.contDiff_sin)).mul (contDiff_const (c := Complex.I)))

/-- The angular ellipse is a closed absolutely continuous curve. -/
theorem absolutelyContinuous_ellipse (a b : ℝ) :
    AbsolutelyContinuousOnInterval (ellipse a b) 0 (2 * Real.pi) :=
  (contDiff_ellipse a b (n := 1)).contDiffOn.absolutelyContinuousOnInterval

/-- A complete angular traversal closes the ellipse. -/
theorem ellipse_closed (a b : ℝ) : ellipse a b 0 = ellipse a b (2 * Real.pi) := by
  simp [ellipse_apply]

/-- The actual angular derivative of the ellipse. -/
theorem hasDerivAt_ellipse (a b t : ℝ) :
    HasDerivAt (ellipse a b) ((-a * Real.sin t : ℝ) + (b * Real.cos t : ℝ) * Complex.I) t := by
  convert (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
    ((Real.hasDerivAt_cos t).const_mul a)).add
      ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
        ((Real.hasDerivAt_sin t).const_mul b)).mul_const Complex.I) using 1
  · ext s
    rw [ellipse_apply]
    simp
  · simp

/-- The signed-area circulation integrand is constantly `ab/2`. -/
theorem circulationFun_area_ellipse (a b t : ℝ) :
    circulationFun areaP areaQ (ellipse a b) t = a * b / 2 := by
  rw [circulationFun, areaP_apply, areaQ_apply, ellipse_apply, (hasDerivAt_ellipse a b t).deriv]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_add, add_zero, sub_zero]
  calc
    _ = a * b * (Real.sin t ^ 2 + Real.cos t ^ 2) / 2 := by ring
    _ = a * b / 2 := by rw [Real.sin_sq_add_cos_sq]; ring

/-- The actual signed-area circulation around the ellipse is `πab`, with either orientation. -/
theorem integral_circulationFun_area_ellipse (a b : ℝ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), circulationFun areaP areaQ (ellipse a b) t) =
      Real.pi * a * b := by
  simp_rw [circulationFun_area_ellipse]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The diagonal real linear map describing the ellipse axes. -/
def ellipseLinearMap (a b : ℝ) : ℂ →ₗ[ℝ] ℂ :=
  Complex.basisOneI.constr ℝ ![(a : ℂ), (b : ℂ) * Complex.I]

@[simp]
theorem ellipseLinearMap_one (a b : ℝ) : ellipseLinearMap a b 1 = (a : ℂ) := by
  simpa only [ellipseLinearMap, Complex.coe_basisOneI, Matrix.cons_val_zero] using
    Complex.basisOneI.constr_basis ℝ ![(a : ℂ), (b : ℂ) * Complex.I] 0

@[simp]
theorem ellipseLinearMap_I (a b : ℝ) :
    ellipseLinearMap a b Complex.I = (b : ℂ) * Complex.I := by
  simpa only [ellipseLinearMap, Complex.coe_basisOneI, Matrix.cons_val_one,
    Matrix.cons_val_zero] using
    Complex.basisOneI.constr_basis ℝ ![(a : ℂ), (b : ℂ) * Complex.I] 1

/-- The diagonal axis map has determinant `ab`. -/
theorem det_ellipseLinearMap (a b : ℝ) : (ellipseLinearMap a b).det = a * b := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

/-- Nonzero ellipse axes give invertible real coordinates. -/
def ellipseCoordinates (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ((ellipseLinearMap a b).equivOfIsUnitDet
    (isUnit_iff_ne_zero.mpr ((det_ellipseLinearMap a b).trans_ne
      (mul_ne_zero ha hb)))).toContinuousLinearEquiv

/-- The ellipse coordinates have the diagonal underlying linear map. -/
theorem ellipseCoordinates_toLinearMap (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (ellipseCoordinates a b ha hb).toLinearEquiv.toLinearMap = ellipseLinearMap a b := by
  rw [ellipseCoordinates, LinearEquiv.toLinearEquiv_toContinuousLinearEquiv]
  exact LinearMap.coe_equivOfIsUnitDet _

/-- The coordinate determinant is the signed product of the axes. -/
theorem det_ellipseCoordinates (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (ellipseCoordinates a b ha hb).toLinearEquiv.toLinearMap.det = a * b := by
  rw [ellipseCoordinates_toLinearMap, det_ellipseLinearMap]

@[simp]
theorem ellipseCoordinates_one (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ellipseCoordinates a b ha hb 1 = (a : ℂ) := by
  have h := congrArg (fun L : ℂ →ₗ[ℝ] ℂ ↦ L 1) (ellipseCoordinates_toLinearMap a b ha hb)
  simpa only [ellipseLinearMap_one, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv] using h

@[simp]
theorem ellipseCoordinates_I (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ellipseCoordinates a b ha hb Complex.I = (b : ℂ) * Complex.I := by
  have h := congrArg (fun L : ℂ →ₗ[ℝ] ℂ ↦ L Complex.I)
    (ellipseCoordinates_toLinearMap a b ha hb)
  simpa only [ellipseLinearMap_I, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv] using h

/-- The ellipse is the actual invertible affine image of the unit-circle parameterization. -/
theorem ellipse_eq_affine_circle (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ellipse a b = affineMap (ellipseCoordinates a b ha hb) 0 ∘ circleMap 0 1 := by
  ext t
  let A := ellipseCoordinates a b ha hb
  have he (z : ℂ) : A z = z.re • A 1 + z.im • A Complex.I :=
    LinearMap.apply_eq_re_smul_one_add_im_smul_I A.toLinearEquiv.toLinearMap z
  simp only [Function.comp_apply, affineMap_apply, add_zero, ContinuousLinearEquiv.coe_coe]
  rw [he, ellipseCoordinates_one, ellipseCoordinates_I, circleMap_zero_re, circleMap_zero_im,
    ellipse_apply]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The ellipse trace is exactly the image of the unit sphere under its axis coordinates. -/
theorem image_ellipse_uIcc (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ellipse a b '' uIcc 0 (2 * Real.pi) =
      ellipseCoordinates a b ha hb '' sphere (0 : ℂ) 1 := by
  rw [ellipse_eq_affine_circle a b ha hb, image_comp, Complex.image_circleMap_uIcc]
  simp only [abs_one, affineMap_apply, add_zero, ContinuousLinearEquiv.coe_coe]

/-- Positive axes have winding number one at the center, by actual AC proximity to a circle. -/
theorem windingNumber_ellipse_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Contour.windingNumber (ellipse a b) 0 (2 * Real.pi) 0 = 1 := by
  have hR : 0 < a + b := add_pos ha hb
  rw [AbsolutelyContinuousOnInterval.windingNumber_eq_of_dist_lt_dist
    ((lipschitzWith_circleMap 0 (a + b)).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := 0) (b := 2 * Real.pi))
    (absolutelyContinuous_ellipse a b)
    (by simpa only [zero_add] using (periodic_circleMap 0 (a + b) 0).symm)
    (ellipse_closed a b)]
  · exact Contour.windingNumber_circleMap_eq_one_of_dist_lt (by simpa using hR)
  intro t ht
  rw [dist_eq_norm, dist_zero_right, norm_circleMap_zero, abs_of_pos hR]
  have hre : (ellipse a b t - circleMap 0 (a + b) t).re = -b * Real.cos t := by
    rw [ellipse_apply]
    simp only [Complex.sub_re, circleMap_zero_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero]
    ring
  have him : (ellipse a b t - circleMap 0 (a + b) t).im = -a * Real.sin t := by
    rw [ellipse_apply]
    simp only [Complex.sub_im, circleMap_zero_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re, mul_one, mul_zero,
      add_zero, zero_add]
    ring
  have hsq : ‖ellipse a b t - circleMap 0 (a + b) t‖ ^ 2 =
      b ^ 2 * Real.cos t ^ 2 + a ^ 2 * Real.sin t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hc := mul_le_mul_of_nonneg_left (Real.cos_sq_le_one t) (sq_nonneg b)
  have hs := mul_le_mul_of_nonneg_left (Real.sin_sq_le_one t) (sq_nonneg a)
  nlinarith [norm_nonneg (ellipse a b t - circleMap 0 (a + b) t), mul_pos ha hb]

/-- The winding number is one at every point of the actual open ellipse. -/
theorem windingNumber_ellipse_inside {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u : ℂ} (hu : u ∈ ball (0 : ℂ) 1) :
    Contour.windingNumber (ellipse a b) 0 (2 * Real.pi)
      (ellipseCoordinates a b ha.ne' hb.ne' u) = 1 := by
  let A := ellipseCoordinates a b ha.ne' hb.ne'
  have hoff (v : ball (0 : ℂ) 1) : A v ∉ ellipse a b '' uIcc 0 (2 * Real.pi) := by
    rw [image_ellipse_uIcc a b ha.ne' hb.ne']
    rintro ⟨w, hw, heq⟩
    have he := A.injective heq
    have hd := v.property
    rw [mem_ball, ← he, mem_sphere.mp hw] at hd
    exact lt_irrefl _ hd
  let f : ball (0 : ℂ) 1 → {z : ℂ // z ∉ ellipse a b '' uIcc 0 (2 * Real.pi)} :=
    fun v ↦ ⟨A v, hoff v⟩
  have hf : Continuous f := (A.continuous.comp continuous_subtype_val).subtype_mk _
  have hlc := (AbsolutelyContinuousOnInterval.isLocallyConstant_windingNumber
    (absolutelyContinuous_ellipse a b) (ellipse_closed a b)).comp_continuous hf
  let : PreconnectedSpace (ball (0 : ℂ) 1) :=
    Subtype.preconnectedSpace (convex_ball (0 : ℂ) 1).isPreconnected
  have he := hlc.apply_eq_of_preconnectedSpace ⟨u, hu⟩ ⟨0, by simp⟩
  have he' : Contour.windingNumber (ellipse a b) 0 (2 * Real.pi) (A u) =
      Contour.windingNumber (ellipse a b) 0 (2 * Real.pi) 0 := by
    simpa only [Function.comp_apply, f, map_zero] using he
  exact he'.trans (windingNumber_ellipse_zero ha hb)

/-- Outside the closed ellipse the winding number vanishes. -/
theorem windingNumber_ellipse_outside {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {u : ℂ} (hu : u ∉ closedBall (0 : ℂ) 1) :
    Contour.windingNumber (ellipse a b) 0 (2 * Real.pi)
      (ellipseCoordinates a b ha hb u) = 0 := by
  let A := ellipseCoordinates a b ha hb
  have hconv : Convex ℝ (A '' closedBall (0 : ℂ) 1) :=
    (convex_closedBall (0 : ℂ) 1).linear_image A.toLinearEquiv.toLinearMap
  have hzero : (0 : ℂ) ∈ A '' closedBall (0 : ℂ) 1 := ⟨0, by simp, map_zero A⟩
  apply Contour.windingNumber_eq_zero_of_starConvex (hconv.starConvex hzero)
    (Contour.IsPiecewiseC1On.of_contDiffOn (contDiff_ellipse a b (n := 1)).contDiffOn)
    (ellipse_closed a b)
  · intro t ht
    have hm : ellipse a b t ∈ ellipse a b '' uIcc 0 (2 * Real.pi) := mem_image_of_mem _ ht
    rw [image_ellipse_uIcc a b ha hb] at hm
    exact image_mono sphere_subset_closedBall hm
  · rintro ⟨v, hv, heq⟩
    exact hu (A.injective heq ▸ hv)

/-- The winding weight of a positive-axis ellipse is the indicator of its actual interior. -/
theorem windingWeight_ellipse {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    windingWeight (ellipse a b) 0 (2 * Real.pi) z =
      (ellipseCoordinates a b ha.ne' hb.ne' '' ball (0 : ℂ) 1).indicator 1 z := by
  let A := ellipseCoordinates a b ha.ne' hb.ne'
  obtain ⟨u, rfl⟩ := A.surjective z
  by_cases htrace : A u ∈ ellipse a b '' uIcc 0 (2 * Real.pi)
  · rw [windingWeight_eq_zero_of_mem htrace, indicator_of_notMem]
    rw [image_ellipse_uIcc a b ha.ne' hb.ne'] at htrace
    obtain ⟨v, hv, heq⟩ := htrace
    rintro ⟨w, hw, heq'⟩
    have he : w = v := A.injective (heq'.trans heq.symm)
    rw [he, mem_ball, mem_sphere.mp hv] at hw
    exact lt_irrefl _ hw
  · rw [windingWeight_eq_of_notMem htrace]
    by_cases hu : u ∈ ball (0 : ℂ) 1
    · rw [windingNumber_ellipse_inside ha hb hu, indicator_of_mem (mem_image_of_mem A hu)]
      simp
    · have hclosed : u ∉ closedBall (0 : ℂ) 1 := by
        intro hc
        have hs : u ∈ sphere (0 : ℂ) 1 := by
          rw [mem_sphere]
          exact le_antisymm (mem_closedBall.mp hc)
            (le_of_not_gt (by simpa only [mem_ball] using hu))
        exact htrace ((image_ellipse_uIcc a b ha.ne' hb.ne').symm ▸ mem_image_of_mem A hs)
      rw [windingNumber_ellipse_outside ha.ne' hb.ne' hclosed, indicator_of_notMem]
      · simp
      · rintro ⟨v, hv, heq⟩
        exact hu (A.injective heq ▸ hv)

/-- The actual affine image of the open unit disc has positive area `π|ab|`. -/
theorem volume_ellipse_image_ball (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    volume (affineMap (ellipseCoordinates a b ha hb) 0 '' Metric.ball (0 : ℂ) 1) =
      ENNReal.ofReal (Real.pi * |a * b|) := by
  rw [volume_affineMap_image _ _ measurableSet_ball.nullMeasurableSet,
    det_ellipseCoordinates, Complex.volume_ball]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.ofReal_mul Real.pi_pos.le, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  exact mul_comm _ _

end TauCeti.Green.Examples
