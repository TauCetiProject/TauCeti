/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.CurveArea.Basic
public import TauCeti.Analysis.Green.AffineTriangle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Signed ellipse area

The ellipse `(a cos t,b sin t)` has signed-area circulation `πab`. Nonzero axes identify it
with the invertible affine image of the unit circle, whose determinant is `ab`.
-/

public section

noncomputable section

open MeasureTheory Set

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
  rw [circulationFun_def, areaP_apply, areaQ_apply, ellipse_apply, (hasDerivAt_ellipse a b t).deriv]
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

/-- The determinant of the real-axis affine ellipse coordinates is the signed product
of its axes. -/
theorem triangleDet_ellipse (a b : ℝ) : triangleDet 0 (a : ℂ) ((b : ℂ) * Complex.I) = a * b := by
  rw [triangleDet_def]
  simp

/-- Nonzero ellipse axes give the canonical invertible affine coordinates with determinant `ab`. -/
def ellipseCoordinates (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  triangleCoordinates 0 (a : ℂ) ((b : ℂ) * Complex.I)
    (by rw [triangleDet_ellipse]; exact mul_ne_zero ha hb)

/-- The canonical real affine determinant recovers the signed product of the ellipse axes. -/
theorem det_ellipseCoordinates (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (ellipseCoordinates a b ha hb).toLinearEquiv.toLinearMap.det = a * b := by
  rw [ellipseCoordinates, det_triangleCoordinates, triangleDet_ellipse]

/-- The ellipse is the actual invertible affine image of the unit-circle parameterization. -/
theorem ellipse_eq_affine_circle (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ellipse a b = affineMap (ellipseCoordinates a b ha hb) 0 ∘ circleMap 0 1 := by
  ext t
  let A := ellipseCoordinates a b ha hb
  have he (z : ℂ) : A z = z.re • A 1 + z.im • A Complex.I := by
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by simp [Complex.real_smul]
    calc
      A z = A (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg A hz
      _ = _ := by simp only [map_add, map_smul]
  have h1 : A 1 = (a : ℂ) := by simp [A, ellipseCoordinates]
  have hI : A Complex.I = (b : ℂ) * Complex.I := by simp [A, ellipseCoordinates]
  simp only [Function.comp_apply, affineMap_apply, add_zero]
  rw [he, h1, hI, circleMap_zero_re, circleMap_zero_im, ellipse_apply]
  simp only [Complex.real_smul]
  push_cast
  ring

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
