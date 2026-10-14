/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.AbsolutelyContinuous
public import TauCeti.Analysis.Green.WindingWeight.Basic
public import TauCeti.Analysis.Contour.Winding.Number.Circle
public import TauCeti.Analysis.Contour.Curve.Circle
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Circular area examples

The area form `(-y dx + x dy)/2` has curl one. Its actual circulation around a radius-`R`
circle is `π R²`. The existing winding number makes its winding weight exactly the indicator
of the open disc, including the prescribed zero value on the trace.
-/

public section

noncomputable section

open MeasureTheory Set Metric

namespace TauCeti.Green.Examples

/-- The horizontal coefficient of the standard signed-area form. -/
def areaP (z : ℂ) : ℝ := -z.im / 2

/-- The vertical coefficient of the standard signed-area form. -/
def areaQ (z : ℂ) : ℝ := z.re / 2

/-- Evaluation of the horizontal area coefficient. -/
@[simp] theorem areaP_apply (z : ℂ) : areaP z = -z.im / 2 := by rfl

/-- Evaluation of the vertical area coefficient. -/
@[simp] theorem areaQ_apply (z : ℂ) : areaQ z = z.re / 2 := by rfl

/-- The horizontal coefficient `areaP` of the signed-area form is smooth. -/
theorem contDiff_areaP {n : WithTop ℕ∞} : ContDiff ℝ n areaP :=
  Complex.imCLM.contDiff.neg.div_const 2

/-- The vertical coefficient `areaQ` of the signed-area form is smooth. -/
theorem contDiff_areaQ {n : WithTop ℕ∞} : ContDiff ℝ n areaQ :=
  Complex.reCLM.contDiff.div_const 2

/-- The signed-area form has curl one in the positive basis `(1,I)`. -/
@[simp]
theorem curl_area (z : ℂ) : curl areaP areaQ z = 1 := by
  have hp : HasFDerivAt areaP ((-(2 : ℝ)⁻¹) • Complex.imCLM) z := by
    convert (Complex.imCLM.hasFDerivAt (x := z)).const_smul (-(2 : ℝ)⁻¹) using 1
    ext w
    rw [areaP]
    simp
    ring
  have hq : HasFDerivAt areaQ ((2 : ℝ)⁻¹ • Complex.reCLM) z := by
    convert (Complex.reCLM.hasFDerivAt (x := z)).const_smul (2 : ℝ)⁻¹ using 1
    ext w
    rw [areaQ]
    simp [div_eq_mul_inv, mul_comm]
  rw [curl, hp.fderiv, hq.fderiv]
  norm_num

/-- The actual signed-area circulation integrand on a centered circle is `R²/2`. -/
theorem circulationFun_area_circleMap (R t : ℝ) :
    circulationFun areaP areaQ (circleMap 0 R) t = R ^ 2 / 2 := by
  rw [circulationFun, deriv_circleMap, areaP, areaQ]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, circleMap_zero_re, circleMap_zero_im]
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- Actual circulation of the signed-area form around a radius-`R` circle. -/
theorem integral_circulationFun_area_circleMap (R : ℝ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), circulationFun areaP areaQ (circleMap 0 R) t) =
      Real.pi * R ^ 2 := by
  simp_rw [circulationFun_area_circleMap]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The winding weight of a positively sized circle is the indicator of its open disc. -/
theorem windingWeight_circleMap {R : ℝ} (hR : 0 < R) (z : ℂ) :
    windingWeight (circleMap 0 R) 0 (2 * Real.pi) z = (ball (0 : ℂ) R).indicator 1 z := by
  by_cases ht : z ∈ circleMap 0 R '' uIcc 0 (2 * Real.pi)
  · rw [windingWeight_eq_zero_of_mem ht]
    have hd : dist z 0 = R := by
      simpa only [Complex.image_circleMap_uIcc, mem_sphere, abs_of_pos hR] using ht
    simp only [indicator_of_notMem (show z ∉ ball (0 : ℂ) R by simp [mem_ball, hd])]
  · rw [windingWeight_eq_of_notMem ht]
    by_cases hi : z ∈ ball (0 : ℂ) R
    · rw [Contour.windingNumber_circleMap_eq_one_of_dist_lt (mem_ball.mp hi)]
      simp [hi]
    · have hne : dist z 0 ≠ R := by
        simpa only [Complex.image_circleMap_uIcc, mem_sphere, abs_of_pos hR] using ht
      rw [Contour.windingNumber_circleMap_eq_zero_of_lt_dist hR.le
        (lt_of_le_of_ne (le_of_not_gt (by simpa only [mem_ball] using hi)) hne.symm)]
      simp [hi]

/-- The actual area integral of the circular winding weight is `π R²`. -/
theorem integral_windingWeight_circleMap {R : ℝ} (hR : 0 < R) :
    (∫ z : ℂ, windingWeight (circleMap 0 R) 0 (2 * Real.pi) z) = Real.pi * R ^ 2 := by
  simp_rw [windingWeight_circleMap hR]
  rw [integral_indicator measurableSet_ball]
  simp only [Pi.one_apply]
  rw [setIntegral_const]
  simp only [Measure.real, smul_eq_mul, mul_one]
  rw [Complex.volume_ball]
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le, mul_comm]

end TauCeti.Green.Examples
