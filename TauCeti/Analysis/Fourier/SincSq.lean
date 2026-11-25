/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

import Mathlib.Analysis.Fourier.Inversion
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.SpecialFunctions.Integrals.SincSq
import TauCeti.Analysis.SpecialFunctions.Integrals.Trigonometric.Fejer
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# The Fourier and cosine transforms of `sinc²`

Unlike `Real.sinc`, whose integral exists only as an improper limit, `x ↦ Real.sinc x ^ 2` is
nonnegative and Lebesgue integrable on `ℝ` (`TauCeti.integrable_sinc_sq`), and its Fourier
transform is a continuous triangular tent of compact support. Rescaling `sinc²` therefore yields
nonnegative `L¹` smoothing kernels on `ℝ` whose frequency support lies in a prescribed bounded
interval, the real-line analogue of the periodic Fejér kernel.

In Mathlib's Fourier normalisation `𝓕 f w = ∫ x, exp (-2 π i x w) f x`, the transform of `sinc²`
is `w ↦ π * max (1 - |π * w|) 0`, supported on `[-π⁻¹, π⁻¹]` (`TauCeti.fourier_sinc_sq`). Written
in angular frequency `ω = 2 * π * w`, its cosine transform is `π * max (1 - |ω| / 2) 0`, supported
on `[-2, 2]` (`TauCeti.integral_sinc_sq_mul_cos`).

## Main results

* `TauCeti.fourier_sinc_sq`:
  `𝓕 (fun x : ℝ ↦ ((Real.sinc x ^ 2 : ℝ) : ℂ)) w = ((π * max (1 - |π * w|) 0 : ℝ) : ℂ)`.
* `TauCeti.integral_sinc_sq_mul_cos`:
  `∫ x : ℝ, Real.sinc x ^ 2 * Real.cos (ω * x) = π * max (1 - |ω| / 2) 0`.
-/

public section

noncomputable section

open MeasureTheory Real Set
open scoped FourierTransform Real

namespace TauCeti

/-- Outside `(-π⁻¹, π⁻¹)`, the triangular tent `max (1 - |π w|) 0` vanishes. -/
private theorem triangle_eq_zero_of_pi_inv_le_abs {w : ℝ} (hw : π⁻¹ ≤ |w|) :
    max (1 - |π * w|) 0 = 0 := by
  refine max_eq_right (sub_nonpos.mpr ?_)
  rw [abs_mul, abs_of_pos pi_pos]
  calc (1 : ℝ) = π * π⁻¹ := (mul_inv_cancel₀ pi_pos.ne').symm
    _ ≤ π * |w| := mul_le_mul_of_nonneg_left hw pi_pos.le

/-- Over `[-π⁻¹, π⁻¹]`, the cosine integral of `w ↦ max (1 - |π w|) 0` against `cos (w (2 π x))`
equals `π⁻¹ sinc(x)²`. -/
private theorem intervalIntegral_triangle_mul_cos (x : ℝ) :
    ∫ w in (-π⁻¹)..π⁻¹, max (1 - |π * w|) 0 * cos (w * (2 * π * x)) = π⁻¹ * sinc x ^ 2 := by
  have heven : Function.Even (fun w : ℝ ↦ max (1 - |π * w|) 0 * cos (w * (2 * π * x))) := by
    intro w
    simp [abs_neg, neg_mul, cos_neg]
  rw [intervalIntegral.integral_eq_two_smul_of_even heven, smul_eq_mul]
  have hcongr : ∫ w in (0 : ℝ)..π⁻¹, max (1 - |π * w|) 0 * cos (w * (2 * π * x)) =
      ∫ w in (0 : ℝ)..π⁻¹, (1 - w / π⁻¹) * cos (w * (2 * π * x)) := by
    refine intervalIntegral.integral_congr fun w hw ↦ ?_
    rw [uIcc_of_le (inv_nonneg.mpr pi_pos.le)] at hw
    have hw_le : π * w ≤ 1 := by
      calc π * w ≤ π * π⁻¹ := mul_le_mul_of_nonneg_left hw.2 pi_pos.le
        _ = 1 := mul_inv_cancel₀ pi_pos.ne'
    rw [abs_of_nonneg (mul_nonneg pi_pos.le hw.1), max_eq_left (sub_nonneg.mpr hw_le),
      div_inv_eq_mul, mul_comm w π]
  rw [hcongr, integral_one_sub_div_mul_cos_mul]
  have harg : π⁻¹ * (2 * π * x) / 2 = x := by field_simp [pi_pos.ne']
  rw [harg]
  ring

/-- The inverse Fourier transform of `w ↦ max (1 - |π w|) 0` is `x ↦ π⁻¹ sinc(x)²`. -/
private theorem fourierInv_triangle (x : ℝ) :
    𝓕⁻ (fun w : ℝ ↦ ((max (1 - |π * w|) 0 : ℝ) : ℂ)) x =
      ((π⁻¹ * sinc x ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourierInv_eq']
  have hsupp : ∀ w : ℝ, w ∉ Ioc (-π⁻¹) π⁻¹ →
      Complex.exp (↑(2 * π * inner ℝ w x) * Complex.I) • ((max (1 - |π * w|) 0 : ℝ) : ℂ) = 0 := by
    intro w hw
    have habs : π⁻¹ ≤ |w| := le_of_not_gt fun hlt ↦
      hw ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
    rw [triangle_eq_zero_of_pi_inv_le_abs habs]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    ← intervalIntegral.integral_of_le (by linarith [inv_pos.mpr pi_pos] : -π⁻¹ ≤ π⁻¹)]
  have hsplit : ∀ w : ℝ,
      Complex.exp (↑(2 * π * inner ℝ w x) * Complex.I) • ((max (1 - |π * w|) 0 : ℝ) : ℂ) =
        ((max (1 - |π * w|) 0 * cos (w * (2 * π * x)) : ℝ) : ℂ) +
          ((max (1 - |π * w|) 0 * sin (w * (2 * π * x)) : ℝ) : ℂ) * Complex.I := fun w ↦ by
    have harg : (↑(2 * π * inner ℝ w x) : ℂ) = ((w * (2 * π * x) : ℝ) : ℂ) := by
      simp only [RCLike.inner_apply, conj_trivial]
      push_cast
      ring
    rw [smul_eq_mul, harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  simp_rw [hsplit]
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous _).intervalIntegrable _ _)
    ((by fun_prop : Continuous _).intervalIntegrable _ _)]
  have hodd : Function.Odd
      (fun w : ℝ ↦ ((max (1 - |π * w|) 0 * sin (w * (2 * π * x)) : ℝ) : ℂ) * Complex.I) := by
    intro w
    simp [abs_neg, neg_mul, sin_neg]
  rw [intervalIntegral.integral_eq_zero_of_odd hodd, add_zero, intervalIntegral.integral_ofReal,
    intervalIntegral_triangle_mul_cos]

/-- **The Fourier transform of `sinc²` is a triangular tent.** Under Mathlib's convention
`𝓕 f w = ∫ x, exp (-2 π i x w) f x`,
`𝓕 (fun x ↦ (sinc x ^ 2 : ℂ)) w = π * max (1 - |π * w|) 0`. -/
theorem fourier_sinc_sq (w : ℝ) :
    𝓕 (fun x : ℝ ↦ ((sinc x ^ 2 : ℝ) : ℂ)) w = ((π * max (1 - |π * w|) 0 : ℝ) : ℂ) := by
  let g : ℝ → ℂ := fun u ↦ ((max (1 - |π * u|) 0 : ℝ) : ℂ)
  have hg_cont : Continuous g := by fun_prop
  have hg_supp : HasCompactSupport g := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc (-π⁻¹) π⁻¹) isCompact_Icc ?_
    intro u hu
    by_contra hnot
    have habs : π⁻¹ ≤ |u| := le_of_not_gt fun hlt ↦ hnot (Ioo_subset_Icc_self (abs_lt.mp hlt))
    exact hu (by simp only [g, triangle_eq_zero_of_pi_inv_le_abs habs, Complex.ofReal_zero])
  have hg_int : Integrable g := hg_cont.integrable_of_hasCompactSupport hg_supp
  have hfinv : 𝓕⁻ g = (π⁻¹ : ℂ) • fun x : ℝ ↦ ((sinc x ^ 2 : ℝ) : ℂ) := by
    ext x
    rw [fourierInv_triangle]
    simp [Pi.smul_apply]
  have hfg_int : Integrable (𝓕 g) := by
    have heven : (fun u : ℝ ↦ g (-u)) = g := funext fun u ↦ by simp [g, abs_neg]
    rw [← heven, ← Real.fourierInv_eq_fourier_comp_neg, hfinv]
    exact integrable_sinc_sq.ofReal.smul (π⁻¹ : ℂ)
  have hinv := congrFun (hg_cont.fourier_fourierInv_eq hg_int hfg_int) w
  rw [hfinv, Real.fourier_const_smul, Pi.smul_apply, smul_eq_mul] at hinv
  calc 𝓕 (fun x : ℝ ↦ ((sinc x ^ 2 : ℝ) : ℂ)) w
      = (π : ℂ) * ((π⁻¹ : ℂ) * 𝓕 (fun x : ℝ ↦ ((sinc x ^ 2 : ℝ) : ℂ)) w) := by
          rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ pi_pos.ne',
            Complex.ofReal_one, one_mul]
    _ = (π : ℂ) * g w := by rw [hinv]
    _ = ((π * max (1 - |π * w|) 0 : ℝ) : ℂ) := by simp [g]

/-- **The cosine transform of `sinc²` in angular frequency.** For every real `ω`,
`∫ x, sinc x ^ 2 * cos (ω * x) = π * max (1 - |ω| / 2) 0`; in particular it vanishes whenever
`2 ≤ |ω|`. -/
theorem integral_sinc_sq_mul_cos (ω : ℝ) :
    ∫ x : ℝ, sinc x ^ 2 * cos (ω * x) = π * max (1 - |ω| / 2) 0 := by
  have h := congrArg Complex.re (fourier_sinc_sq (ω / (2 * π)))
  rw [Real.fourier_eq, Complex.ofReal_re] at h
  have hint : Integrable (fun x : ℝ ↦
      𝐞 (-inner ℝ x (ω / (2 * π))) • ((sinc x ^ 2 : ℝ) : ℂ)) :=
    integrable_sinc_sq.ofReal.fourierChar_smul
      (Continuous.aemeasurable (by fun_prop))
  rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint] at h
  have hre : ∀ x : ℝ, Complex.reCLM (𝐞 (-inner ℝ x (ω / (2 * π))) •
      ((sinc x ^ 2 : ℝ) : ℂ)) = sinc x ^ 2 * cos (ω * x) := fun x ↦ by
    have harg : (2 : ℝ) * π * -inner ℝ x (ω / (2 * π)) = -(ω * x) := by
      simp only [RCLike.inner_apply, conj_trivial]
      field_simp [pi_pos.ne']
    rw [Complex.reCLM_apply, Circle.smul_def, Real.fourierChar_apply, harg, smul_eq_mul,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, cos_neg]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero]
    ring
  have habs : |π * (ω / (2 * π))| = |ω| / 2 := by
    have hpi : π * (ω / (2 * π)) = ω / 2 := by field_simp [pi_pos.ne']
    rw [hpi, abs_div, abs_two]
  simp_rw [hre] at h
  rwa [habs] at h

end TauCeti
