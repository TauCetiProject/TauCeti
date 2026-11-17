/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# Integrability and Fourier transform of `sinc²`

This file proves the `L¹` integrability, Fourier transform, cosine transform, and total mass of
the squared sinc function `x ↦ Real.sinc x ^ 2` on `ℝ`.

The algebraic identity `(1 + x²) sinc(x)² = sinc(x)² + sin(x)² ≤ 2` yields integrability by
comparison with `(1 + x²)⁻¹`. Direct integration of the triangular tent `1 - |y| / a` against
`cos (y v)` and `exp (i y v)` identifies `x ↦ π⁻¹ sinc(x)²` as the inverse Fourier transform of
the continuous compactly supported triangle `w ↦ max (1 - |π w|) 0`. Fourier inversion then gives
the forward Fourier transform of `sinc²`, its cosine transform, and its full-line and half-line
masses `π` and `π / 2`.

## Main results

* `TauCeti.integrable_sinc_sq`: `x ↦ Real.sinc x ^ 2` is Lebesgue integrable on `ℝ`.
* `TauCeti.integral_one_sub_abs_div_mul_cos` and `TauCeti.integral_one_sub_abs_div_mul_cexp`:
  the triangle cosine and exponential integrals evaluate to `a * Real.sinc (a * v / 2) ^ 2`.
* `TauCeti.fourier_sinc_sq`: the Fourier transform of `x ↦ (Real.sinc x ^ 2 : ℂ)` is
  `w ↦ π * max (1 - |π w|) 0`.
* `TauCeti.integral_sinc_sq` and `TauCeti.integral_Ioi_sinc_sq`:
  `∫ x, Real.sinc x ^ 2 = π` and `∫ x in Ioi 0, Real.sinc x ^ 2 = π / 2`.
* `TauCeti.integral_sinc_sq_mul_cos`:
  `∫ x, Real.sinc x ^ 2 * Real.cos (ω * x) = π * max (1 - |ω| / 2) 0`.
-/

public section

noncomputable section

open MeasureTheory Real Set
open scoped FourierTransform Real

namespace TauCeti

/-- The squared sinc function is Lebesgue integrable on `ℝ`, dominated by `2 / (1 + x²)`. -/
theorem integrable_sinc_sq : Integrable (fun x : ℝ ↦ sinc x ^ 2) := by
  refine (integrable_inv_one_add_sq.const_mul 2).mono'
    (by fun_prop : Continuous fun x : ℝ ↦ sinc x ^ 2).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  rw [norm_of_nonneg (sq_nonneg _), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h1 : sinc x ^ 2 ≤ 1 := by nlinarith [abs_le.mp (abs_sinc_le_one x)]
  have h2 : sin x ^ 2 ≤ 1 := sin_sq_le_one x
  have hid : sinc x ^ 2 * (1 + x ^ 2) = sinc x ^ 2 + sin x ^ 2 := by
    rw [← mul_sinc x]
    ring
  linarith

/-- Integrating an even function over `[-a, a]` doubles the integral over `[0, a]`. -/
private theorem integral_neg_self_eq_two_mul_of_even {f : ℝ → ℝ} (heven : ∀ y, f (-y) = f y)
    (a : ℝ) (hf : IntervalIntegrable f volume 0 a) :
    ∫ y in (-a)..a, f y = 2 * ∫ y in (0 : ℝ)..a, f y := by
  have hneg : IntervalIntegrable f volume (-a) 0 :=
    (IntervalIntegrable.iff_comp_neg (a := -a) (b := 0) (f := f)).mpr
      (by simpa [heven] using hf.symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals hneg hf]
  have hcomp : ∫ y in (-a)..0, f y = ∫ y in (0 : ℝ)..a, f y := by
    simpa [heven] using (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := a) f).symm
  rw [hcomp, two_mul]

/-- The triangle cosine integral on `[0, a]` for `0 < a` and `v ≠ 0`. -/
private theorem integral_zero_one_sub_div_mul_cos {a v : ℝ} (ha : 0 < a) (hv : v ≠ 0) :
    ∫ y in (0 : ℝ)..a, (1 - y / a) * cos (y * v) = (1 - cos (a * v)) / (a * v ^ 2) := by
  let F : ℝ → ℝ := fun y ↦ (1 - y / a) * sin (y * v) / v - cos (y * v) / (a * v ^ 2)
  have hderiv : ∀ y ∈ uIcc (0 : ℝ) a, HasDerivAt F ((1 - y / a) * cos (y * v)) y := by
    intro y _
    have h1 : HasDerivAt (fun t ↦ 1 - t / a) (-(1 / a)) y :=
      ((hasDerivAt_id' y).div_const a).const_sub 1
    have hmul : HasDerivAt (fun t ↦ t * v) v y := by
      simpa using (hasDerivAt_id' y).mul_const v
    have h2 : HasDerivAt (fun t ↦ sin (t * v)) (cos (y * v) * v) y := hmul.sin
    have h3 : HasDerivAt (fun t ↦ cos (t * v)) (-sin (y * v) * v) y := hmul.cos
    convert ((h1.mul h2).div_const v).sub (h3.div_const (a * v ^ 2)) using 1
    field_simp [ha.ne', hv]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous _).intervalIntegrable 0 a)]
  simp only [F, div_self ha.ne', sub_self, zero_mul, zero_div, zero_sub, mul_zero, sin_zero,
    cos_zero, sub_zero, sub_neg_eq_add]
  ring

/-- The cosine transform of the triangular tent `1 - |y| / a` on `[-a, a]` evaluates to
`a * Real.sinc (a * v / 2) ^ 2` for every `0 ≤ a` and `v : ℝ`. -/
theorem integral_one_sub_abs_div_mul_cos {a : ℝ} (ha : 0 ≤ a) (v : ℝ) :
    ∫ y in (-a)..a, (1 - |y| / a) * cos (y * v) = a * sinc (a * v / 2) ^ 2 := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  have heven : ∀ y : ℝ, (1 - |(-y)| / a) * cos ((-y) * v) = (1 - |y| / a) * cos (y * v) :=
    fun y ↦ by rw [abs_neg, neg_mul, cos_neg]
  rw [integral_neg_self_eq_two_mul_of_even heven a
    ((by fun_prop : Continuous _).intervalIntegrable 0 a)]
  have hcongr : ∫ y in (0 : ℝ)..a, (1 - |y| / a) * cos (y * v) =
      ∫ y in (0 : ℝ)..a, (1 - y / a) * cos (y * v) :=
    intervalIntegral.integral_congr fun y hy ↦ by
      rw [uIcc_of_le ha.le] at hy
      rw [abs_of_nonneg hy.1]
  rw [hcongr]
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [mul_zero, cos_zero, mul_one, zero_div, sinc_zero, one_pow]
    have hF : ∀ y ∈ uIcc (0 : ℝ) a, HasDerivAt (fun t ↦ t - t ^ 2 / (2 * a)) (1 - y / a) y := by
      intro y _
      have h2 : HasDerivAt (fun t ↦ t ^ 2 / (2 * a)) (y / a) y := by
        convert (hasDerivAt_pow 2 y).div_const (2 * a) using 1
        norm_num
        field_simp [ha.ne']
      exact (hasDerivAt_id' y).sub h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((by fun_prop : Continuous _).intervalIntegrable 0 a)]
    field_simp [ha.ne']
    ring
  · rw [integral_zero_one_sub_div_mul_cos ha hv]
    have hcos : 1 - cos (a * v) = 2 * sin (a * v / 2) ^ 2 := by
      have h := cos_two_mul' (a * v / 2)
      rw [mul_div_cancel₀ _ two_ne_zero] at h
      linarith [sin_sq_add_cos_sq (a * v / 2)]
    have hav : a * v / 2 ≠ 0 := div_ne_zero (mul_ne_zero ha.ne' hv) two_ne_zero
    rw [hcos, sinc_of_ne_zero hav]
    field_simp [ha.ne', hv]

/-- The complex exponential integral of the triangular tent `1 - |y| / a` on `[-a, a]` evaluates to
`a * Real.sinc (a * v / 2) ^ 2` for every `0 ≤ a` and `v : ℝ`. -/
theorem integral_one_sub_abs_div_mul_cexp {a : ℝ} (ha : 0 ≤ a) (v : ℝ) :
    ∫ y in (-a)..a, ((1 - |y| / a : ℝ) : ℂ) * Complex.exp (Complex.I * y * v) =
      ((a * sinc (a * v / 2) ^ 2 : ℝ) : ℂ) := by
  have hsplit : ∀ y : ℝ, ((1 - |y| / a : ℝ) : ℂ) * Complex.exp (Complex.I * y * v) =
      (((1 - |y| / a) * cos (y * v) : ℝ) : ℂ) +
        (((1 - |y| / a) * sin (y * v) : ℝ) : ℂ) * Complex.I := fun y ↦ by
    have hexp : Complex.exp (Complex.I * y * v) =
        (cos (y * v) : ℂ) + (sin (y * v) : ℂ) * Complex.I := by
      have : Complex.I * (y : ℂ) * (v : ℂ) = ((y * v : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin]
    rw [hexp]
    push_cast
    ring
  simp_rw [hsplit]
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous _).intervalIntegrable (-a) a)
    ((by fun_prop : Continuous _).intervalIntegrable (-a) a)]
  have hodd : Function.Odd (fun y : ℝ ↦ (((1 - |y| / a) * sin (y * v) : ℝ) : ℂ) * Complex.I) := by
    intro y
    simp only [abs_neg, neg_mul, sin_neg, mul_neg, Complex.ofReal_neg]
  rw [intervalIntegral.integral_eq_zero_of_odd hodd, add_zero, intervalIntegral.integral_ofReal,
    integral_one_sub_abs_div_mul_cos ha v]

/-- Outside `(-π⁻¹, π⁻¹)`, the triangle `max (1 - |π w|) 0` vanishes. -/
private theorem triangle_eq_zero_of_pi_inv_le_abs {w : ℝ} (hw : π⁻¹ ≤ |w|) :
    max (1 - |π * w|) 0 = 0 := by
  have habs : 1 ≤ |π * w| := by
    rw [abs_mul, abs_of_pos pi_pos]
    calc (1 : ℝ) = π * π⁻¹ := (mul_inv_cancel₀ pi_pos.ne').symm
      _ ≤ π * |w| := mul_le_mul_of_nonneg_left hw pi_pos.le
  exact max_eq_right (sub_nonpos.mpr habs)

/-- The inverse Fourier transform of the triangle `w ↦ max (1 - |π w|) 0` is `x ↦ π⁻¹ sinc(x)²`. -/
private theorem fourierInv_triangle (x : ℝ) :
    𝓕⁻ (fun w : ℝ ↦ ((max (1 - |π * w|) 0 : ℝ) : ℂ)) x =
      ((π⁻¹ * sinc x ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourierInv_eq']
  have hsupp : ∀ w : ℝ, w ∉ Ioc (-π⁻¹) π⁻¹ →
      Complex.exp (↑(2 * π * inner ℝ w x) * Complex.I) • ((max (1 - |π * w|) 0 : ℝ) : ℂ) = 0 := by
    intro w hw
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hw
    have habs : π⁻¹ ≤ |w| := by
      rcases hw with h | h
      · exact le_trans (by linarith) (neg_le_abs w)
      · exact le_trans h.le (le_abs_self w)
    rw [triangle_eq_zero_of_pi_inv_le_abs habs]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    ← intervalIntegral.integral_of_le (by linarith [inv_pos.mpr pi_pos] : -π⁻¹ ≤ π⁻¹)]
  have hcongr : ∫ w in (-π⁻¹)..π⁻¹,
        Complex.exp (↑(2 * π * inner ℝ w x) * Complex.I) • ((max (1 - |π * w|) 0 : ℝ) : ℂ) =
      ∫ w in (-π⁻¹)..π⁻¹,
        ((1 - |(2 * π * w)| / 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((2 * π * w : ℝ) : ℂ) * x) := by
    refine intervalIntegral.integral_congr fun w hw ↦ ?_
    rw [uIcc_of_le (by linarith [inv_pos.mpr pi_pos])] at hw
    have habs : |π * w| ≤ 1 := by
      rw [abs_mul, abs_of_pos pi_pos]
      calc π * |w| ≤ π * π⁻¹ := mul_le_mul_of_nonneg_left (abs_le.mpr hw) pi_pos.le
        _ = 1 := mul_inv_cancel₀ pi_pos.ne'
    have h1 : |2 * π * w| / 2 = |π * w| := by
      rw [mul_assoc, abs_mul, abs_of_pos two_pos]; ring
    rw [smul_eq_mul, max_eq_left (sub_nonneg.mpr habs), h1, mul_comm]
    congr 2
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  rw [hcongr]
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun y : ℝ ↦ ((1 - |y| / 2 : ℝ) : ℂ) * Complex.exp (Complex.I * y * x))
    (a := -π⁻¹) (b := π⁻¹) (c := 2 * π) (mul_ne_zero two_ne_zero pi_pos.ne')
  have hbd1 : 2 * π * -π⁻¹ = -2 := by field_simp [pi_pos.ne']
  have hbd2 : 2 * π * π⁻¹ = 2 := by field_simp [pi_pos.ne']
  rw [hbd1, hbd2, integral_one_sub_abs_div_mul_cexp (by norm_num : (0 : ℝ) ≤ 2) x,
    mul_div_cancel_left₀ x two_ne_zero] at hsub
  rw [hsub]
  simp only [Complex.real_smul]
  push_cast
  field_simp [pi_pos.ne']

/-- The Fourier transform of `x ↦ (Real.sinc x ^ 2 : ℂ)` is the triangular tent
`w ↦ π * max (1 - |π w|) 0`. -/
theorem fourier_sinc_sq (w : ℝ) :
    𝓕 (fun x : ℝ ↦ ((sinc x ^ 2 : ℝ) : ℂ)) w = ((π * max (1 - |π * w|) 0 : ℝ) : ℂ) := by
  let g : ℝ → ℂ := fun u ↦ ((max (1 - |π * u|) 0 : ℝ) : ℂ)
  have hg_cont : Continuous g := by fun_prop
  have hg_supp : HasCompactSupport g := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc (-π⁻¹) π⁻¹) isCompact_Icc ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_contra hnot
    rw [mem_Icc, not_and_or, not_le, not_le] at hnot
    have habs : π⁻¹ ≤ |u| := by
      rcases hnot with h | h
      · exact le_trans (by linarith) (neg_le_abs u)
      · exact le_trans h.le (le_abs_self u)
    exact hu (by simp only [g, triangle_eq_zero_of_pi_inv_le_abs habs, Complex.ofReal_zero])
  have hg_int : Integrable g := hg_cont.integrable_of_hasCompactSupport hg_supp
  have hfinv : 𝓕⁻ g = fun x : ℝ ↦ ((π⁻¹ * sinc x ^ 2 : ℝ) : ℂ) := funext fourierInv_triangle
  have hfeq : 𝓕 g = fun x : ℝ ↦ ((π⁻¹ * sinc x ^ 2 : ℝ) : ℂ) := by
    have heven : (fun u : ℝ ↦ g (-u)) = g := funext fun u ↦ by simp [g, abs_neg]
    have hinv : 𝓕 g = 𝓕⁻ g := by
      rw [Real.fourierInv_eq_fourier_comp_neg, heven]
    rw [hinv, hfinv]
  have hfg_int : Integrable (𝓕 g) := by
    rw [hfeq]
    exact (integrable_sinc_sq.const_mul π⁻¹).ofReal
  have hinv := congrFun (hg_cont.fourier_fourierInv_eq hg_int hfg_int) w
  rw [hfinv] at hinv
  have hscale : 𝓕 (fun x : ℝ ↦ ((π⁻¹ * sinc x ^ 2 : ℝ) : ℂ)) w =
      (π⁻¹ : ℂ) * 𝓕 (fun x : ℝ ↦ ((sinc x ^ 2 : ℝ) : ℂ)) w := by
    simp only [Real.fourier_real_eq_integral_exp_smul, Complex.ofReal_mul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1 with x
    push_cast
    ring
  rw [hscale] at hinv
  calc 𝓕 (fun x : ℝ ↦ ((sinc x ^ 2 : ℝ) : ℂ)) w
      = (π : ℂ) * ((π⁻¹ : ℂ) * 𝓕 (fun x : ℝ ↦ ((sinc x ^ 2 : ℝ) : ℂ)) w) := by
          rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ pi_pos.ne',
            Complex.ofReal_one, one_mul]
    _ = (π : ℂ) * g w := by rw [hinv]
    _ = ((π * max (1 - |π * w|) 0 : ℝ) : ℂ) := by push_cast; rfl

/-- The total mass of `sinc²` on `ℝ` is `π`. -/
theorem integral_sinc_sq : ∫ x : ℝ, sinc x ^ 2 = π := by
  have h := fourier_sinc_sq 0
  rw [Real.fourier_real_eq_integral_exp_smul] at h
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul, abs_zero,
    sub_zero, max_eq_left zero_le_one, mul_one] at h
  have h' : Complex.ofRealCLM (∫ x : ℝ, sinc x ^ 2) = Complex.ofRealCLM π := by
    rw [← Complex.ofRealCLM.integral_comp_comm integrable_sinc_sq]
    simpa only [Complex.ofRealCLM_apply] using h
  exact Complex.ofReal_inj.mp h'

/-- The integral of `sinc²` on the positive half-line `(0, ∞)` is `π / 2`. -/
theorem integral_Ioi_sinc_sq : ∫ x in Ioi (0 : ℝ), sinc x ^ 2 = π / 2 := by
  have h := integral_comp_abs (f := fun x : ℝ ↦ sinc x ^ 2)
  have heven : (fun x : ℝ ↦ sinc |x| ^ 2) = fun x : ℝ ↦ sinc x ^ 2 := funext fun x ↦ by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, sinc_neg]
  rw [heven, integral_sinc_sq] at h
  linarith

/-- The cosine transform of `sinc²`: `∫ x, sinc(x)² cos(ω x) = π max (1 - |ω| / 2) 0`.
In particular it vanishes whenever `2 ≤ |ω|`. -/
theorem integral_sinc_sq_mul_cos (ω : ℝ) :
    ∫ x : ℝ, sinc x ^ 2 * cos (ω * x) = π * max (1 - |ω| / 2) 0 := by
  have h := congrArg Complex.re (fourier_sinc_sq (ω / (2 * π)))
  rw [Real.fourier_real_eq_integral_exp_smul, Complex.ofReal_re] at h
  have hint : Integrable (fun x : ℝ ↦
      Complex.exp (↑(-2 * π * x * (ω / (2 * π))) * Complex.I) • ((sinc x ^ 2 : ℝ) : ℂ)) := by
    have := (Real.fourierIntegral_convergent_iff (μ := volume)
      (f := fun x : ℝ ↦ ((sinc x ^ 2 : ℝ) : ℂ)) (ω / (2 * π))).mpr integrable_sinc_sq.ofReal
    simpa only [Real.fourierChar_apply, Circle.smul_def, RCLike.inner_apply, conj_trivial,
      mul_neg, neg_mul, mul_assoc, mul_comm (ω / (2 * π))] using this
  rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint] at h
  have hre : ∀ x : ℝ, Complex.reCLM (Complex.exp (↑(-2 * π * x * (ω / (2 * π))) * Complex.I) •
      ((sinc x ^ 2 : ℝ) : ℂ)) = sinc x ^ 2 * cos (ω * x) := fun x ↦ by
    have harg : -2 * π * x * (ω / (2 * π)) = -(ω * x) := by field_simp [pi_pos.ne']
    rw [Complex.reCLM_apply, harg, smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, cos_neg]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero]
    ring
  have habs : |π * (ω / (2 * π))| = |ω| / 2 := by
    have hpi : π * (ω / (2 * π)) = ω / 2 := by field_simp [pi_pos.ne']
    rw [hpi, abs_div, abs_two]
  simp_rw [hre] at h
  rwa [habs] at h

end TauCeti
