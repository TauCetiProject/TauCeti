/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Complex.VerticalStrip.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.ExpDecay
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.NormSq
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Poisson kernels of the unit vertical strip

In classical complex analysis, bounded harmonic functions on the open vertical strip
`0 < re ζ < 1` are represented from their boundary values on `re ζ = 0` and `re ζ = 1` by the two
strip Poisson kernels:

* `TauCeti.stripPoisson₀ θ t = sin (π θ) / (2 (cosh (π t) - cos (π θ)))`, strictly positive for
  `0 < θ < 1` with integral `1 - θ` for `0 < θ ≤ 1` (`TauCeti.integral_stripPoisson₀`);
* `TauCeti.stripPoisson₁ θ t = sin (π θ) / (2 (cosh (π t) + cos (π θ)))`, strictly positive for
  `0 < θ < 1` with integral `θ` for `0 ≤ θ < 1` (`TauCeti.integral_stripPoisson₁`).

Evaluating the kernel formulas directly at the boundary points `θ = 0` or `θ = 1` yields zero
(`TauCeti.stripPoisson₀_zero`, `TauCeti.stripPoisson₀_one`, `TauCeti.stripPoisson₁_zero`,
`TauCeti.stripPoisson₁_one`). Here we formalize their mass concentration near `0`
(`TauCeti.tendsto_intervalIntegral_stripPoisson₀_nhdsGT`,
`TauCeti.tendsto_intervalIntegral_stripPoisson₁_nhdsLT`) and the resulting uniform one-sided
approximate-identity lower bounds for nonnegative bounded uniformly continuous data, both at fixed
centers (`TauCeti.exists_forall_sub_le_integral_mul_stripPoisson₀`,
`TauCeti.exists_forall_sub_le_integral_mul_stripPoisson₁`) and along contracted centers
(`TauCeti.exists_forall_sub_le_integral_mul_contracted_stripPoisson₀`,
`TauCeti.exists_forall_sub_le_integral_mul_contracted_stripPoisson₁`).

The holomorphic strip kernels `TauCeti.holoPoisson₀` and `TauCeti.holoPoisson₁` realize
`stripPoisson₀` and `stripPoisson₁` as real parts on the open strip, yielding holomorphic
convolutions on `0 < re ζ < 1` for complex integrable boundary data
(`TauCeti.differentiableOn_integral_holoPoisson₀`,
`TauCeti.differentiableOn_integral_holoPoisson₁`).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Metric Real Set Topology

namespace TauCeti

/-! ### The Poisson kernels of the unit vertical strip -/

/-- The left boundary Poisson kernel `P₀(θ, t) = sin (π θ) / (2 (cosh (π t) - cos (π θ)))` of the
vertical strip `0 ≤ re z ≤ 1`. For `0 < θ < 1` it is strictly positive with integral `1 - θ` over
`ℝ` (classically representing the harmonic contribution from `re z = 0`). -/
def stripPoisson₀ (θ t : ℝ) : ℝ :=
  Real.sin (π * θ) / (2 * (Real.cosh (π * t) - Real.cos (π * θ)))

/-- The right boundary Poisson kernel `P₁(θ, t) = sin (π θ) / (2 (cosh (π t) + cos (π θ)))` of the
vertical strip `0 ≤ re z ≤ 1`. For `0 < θ < 1` it is strictly positive with integral `θ` over `ℝ`
(classically representing the harmonic contribution from `re z = 1`). -/
def stripPoisson₁ (θ t : ℝ) : ℝ :=
  Real.sin (π * θ) / (2 * (Real.cosh (π * t) + Real.cos (π * θ)))

/-- Defining formula for the left strip Poisson kernel `stripPoisson₀`. -/
theorem stripPoisson₀_def (θ t : ℝ) :
    stripPoisson₀ θ t = Real.sin (π * θ) / (2 * (Real.cosh (π * t) - Real.cos (π * θ))) := (rfl)

/-- Defining formula for the right strip Poisson kernel `stripPoisson₁`. -/
theorem stripPoisson₁_def (θ t : ℝ) :
    stripPoisson₁ θ t = Real.sin (π * θ) / (2 * (Real.cosh (π * t) + Real.cos (π * θ))) := (rfl)

@[simp] theorem stripPoisson₀_neg (θ t : ℝ) : stripPoisson₀ θ (-t) = stripPoisson₀ θ t := by
  simp [stripPoisson₀_def, mul_neg, Real.cosh_neg]

@[simp] theorem stripPoisson₁_neg (θ t : ℝ) : stripPoisson₁ θ (-t) = stripPoisson₁ θ t := by
  simp [stripPoisson₁_def, mul_neg, Real.cosh_neg]

/-- Reflecting `θ ↦ 1 - θ` exchanges the two strip Poisson kernels. -/
theorem stripPoisson₀_one_sub (θ t : ℝ) : stripPoisson₀ (1 - θ) t = stripPoisson₁ θ t := by
  have harg : π * (1 - θ) = π - π * θ := by ring
  rw [stripPoisson₀_def, stripPoisson₁_def, harg, Real.sin_pi_sub, Real.cos_pi_sub, sub_neg_eq_add]

/-- Reflecting `θ ↦ 1 - θ` exchanges the two strip Poisson kernels. -/
theorem stripPoisson₁_one_sub (θ t : ℝ) : stripPoisson₁ (1 - θ) t = stripPoisson₀ θ t := by
  simpa using (stripPoisson₀_one_sub (1 - θ) t).symm

private theorem stripPoisson₁_eq_stripPoisson₀_one_sub (θ : ℝ) :
    stripPoisson₁ θ = stripPoisson₀ (1 - θ) := funext fun t => (stripPoisson₀_one_sub θ t).symm

private theorem stripPoisson₀_eq_zero_of_sin_eq_zero {θ : ℝ} (h : Real.sin (π * θ) = 0) :
    stripPoisson₀ θ = 0 := by ext t; simp [stripPoisson₀_def, h]

@[simp] theorem stripPoisson₀_zero (t : ℝ) : stripPoisson₀ 0 t = 0 := by simp [stripPoisson₀_def]
@[simp] theorem stripPoisson₀_one (t : ℝ) : stripPoisson₀ 1 t = 0 := by simp [stripPoisson₀_def]
@[simp] theorem stripPoisson₁_zero (t : ℝ) : stripPoisson₁ 0 t = 0 := by simp [stripPoisson₁_def]
@[simp] theorem stripPoisson₁_one (t : ℝ) : stripPoisson₁ 1 t = 0 := by simp [stripPoisson₁_def]

/-- On the open interval `0 < θ < 1`, the left strip Poisson kernel is strictly positive. -/
theorem stripPoisson₀_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) : 0 < stripPoisson₀ θ t :=
  have hsin := sin_pi_mul_pos_of_pos_of_lt_one hθ.1 hθ.2
  div_pos hsin (mul_pos zero_lt_two (cosh_sub_cos_pos_of_sin_ne_zero hsin.ne' (π * t)))

/-- On the open interval `0 < θ < 1`, the right strip Poisson kernel is strictly positive. -/
theorem stripPoisson₁_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) : 0 < stripPoisson₁ θ t :=
  stripPoisson₀_one_sub θ t ▸ stripPoisson₀_pos ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩ t

/-- On the closed interval `0 ≤ θ ≤ 1`, the left strip Poisson kernel is nonnegative. -/
theorem stripPoisson₀_nonneg {θ : ℝ} (hθ : θ ∈ Icc 0 1) (t : ℝ) : 0 ≤ stripPoisson₀ θ t := by
  rcases eq_or_lt_of_le hθ.1 with rfl | h0; · simp
  rcases eq_or_lt_of_le hθ.2 with rfl | h1; · simp
  exact (stripPoisson₀_pos ⟨h0, h1⟩ t).le

/-- On the closed interval `0 ≤ θ ≤ 1`, the right strip Poisson kernel is nonnegative. -/
theorem stripPoisson₁_nonneg {θ : ℝ} (hθ : θ ∈ Icc 0 1) (t : ℝ) : 0 ≤ stripPoisson₁ θ t :=
  stripPoisson₀_one_sub θ t ▸ stripPoisson₀_nonneg ⟨sub_nonneg.2 hθ.2, sub_le_self 1 hθ.1⟩ t

/-- For every real `θ`, `t ↦ stripPoisson₀ θ t` is continuous on `ℝ`. -/
@[fun_prop] theorem continuous_stripPoisson₀ (θ : ℝ) : Continuous (stripPoisson₀ θ) := by
  by_cases h : Real.sin (π * θ) = 0
  · rw [stripPoisson₀_eq_zero_of_sin_eq_zero h]; exact continuous_const
  exact Continuous.div continuous_const (by fun_prop) fun t =>
    (mul_pos zero_lt_two (cosh_sub_cos_pos_of_sin_ne_zero h (π * t))).ne'

/-- For every real `θ`, `t ↦ stripPoisson₁ θ t` is continuous on `ℝ`. -/
@[fun_prop] theorem continuous_stripPoisson₁ (θ : ℝ) : Continuous (stripPoisson₁ θ) :=
  stripPoisson₁_eq_stripPoisson₀_one_sub θ ▸ continuous_stripPoisson₀ (1 - θ)

private theorem hasDerivAt_stripPoisson₀_primitive {θ : ℝ} (hsin : Real.sin (π * θ) ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun s => π⁻¹ * Real.arctan ((Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ)))
      (stripPoisson₀ θ t) t := by
  have hlin : HasDerivAt (fun s => (Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ))
      (π * Real.exp (π * t) / Real.sin (π * θ)) t := by
    simpa [mul_comm] using
      (((hasDerivAt_id t).const_mul π).exp.sub_const (Real.cos (π * θ))).div_const _
  refine (((Real.hasDerivAt_arctan _).comp t hlin).const_mul π⁻¹).congr_deriv ?_
  have hden : 2 * (Real.cosh (π * t) - Real.cos (π * θ)) = Real.exp (-(π * t)) *
      ((Real.exp (π * t) - Real.cos (π * θ)) ^ 2 + Real.sin (π * θ) ^ 2) := by
    rw [Real.cosh_eq, Real.exp_neg]; field_simp [(Real.exp_pos (π * t)).ne']
    linear_combination -(Real.cos_sq_add_sin_sq (π * θ))
  have hsq : (Real.exp (π * t) - Real.cos (π * θ)) ^ 2 + Real.sin (π * θ) ^ 2 ≠ 0 := by positivity
  rw [stripPoisson₀_def, hden, Real.exp_neg]
  field_simp [pi_ne_zero, (Real.exp_pos (π * t)).ne', hsin, hsq]; ring

/-- For every real `θ`, the left strip Poisson kernel is integrable on `ℝ`. -/
theorem integrable_stripPoisson₀ (θ : ℝ) : Integrable (stripPoisson₀ θ) := by
  by_cases hsin : Real.sin (π * θ) = 0; · simp [stripPoisson₀_eq_zero_of_sin_eq_zero hsin]
  have hc : 0 < 1 - |Real.cos (π * θ)| := sub_pos.2 (abs_cos_lt_one_of_sin_ne_zero hsin)
  have hIoi : IntegrableOn (stripPoisson₀ θ) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 pi_pos).const_mul
      (|Real.sin (π * θ)| / (1 - |Real.cos (π * θ)|))).mono'
      (continuous_stripPoisson₀ θ).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    have hcosh : Real.exp (π * t) / 2 ≤ Real.cosh (π * t) :=
      Real.cosh_eq _ ▸ by linarith [Real.exp_pos (-(π * t))]
    have hden : (1 - |Real.cos (π * θ)|) * Real.exp (π * t) ≤
        2 * (Real.cosh (π * t) - Real.cos (π * θ)) := by
      nlinarith [one_sub_abs_cos_mul_cosh_le (π * θ) (π * t), hcosh]
    rw [Real.norm_eq_abs, stripPoisson₀_def, abs_div,
      abs_of_pos (mul_pos zero_lt_two (cosh_sub_cos_pos_of_sin_ne_zero hsin (π * t)))]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hc (Real.exp_pos _)) hden).trans_eq
      (by rw [neg_mul, Real.exp_neg]; field_simp [hc.ne'])
  have hIic : IntegrableOn (stripPoisson₀ θ) (Iic 0) := by
    simpa [Function.comp_def, stripPoisson₀_neg, show Homeomorph.neg ℝ ⁻¹' Ici (0 : ℝ) = Iic 0 by
      ext; simp] using
      ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding (f := stripPoisson₀ θ) (s := Ici 0)).2
        ((integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2 hIoi)
  exact integrableOn_univ.1 (Iic_union_Ioi (a := (0 : ℝ)) ▸ hIic.union hIoi)

/-- For every real `θ`, the right strip Poisson kernel is integrable on `ℝ`. -/
theorem integrable_stripPoisson₁ (θ : ℝ) : Integrable (stripPoisson₁ θ) :=
  stripPoisson₁_eq_stripPoisson₀_one_sub θ ▸ integrable_stripPoisson₀ (1 - θ)

private theorem inv_pi_mul_pi_div_two : π⁻¹ * (π / 2) = (2⁻¹ : ℝ) := by field_simp [pi_ne_zero]

/-- For `0 < θ ≤ 1`, the left strip Poisson kernel has total integral `1 - θ` on `ℝ`. -/
theorem integral_stripPoisson₀ {θ : ℝ} (hθ : θ ∈ Ioc 0 1) : ∫ t, stripPoisson₀ θ t = 1 - θ := by
  rcases eq_or_lt_of_le hθ.2 with rfl | h1; · simp
  have hsin := sin_pi_mul_pos_of_pos_of_lt_one hθ.1 h1
  have htop : Tendsto (fun s => π⁻¹ * Real.arctan ((Real.exp (π * s) - Real.cos (π * θ)) /
      Real.sin (π * θ))) atTop (𝓝 (2⁻¹ : ℝ)) := inv_pi_mul_pi_div_two ▸
    ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop pi_pos)).atTop_add
        tendsto_const_nhds).atTop_div_const hsin)).const_mul π⁻¹
  have hval : π⁻¹ * Real.arctan ((0 - Real.cos (π * θ)) / Real.sin (π * θ)) = θ - 2⁻¹ := by
    rw [zero_sub, show -Real.cos (π * θ) / Real.sin (π * θ) = Real.tan (π * θ - π / 2) by
      rw [Real.tan_eq_sin_div_cos, Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two],
      Real.arctan_tan (by nlinarith [pi_pos, hθ.1]) (by nlinarith [pi_pos, h1])]
    field_simp [pi_ne_zero]
  have hbot := hval ▸ ((Real.continuous_arctan.tendsto _).comp (((Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atBot pi_pos)).sub_const _).div_const _)).const_mul π⁻¹
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_stripPoisson₀_primitive hsin.ne')
    (integrable_stripPoisson₀ θ) hbot htop]; ring

/-- For `0 ≤ θ < 1`, the right strip Poisson kernel has total integral `θ` on `ℝ`. -/
theorem integral_stripPoisson₁ {θ : ℝ} (hθ : θ ∈ Ico 0 1) : ∫ t, stripPoisson₁ θ t = θ := by
  rw [stripPoisson₁_eq_stripPoisson₀_one_sub,
    integral_stripPoisson₀ ⟨sub_pos.2 hθ.2, sub_le_self 1 hθ.1⟩, sub_sub_cancel]

/-! ### Holomorphic strip kernel and Poisson approximation -/

section StripKernel

/-- The holomorphic right-boundary strip kernel `I / (1 + exp (I π ζ))`, whose real part on
`0 < re ζ < 1` is `stripPoisson₁ ζ.re ζ.im` (`TauCeti.re_holoPoisson₁`). -/
def holoPoisson₁ (ζ : ℂ) : ℂ := I / (1 + Complex.exp (I * π * ζ))

/-- The holomorphic left-boundary strip kernel `holoPoisson₁ (1 - ζ)`, whose real part on
`0 < re ζ < 1` is `stripPoisson₀ ζ.re ζ.im` (`TauCeti.re_holoPoisson₀`). -/
def holoPoisson₀ (ζ : ℂ) : ℂ := holoPoisson₁ (1 - ζ)

/-- Defining formula for the holomorphic right-boundary strip kernel `holoPoisson₁`. -/
theorem holoPoisson₁_def (ζ : ℂ) : holoPoisson₁ ζ = I / (1 + Complex.exp (I * π * ζ)) := (rfl)

/-- Reflection formula relating `holoPoisson₀` to `holoPoisson₁`. -/
theorem holoPoisson₀_def (ζ : ℂ) : holoPoisson₀ ζ = holoPoisson₁ (1 - ζ) := (rfl)

/-- The real part of `holoPoisson₁ ζ` is `stripPoisson₁ ζ.re ζ.im`. -/
@[simp] theorem re_holoPoisson₁ (ζ : ℂ) : (holoPoisson₁ ζ).re = stripPoisson₁ ζ.re ζ.im := by
  rw [holoPoisson₁, Complex.div_re, Complex.normSq_one_add_exp_eq_two_mul_cosh_add_cos,
    Complex.add_im, Complex.exp_im, stripPoisson₁_def]
  simp only [I_re, zero_mul, zero_div, I_im, one_mul, zero_add, one_im, ofReal_im, mul_im,
    ofReal_re, mul_re, sub_self, zero_sub, Real.cosh_neg]
  field_simp [(Real.exp_pos (-(π * ζ.im))).ne']

/-- The real part of `holoPoisson₀ ζ` is `stripPoisson₀ ζ.re ζ.im`. -/
@[simp] theorem re_holoPoisson₀ (ζ : ℂ) : (holoPoisson₀ ζ).re = stripPoisson₀ ζ.re ζ.im := by
  rw [holoPoisson₀_def, re_holoPoisson₁]; simp [stripPoisson₁_one_sub]

/-- On the open unit vertical strip `0 < re ζ < 1`, `1 + exp (I * π * ζ)` is nonzero. -/
theorem one_add_exp_I_pi_mul_ne_zero {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    1 + Complex.exp (I * π * ζ) ≠ 0 := by
  have hsin : 0 < Real.sin (π * ζ.re) := sin_pi_mul_pos_of_pos_of_lt_one hζ.1 hζ.2
  refine normSq_pos.1 ?_
  rw [Complex.normSq_one_add_exp, show (I * (π : ℂ) * ζ).im = π * ζ.re by simp]; positivity

/-- Complex derivative of `holoPoisson₁` away from the zeros of `1 + exp (I * π * ζ)`. -/
theorem hasDerivAt_holoPoisson₁ {ζ : ℂ} (hζ : 1 + Complex.exp (I * π * ζ) ≠ 0) : HasDerivAt
    holoPoisson₁ (π * Complex.exp (I * π * ζ) / (1 + Complex.exp (I * π * ζ)) ^ 2) ζ := by
  have h1 : HasDerivAt (fun w : ℂ => 1 + Complex.exp (I * π * w))
      (Complex.exp (I * π * ζ) * (I * π)) ζ := by
    simpa using (((hasDerivAt_id ζ).const_mul (I * π)).cexp).const_add 1
  refine ((hasDerivAt_const ζ I).div h1 hζ).congr_deriv ?_
  rw [zero_mul, zero_sub, show -(I * (Complex.exp (I * π * ζ) * (I * π))) =
    -(I * I) * π * Complex.exp (I * π * ζ) by ring, I_mul_I]; ring

/-- Complex derivative of `holoPoisson₀` away from the zeros of `1 + exp (I * π * (1 - ζ))`. -/
theorem hasDerivAt_holoPoisson₀ {ζ : ℂ} (hζ : 1 + Complex.exp (I * π * (1 - ζ)) ≠ 0) :
    HasDerivAt holoPoisson₀
      (-(π * Complex.exp (I * π * (1 - ζ)) / (1 + Complex.exp (I * π * (1 - ζ))) ^ 2)) ζ :=
  ((hasDerivAt_holoPoisson₁ hζ).comp ζ ((hasDerivAt_id ζ).const_sub 1)).congr_deriv (by simp)

/-- The right-boundary holomorphic strip kernel `holoPoisson₁` is complex-differentiable on the
open vertical strip `0 < re ζ < 1`. -/
theorem differentiableOn_holoPoisson₁ : DifferentiableOn ℂ holoPoisson₁ (verticalStrip 0 1) :=
  fun _ hζ => (hasDerivAt_holoPoisson₁
    (one_add_exp_I_pi_mul_ne_zero hζ)).differentiableAt.differentiableWithinAt

/-- The left-boundary holomorphic strip kernel `holoPoisson₀` is complex-differentiable on the
open vertical strip `0 < re ζ < 1`. -/
theorem differentiableOn_holoPoisson₀ : DifferentiableOn ℂ holoPoisson₀ (verticalStrip 0 1) :=
  (funext holoPoisson₀_def).symm ▸ differentiableOn_holoPoisson₁.comp
    ((differentiable_const (1 : ℂ)).sub differentiable_id).differentiableOn
    fun _ hζ => one_sub_mem_verticalStrip_iff.2 hζ

/-- Uniform bound on `‖deriv holoPoisson₁ ζ‖` across any substrip `0 < re ζ ≤ b` (`b < 1`). -/
theorem norm_deriv_holoPoisson₁_le {b : ℝ} (hb : b < 1) {ζ : ℂ} (hζ : ζ.re ∈ Ioc 0 b) :
    ‖deriv holoPoisson₁ ζ‖ ≤ π / (2 * (1 + Real.cos (π * b))) := by
  rw [(hasDerivAt_holoPoisson₁ (one_add_exp_I_pi_mul_ne_zero ⟨hζ.1, hζ.2.trans_lt hb⟩)).deriv]
  have hcosb : 0 < 1 + Real.cos (π * b) := by
    linarith [neg_abs_le (Real.cos (π * b)), abs_cos_lt_one_of_sin_ne_zero
      (sin_pi_mul_pos_of_pos_of_lt_one (hζ.1.trans_le hζ.2) hb).ne']
  have hcos : Real.cos (π * b) ≤ Real.cos (π * ζ.re) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg pi_pos.le hζ.1.le)
      (mul_le_of_le_one_right pi_pos.le hb.le) (mul_le_mul_of_nonneg_left hζ.2 pi_pos.le)
  have hden : 2 * Real.exp (-(π * ζ.im)) * (1 + Real.cos (π * b)) ≤
      ‖1 + Complex.exp (I * π * ζ)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_one_add_exp_eq_two_mul_cosh_add_cos]
    simp only [mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self, zero_add,
      zero_sub, mul_im, one_mul, Real.cosh_neg]
    nlinarith [Real.one_le_cosh (π * ζ.im), Real.exp_pos (-(π * ζ.im))]
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg pi_pos.le, norm_pow,
    Complex.norm_exp, show (I * π * ζ).re = -(π * ζ.im) by simp [mul_re]]
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans_eq
    (by field_simp [(Real.exp_pos (-(π * ζ.im))).ne'])

/-- Uniform bound on `‖deriv holoPoisson₀ ζ‖` across any substrip `a ≤ re ζ < 1` (`0 < a`). -/
theorem norm_deriv_holoPoisson₀_le {a : ℝ} (ha : 0 < a) {ζ : ℂ} (hζ : ζ.re ∈ Ico a 1) :
    ‖deriv holoPoisson₀ ζ‖ ≤ π / (2 * (1 - Real.cos (π * a))) := by
  have h1ζ : 1 - ζ ∈ verticalStrip 0 1 := one_sub_mem_verticalStrip_iff.2 ⟨ha.trans_le hζ.1, hζ.2⟩
  rw [(hasDerivAt_holoPoisson₀ (one_add_exp_I_pi_mul_ne_zero h1ζ)).deriv, norm_neg,
    ← (hasDerivAt_holoPoisson₁ (one_add_exp_I_pi_mul_ne_zero h1ζ)).deriv]
  refine (norm_deriv_holoPoisson₁_le (sub_lt_self 1 ha)
    ⟨by rw [Complex.sub_re, Complex.one_re]; linarith [hζ.2],
      by rw [Complex.sub_re, Complex.one_re]; linarith [hζ.1]⟩).trans_eq ?_
  rw [show π * (1 - a) = π - π * a by ring, Real.cos_pi_sub]; ring

/-- For an integrable function `u : ℝ → ℂ` and `ζ` in the open unit strip,
`s ↦ u s * holoPoisson₁ (ζ - s * I)` is integrable on `ℝ`. -/
theorem integrable_mul_holoPoisson₁ {u : ℝ → ℂ} (hu : Integrable u) {ζ : ℂ}
    (hζ : ζ ∈ verticalStrip 0 1) : Integrable (fun s : ℝ => u s * holoPoisson₁ (ζ - s * I)) := by
  have hsin := sin_pi_mul_pos_of_pos_of_lt_one hζ.1 hζ.2
  have hcont : Continuous fun s : ℝ => holoPoisson₁ (ζ - s * I) :=
    Continuous.div continuous_const (by fun_prop) fun _ =>
      one_add_exp_I_pi_mul_ne_zero ⟨by simpa using hζ.1, by simpa using hζ.2⟩
  refine (hu.norm.const_mul (Real.sin (π * ζ.re))⁻¹).mono'
    (hu.aestronglyMeasurable.mul hcont.aestronglyMeasurable) (ae_of_all _ fun s => ?_)
  have hden : Real.sin (π * ζ.re) ≤ ‖1 + Complex.exp (I * π * (ζ - s * I))‖ := by
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_one_add_exp]
    simpa [mul_im] using sq_nonneg (Real.exp (I * π * (ζ - s * I)).re +
      Real.cos (π * (ζ - s * I).re))
  rw [norm_mul, holoPoisson₁_def, norm_div, Complex.norm_I, mul_comm]
  exact mul_le_mul_of_nonneg_right ((one_div_le_one_div_of_le hsin hden).trans_eq (one_div _))
    (norm_nonneg _)

private theorem holoPoisson₀_sub_neg_mul_I (ζ : ℂ) (s : ℝ) :
    holoPoisson₀ (ζ - ((-s : ℝ) : ℂ) * I) = holoPoisson₁ ((1 - ζ) - (s : ℂ) * I) := by
  rw [holoPoisson₀_def, show 1 - (ζ - ((-s : ℝ) : ℂ) * I) = (1 - ζ) - (s : ℂ) * I by
    push_cast; ring]

/-- For an integrable function `u : ℝ → ℂ` and `ζ` in the open unit strip,
`s ↦ u s * holoPoisson₀ (ζ - s * I)` is integrable on `ℝ`. -/
theorem integrable_mul_holoPoisson₀ {u : ℝ → ℂ} (hu : Integrable u) {ζ : ℂ}
    (hζ : ζ ∈ verticalStrip 0 1) : Integrable (fun s : ℝ => u s * holoPoisson₀ (ζ - s * I)) := by
  have h := integrable_mul_holoPoisson₁ hu.comp_neg (one_sub_mem_verticalStrip_iff.2 hζ)
  refine ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_emb
    (Homeomorph.neg ℝ).measurableEmbedding).1 (h.congr (ae_of_all _ fun s => ?_))
  dsimp only [Function.comp_apply]; rw [holoPoisson₀_sub_neg_mul_I]

private theorem integral_holoPoisson₀_eq (u : ℝ → ℂ) (ζ : ℂ) :
    ∫ s, u s * holoPoisson₀ (ζ - s * I) = ∫ s, u (-s) * holoPoisson₁ ((1 - ζ) - s * I) := by
  rw [← MeasureTheory.integral_neg_eq_self (fun s : ℝ => u s * holoPoisson₀ (ζ - s * I))]
  exact integral_congr_ae (ae_of_all _ fun s => by dsimp only; rw [holoPoisson₀_sub_neg_mul_I])

/-- Convolving an integrable function `u : ℝ → ℂ` with `holoPoisson₁` produces a holomorphic
function on the open vertical strip `0 < re ζ < 1`. -/
theorem differentiableOn_integral_holoPoisson₁ {u : ℝ → ℂ} (hu : Integrable u) : DifferentiableOn ℂ
    (fun ζ => ∫ s, u s * holoPoisson₁ (ζ - s * I)) (verticalStrip 0 1) := by
  intro ζ₀ hζ₀
  let r := min (ζ₀.re / 2) ((1 - ζ₀.re) / 2); let a := ζ₀.re - r; let b := ζ₀.re + r
  have hr : 0 < r := lt_min (half_pos hζ₀.1) (half_pos (sub_pos.2 hζ₀.2))
  have ha : 0 < a := by grind
  have hb : b < 1 := by grind
  have hmem {ζ : ℂ} (hζ : ζ ∈ ball ζ₀ r) (s : ℝ) : (ζ - s * I).re ∈ Icc a b := by
    have hre : |ζ.re - ζ₀.re| < r := (abs_re_le_norm (ζ - ζ₀)).trans_lt (mem_ball_iff_norm.1 hζ)
    simp only [sub_re, mul_I_re, ofReal_im, neg_zero, sub_zero, mem_Icc, a, b]; grind [abs_lt]
  have hws {ζ : ℂ} (hζ : ζ ∈ ball ζ₀ r) (s : ℝ) : ζ - s * I ∈ verticalStrip 0 1 :=
    ⟨ha.trans_le (hmem hζ s).1, (hmem hζ s).2.trans_lt hb⟩
  let C := π / (2 * (1 + Real.cos (π * b)))
  have hderiv_cont : Continuous fun s : ℝ => deriv holoPoisson₁ (ζ₀ - s * I) :=
    (Continuous.div (by fun_prop) (by fun_prop) fun s => pow_ne_zero 2
      (one_add_exp_I_pi_mul_ne_zero (hws (mem_ball_self hr) s))).congr fun s =>
      ((hasDerivAt_holoPoisson₁ (one_add_exp_I_pi_mul_ne_zero
        (hws (mem_ball_self hr) s))).deriv).symm
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := ball ζ₀ r)
    (F' := fun ζ (s : ℝ) => u s * deriv holoPoisson₁ (ζ - s * I)) (bound := fun s => |C| * ‖u s‖)
    (ball_mem_nhds ζ₀ hr) ?_ (integrable_mul_holoPoisson₁ hu hζ₀)
    (hu.aestronglyMeasurable.mul hderiv_cont.aestronglyMeasurable) ?_ (hu.norm.const_mul |C|) ?_
    ).2.differentiableAt.differentiableWithinAt
  · filter_upwards [ball_mem_nhds ζ₀ hr] with ζ hζ
    exact hu.aestronglyMeasurable.mul (Continuous.div continuous_const (by fun_prop) fun s =>
      one_add_exp_I_pi_mul_ne_zero (hws hζ s)).aestronglyMeasurable
  · exact ae_of_all _ fun s ζ hζ => by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right ((norm_deriv_holoPoisson₁_le hb
        ⟨ha.trans_le (hmem hζ s).1, (hmem hζ s).2⟩).trans (le_abs_self C)) (norm_nonneg _)
  · exact ae_of_all _ fun s ζ hζ =>
      have hd := hasDerivAt_holoPoisson₁ (one_add_exp_I_pi_mul_ne_zero (hws hζ s))
      by simpa using ((hd.comp ζ ((hasDerivAt_id ζ).sub_const ((s : ℂ) * I))).const_mul
        (u s)).congr_deriv (by rw [mul_one, ← hd.deriv])

/-- Convolving an integrable function `u : ℝ → ℂ` with `holoPoisson₀` produces a holomorphic
function on the open vertical strip `0 < re ζ < 1`. -/
theorem differentiableOn_integral_holoPoisson₀ {u : ℝ → ℂ} (hu : Integrable u) : DifferentiableOn ℂ
    (fun ζ => ∫ s, u s * holoPoisson₀ (ζ - s * I)) (verticalStrip 0 1) := by
  simp_rw [integral_holoPoisson₀_eq]
  exact (differentiableOn_integral_holoPoisson₁ hu.comp_neg).comp
    (by fun_prop : Differentiable ℂ fun ζ : ℂ => 1 - ζ).differentiableOn fun _ hζ =>
      one_sub_mem_verticalStrip_iff.2 hζ

/-- The real part of the `holoPoisson₁` convolution of an integrable function `u` at
`ζ ∈ verticalStrip 0 1` is the `stripPoisson₁` integral of `u`. -/
theorem re_integral_holoPoisson₁ {u : ℝ → ℝ} (hu : Integrable u) {ζ : ℂ}
    (hζ : ζ ∈ verticalStrip 0 1) : (∫ s, (u s : ℂ) * holoPoisson₁ (ζ - s * I)).re =
      ∫ s, u s * stripPoisson₁ ζ.re (ζ.im - s) :=
  (Complex.reCLM.integral_comp_comm
    (integrable_mul_holoPoisson₁ (Complex.ofRealCLM.integrable_comp hu) hζ)).symm.trans
    (integral_congr_ae (ae_of_all _ fun s => by simp [re_holoPoisson₁]))

/-- The real part of the `holoPoisson₀` convolution of an integrable function `u` at
`ζ ∈ verticalStrip 0 1` is the `stripPoisson₀` integral of `u`. -/
theorem re_integral_holoPoisson₀ {u : ℝ → ℝ} (hu : Integrable u) {ζ : ℂ}
    (hζ : ζ ∈ verticalStrip 0 1) : (∫ s, (u s : ℂ) * holoPoisson₀ (ζ - s * I)).re =
      ∫ s, u s * stripPoisson₀ ζ.re (ζ.im - s) := by
  have hre : (∫ s, (u (-s) : ℂ) * holoPoisson₁ ((1 - ζ) - s * I)).re =
      ∫ s, u (-s) * stripPoisson₁ (1 - ζ).re ((1 - ζ).im - s) := by
    simpa only [Function.comp_apply] using
      re_integral_holoPoisson₁ hu.comp_neg (one_sub_mem_verticalStrip_iff.2 hζ)
  rw [integral_holoPoisson₀_eq (fun s => (u s : ℂ)), hre,
    ← MeasureTheory.integral_neg_eq_self (fun s : ℝ => u s * stripPoisson₀ ζ.re (ζ.im - s))]
  exact integral_congr_ae (ae_of_all _ fun s => by
    have him : -ζ.im - s = -(ζ.im - -s) := by ring
    dsimp only; rw [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub,
      stripPoisson₁_one_sub, him, stripPoisson₀_neg])

/-- For fixed `r > 0`, the mass `∫ y in (-r)..r, stripPoisson₀ ε y` converges to `1` as `ε → 0⁺`. -/
theorem tendsto_intervalIntegral_stripPoisson₀_nhdsGT {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε => ∫ y in (-r)..r, stripPoisson₀ ε y) (𝓝[>] 0) (𝓝 1) := by
  have hsin_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < Real.sin (π * ε) := Filter.mem_of_superset
    (Ioo_mem_nhdsGT zero_lt_one) fun _ hε => sin_pi_mul_pos_of_pos_of_lt_one hε.1 hε.2
  have hinv : Tendsto (fun ε : ℝ => (Real.sin (π * ε))⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨((Real.continuous_sin.comp
      (continuous_const_mul π)).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds, hsin_pos⟩)
  have hcos : Tendsto (fun ε : ℝ => Real.cos (π * ε)) (𝓝[>] 0) (𝓝 1) := by
    simpa using ((by fun_prop : Continuous fun ε : ℝ => Real.cos (π * ε)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hF_top : Tendsto (fun ε => π⁻¹ * Real.arctan ((Real.exp (π * r) - Real.cos (π * ε)) /
      Real.sin (π * ε))) (𝓝[>] 0) (𝓝 (2⁻¹ : ℝ)) := inv_pi_mul_pi_div_two ▸
    ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp (by
      simpa only [div_eq_mul_inv] using (tendsto_const_nhds.sub hcos).pos_mul_atTop
        (sub_pos.2 (Real.one_lt_exp_iff.2 (mul_pos pi_pos hr))) hinv)).const_mul π⁻¹
  have hF_bot : Tendsto (fun ε => π⁻¹ * Real.arctan ((Real.exp (-(π * r)) - Real.cos (π * ε)) /
      Real.sin (π * ε))) (𝓝[>] 0) (𝓝 (-(2⁻¹ : ℝ))) := by
    rw [show -(2⁻¹ : ℝ) = π⁻¹ * -(π / 2) by rw [mul_neg, inv_pi_mul_pi_div_two]]
    refine ((Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (tendsto_neg_atTop_iff.1 ?_)).const_mul π⁻¹
    simpa only [div_eq_mul_inv, ← neg_mul, neg_sub] using
      (hcos.sub tendsto_const_nhds).pos_mul_atTop
        (sub_pos.2 (Real.exp_lt_one_iff.2 (neg_neg_of_pos (mul_pos pi_pos hr)))) hinv
  refine ((by norm_num : (2⁻¹ : ℝ) - -(2⁻¹ : ℝ) = 1) ▸ hF_top.sub hF_bot).congr' ?_
  filter_upwards [hsin_pos] with ε hsin
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ =>
    hasDerivAt_stripPoisson₀_primitive hsin.ne' y)
    (integrable_stripPoisson₀ ε).intervalIntegrable]; simp [mul_neg]

/-- For fixed `r > 0`, the mass `∫ y in (-r)..r, stripPoisson₁ θ y` converges to `1` as `θ → 1⁻`. -/
theorem tendsto_intervalIntegral_stripPoisson₁_nhdsLT {r : ℝ} (hr : 0 < r) :
    Tendsto (fun θ => ∫ y in (-r)..r, stripPoisson₁ θ y) (𝓝[<] 1) (𝓝 1) := by
  simp_rw [← stripPoisson₀_one_sub]
  refine (tendsto_intervalIntegral_stripPoisson₀_nhdsGT hr).comp (tendsto_nhdsWithin_iff.2
    ⟨((continuous_const.sub continuous_id).tendsto' 1 0 (sub_self 1)).mono_left nhdsWithin_le_nhds,
      by filter_upwards [self_mem_nhdsWithin] with _ (h : _ < 1); exact sub_pos.2 h⟩)

private theorem mul_le_integral_mul_stripPoisson₀ {u : ℝ → ℝ} (hu : UniformContinuous u)
    (hbdd : ∃ M, ∀ t, ‖u t‖ ≤ M) (hunonneg : ∀ s, 0 ≤ u s) {ε c r a b : ℝ} (hε : ε ∈ Ioo 0 1)
    (ha : 0 ≤ a) (hb : b ≤ ∫ s in Icc (c - r) (c + r), stripPoisson₀ ε (c - s))
    (hpt : ∀ s ∈ Icc (c - r) (c + r), a ≤ u s) : a * b ≤ ∫ s, u s * stripPoisson₀ ε (c - s) := by
  obtain ⟨M, hM⟩ := hbdd
  have hint : Integrable (fun s => u s * stripPoisson₀ ε (c - s)) :=
    ((integrable_stripPoisson₀ ε).comp_sub_left c).bdd_mul hu.continuous.aestronglyMeasurable
      (ae_of_all _ hM)
  calc a * b ≤ ∫ s in Icc (c - r) (c + r), a * stripPoisson₀ ε (c - s) :=
        integral_const_mul a _ ▸ mul_le_mul_of_nonneg_left hb ha
    _ ≤ ∫ s in Icc (c - r) (c + r), u s * stripPoisson₀ ε (c - s) := setIntegral_mono_on
        (((integrable_stripPoisson₀ ε).comp_sub_left c).const_mul a).integrableOn hint.integrableOn
        measurableSet_Icc fun _ hs =>
          mul_le_mul_of_nonneg_right (hpt _ hs) (stripPoisson₀_pos hε _).le
    _ ≤ ∫ s, u s * stripPoisson₀ ε (c - s) := setIntegral_le_integral hint
        (ae_of_all _ fun s => mul_nonneg (hunonneg s) (stripPoisson₀_pos hε _).le)

/-- Uniform one-sided approximate-identity lower bound of `stripPoisson₀ ε` as `ε → 0⁺`, for a
nonnegative bounded uniformly continuous function. -/
theorem exists_forall_sub_le_integral_mul_stripPoisson₀ {u : ℝ → ℝ} (hu : UniformContinuous u)
    (hbdd : ∃ M, ∀ t, ‖u t‖ ≤ M) (hunonneg : ∀ s, 0 ≤ u s) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ t : ℝ, u t - κ ≤ ∫ s, u s * stripPoisson₀ ε (t - s) := by
  obtain ⟨M, hM⟩ := hbdd; let U := max M 1
  have hUpos : 0 < U := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨η, hηpos, hη⟩ := Metric.uniformContinuous_iff.1 hu (κ / 3) (by positivity)
  have hκU : 0 < κ / (3 * U) := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁_mem⟩ := Metric.mem_nhdsWithin_iff.1
    ((tendsto_intervalIntegral_stripPoisson₀_nhdsGT (half_pos hηpos)).eventually
      (Ioo_mem_nhds (sub_lt_self 1 hκU) (by norm_num : (1 : ℝ) < 2)))
  refine ⟨min δ₁ (2⁻¹ : ℝ), lt_min hδ₁ (by norm_num), fun ε hε t => ?_⟩
  have hεI : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε.1, (hε.2.trans_le (min_le_right _ _)).trans (by norm_num)⟩
  by_cases hsign : u t - κ / 3 ≤ 0
  · exact (by linarith : u t - κ ≤ 0).trans
      (integral_nonneg fun s => mul_nonneg (hunonneg s) (stripPoisson₀_pos hεI _).le)
  have hstep1 : u t - κ ≤ (u t - κ / 3) * (1 - κ / (3 * U)) := by
    have h1 := mul_le_mul_of_nonneg_right (by
      linarith [(le_abs_self (u t)).trans ((hM t).trans (le_max_left M 1))] : u t - κ / 3 ≤ U)
      hκU.le
    have h2 : U * (κ / (3 * U)) = κ / 3 := by field_simp [hUpos.ne']
    linarith
  refine hstep1.trans (mul_le_integral_mul_stripPoisson₀ (r := η / 2) hu ⟨M, hM⟩ hunonneg hεI
    (not_le.1 hsign).le ?_ fun s hs => ?_)
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_sub_left (fun y => stripPoisson₀ ε y), sub_add_cancel_left,
      sub_sub_cancel]
    exact (hδ₁_mem ⟨by simp [abs_of_pos hε.1, hε.2.trans_le (min_le_left _ _)], hε.1⟩).1.le
  · have hd := hη (a := s) (b := t) (by rw [Real.dist_eq]; exact
      (abs_sub_le_iff.2 ⟨by linarith [hs.2], by linarith [hs.1]⟩).trans_lt (half_lt_self hηpos))
    rw [Real.dist_eq] at hd; linarith [(abs_sub_le_iff.1 hd.le).2]

/-- Uniform one-sided approximate-identity lower bound of `stripPoisson₁ θ` as `θ → 1⁻`, for a
nonnegative bounded uniformly continuous function. -/
theorem exists_forall_sub_le_integral_mul_stripPoisson₁ {u : ℝ → ℝ} (hu : UniformContinuous u)
    (hbdd : ∃ M, ∀ t, ‖u t‖ ≤ M) (hunonneg : ∀ s, 0 ≤ u s) {κ : ℝ} (hκ : 0 < κ) :
    ∃ θ₀ < 1, ∀ θ ∈ Ioo θ₀ 1, ∀ t : ℝ, u t - κ ≤ ∫ s, u s * stripPoisson₁ θ (t - s) := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_forall_sub_le_integral_mul_stripPoisson₀ hu hbdd hunonneg hκ
  exact ⟨1 - ε₀, sub_lt_self 1 hε₀, fun θ hθ t => by
    simpa only [stripPoisson₀_one_sub] using h (1 - θ) ⟨sub_pos.2 hθ.2, sub_lt_comm.1 hθ.1⟩ t⟩

/-- Uniform one-sided approximate-identity lower bound of `stripPoisson₀ ε` along contracted
centers `(1 - 2 * ε) * t` on `[-T, T]` as `ε → 0⁺`. -/
theorem exists_forall_sub_le_integral_mul_contracted_stripPoisson₀ {u : ℝ → ℝ}
    (hu : UniformContinuous u) (hbdd : ∃ M, ∀ t, ‖u t‖ ≤ M) (hunonneg : ∀ s, 0 ≤ u s) (T : ℝ)
    {κ : ℝ} (hκ : 0 < κ) : ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ t ∈ Icc (-T) T,
      u t - κ ≤ ∫ s, u s * stripPoisson₀ ε ((1 - 2 * ε) * t - s) := by
  obtain ⟨ε₀, hε₀, happrox⟩ :=
    exists_forall_sub_le_integral_mul_stripPoisson₀ hu hbdd hunonneg (half_pos hκ)
  obtain ⟨η, hη, huc⟩ := Metric.uniformContinuous_iff.1 hu (κ / 2) (half_pos hκ)
  refine ⟨min ε₀ (η / (2 * (|T| + 1))), lt_min hε₀ (by positivity), fun ε hε t ht => ?_⟩
  have hdt : dist ((1 - 2 * ε) * t) t < η := by
    rw [Real.dist_eq, show (1 - 2 * ε) * t - t = -(2 * ε * t) by ring, abs_neg, abs_mul,
      abs_of_pos (mul_pos two_pos hε.1)]
    have htabs : |t| ≤ |T| + 1 := (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans
      ((le_abs_self T).trans (by linarith))
    nlinarith [(lt_div_iff₀ (by positivity)).1 (hε.2.trans_le (min_le_right _ _)),
      mul_pos two_pos hε.1]
  have hdu := huc hdt; rw [Real.dist_eq] at hdu
  linarith [(abs_sub_le_iff.1 hdu.le).2,
    happrox ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩ ((1 - 2 * ε) * t)]

/-- Uniform one-sided approximate-identity lower bound of `stripPoisson₁ (1 - ε)` along contracted
centers `(1 - 2 * ε) * t` on `[-T, T]` as `ε → 0⁺`. -/
theorem exists_forall_sub_le_integral_mul_contracted_stripPoisson₁ {u : ℝ → ℝ}
    (hu : UniformContinuous u) (hbdd : ∃ M, ∀ t, ‖u t‖ ≤ M) (hunonneg : ∀ s, 0 ≤ u s) (T : ℝ)
    {κ : ℝ} (hκ : 0 < κ) : ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ t ∈ Icc (-T) T,
      u t - κ ≤ ∫ s, u s * stripPoisson₁ (1 - ε) ((1 - 2 * ε) * t - s) := by
  simpa only [stripPoisson₁_one_sub] using
    exists_forall_sub_le_integral_mul_contracted_stripPoisson₀ hu hbdd hunonneg T hκ

end StripKernel

end TauCeti
