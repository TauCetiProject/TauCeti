/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Complex.VerticalStrip.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Poisson kernels of the unit vertical strip

On the open vertical strip `0 < re ζ < 1`, bounded harmonic functions are represented from their
boundary values on `re ζ = 0` and `re ζ = 1` by the two strip Poisson kernels

* `TauCeti.stripPoisson₀ θ t = sin (π θ) / (2 (cosh (π t) - cos (π θ)))`, strictly positive for
  `0 < θ < 1` with integral `1 - θ` for `0 < θ ≤ 1` (`TauCeti.integral_stripPoisson₀`);
* `TauCeti.stripPoisson₁ θ t = sin (π θ) / (2 (cosh (π t) + cos (π θ)))`, strictly positive for
  `0 < θ < 1` with integral `θ` for `0 ≤ θ < 1` (`TauCeti.integral_stripPoisson₁`).

Evaluating the kernel formulas directly at the boundary points `θ = 0` or `θ = 1` yields zero
(`TauCeti.stripPoisson₀_zero`, `TauCeti.stripPoisson₀_one`, `TauCeti.stripPoisson₁_zero`,
`TauCeti.stripPoisson₁_one`). Boundary values are instead recovered as limits `θ → 0⁺` or `θ → 1⁻`,
through the approximate-identity mass concentration
(`TauCeti.tendsto_intervalIntegral_stripPoisson₀_nhdsGT`,
`TauCeti.exists_eps_integral_stripPoisson₀_ge`).

The holomorphic strip kernels `TauCeti.holoPoisson₀` and `TauCeti.holoPoisson₁` realize
`stripPoisson₀` and `stripPoisson₁` as real parts on the open strip, yielding holomorphic
convolutions on `0 < re ζ < 1` (`TauCeti.differentiableOn_integral_holoPoisson₀`,
`TauCeti.differentiableOn_integral_holoPoisson₁`).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Metric Real Set Topology

namespace TauCeti

/-! ### The Poisson kernels of the unit vertical strip -/

/-- The left boundary Poisson kernel `P₀(θ, t) = sin (π θ) / (2 (cosh (π t) - cos (π θ)))` of the
vertical strip `0 ≤ re z ≤ 1`. For `0 < θ < 1` it is strictly positive and represents interior
harmonic values from boundary data on `re z = 0`, with integral `1 - θ` over `ℝ`. -/
def stripPoisson₀ (θ t : ℝ) : ℝ :=
  Real.sin (π * θ) / (2 * (Real.cosh (π * t) - Real.cos (π * θ)))

/-- The right boundary Poisson kernel `P₁(θ, t) = sin (π θ) / (2 (cosh (π t) + cos (π θ)))` of the
vertical strip `0 ≤ re z ≤ 1`. For `0 < θ < 1` it is strictly positive and represents interior
harmonic values from boundary data on `re z = 1`, with integral `θ` over `ℝ`. -/
def stripPoisson₁ (θ t : ℝ) : ℝ :=
  Real.sin (π * θ) / (2 * (Real.cosh (π * t) + Real.cos (π * θ)))

/-- Defining formula for the left strip Poisson kernel `stripPoisson₀`. -/
theorem stripPoisson₀_def (θ t : ℝ) :
    stripPoisson₀ θ t = Real.sin (π * θ) / (2 * (Real.cosh (π * t) - Real.cos (π * θ))) := by
  rw [stripPoisson₀]

/-- Defining formula for the right strip Poisson kernel `stripPoisson₁`. -/
theorem stripPoisson₁_def (θ t : ℝ) :
    stripPoisson₁ θ t = Real.sin (π * θ) / (2 * (Real.cosh (π * t) + Real.cos (π * θ))) := by
  rw [stripPoisson₁]

@[simp]
theorem stripPoisson₀_neg (θ t : ℝ) : stripPoisson₀ θ (-t) = stripPoisson₀ θ t := by
  simp [stripPoisson₀_def, mul_neg, Real.cosh_neg]

@[simp]
theorem stripPoisson₁_neg (θ t : ℝ) : stripPoisson₁ θ (-t) = stripPoisson₁ θ t := by
  simp [stripPoisson₁_def, mul_neg, Real.cosh_neg]

/-- Reflecting `θ ↦ 1 - θ` exchanges the two strip Poisson kernels. -/
theorem stripPoisson₀_one_sub (θ t : ℝ) : stripPoisson₀ (1 - θ) t = stripPoisson₁ θ t := by
  have hpi : π * (1 - θ) = π - π * θ := by ring
  rw [stripPoisson₀_def, stripPoisson₁_def, hpi, Real.sin_pi_sub, Real.cos_pi_sub, sub_neg_eq_add]

/-- Reflecting `θ ↦ 1 - θ` exchanges the two strip Poisson kernels. -/
theorem stripPoisson₁_one_sub (θ t : ℝ) : stripPoisson₁ (1 - θ) t = stripPoisson₀ θ t := by
  simpa using (stripPoisson₀_one_sub (1 - θ) t).symm

private theorem stripPoisson₁_eq_stripPoisson₀_one_sub (θ : ℝ) :
    stripPoisson₁ θ = stripPoisson₀ (1 - θ) :=
  funext fun t => (stripPoisson₀_one_sub θ t).symm

private theorem stripPoisson₀_eq_zero_of_sin_eq_zero {θ : ℝ} (h : Real.sin (π * θ) = 0) :
    stripPoisson₀ θ = 0 := by
  ext t
  simp [stripPoisson₀_def, h]

@[simp]
theorem stripPoisson₀_zero (t : ℝ) : stripPoisson₀ 0 t = 0 := by simp [stripPoisson₀_def]

@[simp]
theorem stripPoisson₀_one (t : ℝ) : stripPoisson₀ 1 t = 0 := by simp [stripPoisson₀_def]

@[simp]
theorem stripPoisson₁_zero (t : ℝ) : stripPoisson₁ 0 t = 0 := by simp [stripPoisson₁_def]

@[simp]
theorem stripPoisson₁_one (t : ℝ) : stripPoisson₁ 1 t = 0 := by simp [stripPoisson₁_def]

private theorem abs_cos_lt_one_of_sin_ne_zero {x : ℝ} (h : Real.sin x ≠ 0) : |Real.cos x| < 1 :=
  (sq_lt_one_iff_abs_lt_one _).1 (by nlinarith [Real.sin_sq_add_cos_sq x, sq_pos_of_ne_zero h])

private theorem one_sub_abs_cos_mul_cosh_le {θ : ℝ} (t : ℝ) :
    (1 - |Real.cos (π * θ)|) * Real.cosh (π * t) ≤ Real.cosh (π * t) - Real.cos (π * θ) := by
  have h := mul_nonneg (abs_nonneg (Real.cos (π * θ))) (sub_nonneg.2 (Real.one_le_cosh (π * t)))
  linarith [le_abs_self (Real.cos (π * θ))]

private theorem cosh_sub_cos_pos_of_sin_ne_zero {θ : ℝ} (h : Real.sin (π * θ) ≠ 0) (t : ℝ) :
    0 < Real.cosh (π * t) - Real.cos (π * θ) :=
  (mul_pos (sub_pos.2 (abs_cos_lt_one_of_sin_ne_zero h)) (Real.cosh_pos _)).trans_le
    (one_sub_abs_cos_mul_cosh_le t)

/-- On the open interval `0 < θ < 1`, the left strip Poisson kernel is strictly positive. -/
theorem stripPoisson₀_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) : 0 < stripPoisson₀ θ t := by
  have hsin : 0 < Real.sin (π * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (mul_lt_of_lt_one_right pi_pos hθ.2)
  exact div_pos hsin (mul_pos zero_lt_two (cosh_sub_cos_pos_of_sin_ne_zero hsin.ne' t))

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
@[fun_prop]
theorem continuous_stripPoisson₀ (θ : ℝ) : Continuous (stripPoisson₀ θ) := by
  by_cases h : Real.sin (π * θ) = 0
  · rw [stripPoisson₀_eq_zero_of_sin_eq_zero h]
    exact continuous_const
  exact Continuous.div continuous_const (by fun_prop) fun t =>
    (mul_pos zero_lt_two (cosh_sub_cos_pos_of_sin_ne_zero h t)).ne'

/-- For every real `θ`, `t ↦ stripPoisson₁ θ t` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_stripPoisson₁ (θ : ℝ) : Continuous (stripPoisson₁ θ) := by
  rw [stripPoisson₁_eq_stripPoisson₀_one_sub]
  exact continuous_stripPoisson₀ (1 - θ)

private theorem hasDerivAt_stripPoisson₀_primitive {θ : ℝ} (hsin : Real.sin (π * θ) ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun s => π⁻¹ * Real.arctan ((Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ)))
      (stripPoisson₀ θ t) t := by
  have hlin : HasDerivAt (fun s => (Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ))
      (π * Real.exp (π * t) / Real.sin (π * θ)) t := by
    have h1 := ((hasDerivAt_id t).const_mul π).exp.sub_const (Real.cos (π * θ))
    simpa [mul_comm] using h1.div_const (Real.sin (π * θ))
  refine (((Real.hasDerivAt_arctan _).comp t hlin).const_mul π⁻¹).congr_deriv ?_
  have hden : 2 * (Real.cosh (π * t) - Real.cos (π * θ)) = Real.exp (-(π * t)) *
      ((Real.exp (π * t) - Real.cos (π * θ)) ^ 2 + Real.sin (π * θ) ^ 2) := by
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp [(Real.exp_pos (π * t)).ne']
    linear_combination -(Real.cos_sq_add_sin_sq (π * θ))
  rw [stripPoisson₀_def, hden, Real.exp_neg]
  have hsq : (Real.exp (π * t) - Real.cos (π * θ)) ^ 2 + Real.sin (π * θ) ^ 2 ≠ 0 := by positivity
  field_simp [pi_ne_zero, (Real.exp_pos (π * t)).ne', hsin, hsq]
  ring

/-- For every real `θ`, the left strip Poisson kernel is integrable on `ℝ`. -/
theorem integrable_stripPoisson₀ (θ : ℝ) : Integrable (stripPoisson₀ θ) := by
  by_cases hsin : Real.sin (π * θ) = 0
  · simp [stripPoisson₀_eq_zero_of_sin_eq_zero hsin]
  have hc : 0 < 1 - |Real.cos (π * θ)| := sub_pos.2 (abs_cos_lt_one_of_sin_ne_zero hsin)
  have hIoi : IntegrableOn (stripPoisson₀ θ) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 pi_pos).const_mul
      (|Real.sin (π * θ)| / (1 - |Real.cos (π * θ)|))).mono'
      (continuous_stripPoisson₀ θ).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    have hcosh : Real.exp (π * t) / 2 ≤ Real.cosh (π * t) := by
      rw [Real.cosh_eq]
      linarith [Real.exp_pos (-(π * t))]
    have hden : (1 - |Real.cos (π * θ)|) * Real.exp (π * t) ≤
        2 * (Real.cosh (π * t) - Real.cos (π * θ)) := by
      nlinarith [one_sub_abs_cos_mul_cosh_le (θ := θ) t, hcosh]
    rw [Real.norm_eq_abs, stripPoisson₀_def, abs_div,
      abs_of_pos (mul_pos zero_lt_two (cosh_sub_cos_pos_of_sin_ne_zero hsin t))]
    refine (div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hc (Real.exp_pos _)) hden).trans_eq ?_
    rw [neg_mul, Real.exp_neg]
    field_simp [hc.ne']
  have hIic : IntegrableOn (stripPoisson₀ θ) (Iic 0) := by
    have hpre : (Homeomorph.neg ℝ ⁻¹' Ici (0 : ℝ)) = Iic 0 := by ext t; simp
    have hIci : IntegrableOn (stripPoisson₀ θ) (Ici 0) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).2 hIoi
    simpa [hpre, Function.comp_def, stripPoisson₀_neg] using
      ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding (f := stripPoisson₀ θ) (s := Ici 0)).2 hIci
  exact integrableOn_univ.1 (Iic_union_Ioi (a := (0 : ℝ)) ▸ hIic.union hIoi)

/-- For every real `θ`, the right strip Poisson kernel is integrable on `ℝ`. -/
theorem integrable_stripPoisson₁ (θ : ℝ) : Integrable (stripPoisson₁ θ) := by
  rw [stripPoisson₁_eq_stripPoisson₀_one_sub]
  exact integrable_stripPoisson₀ (1 - θ)

private theorem inv_pi_mul_pi_div_two : π⁻¹ * (π / 2) = (2⁻¹ : ℝ) := by
  field_simp [pi_ne_zero]

/-- For `0 < θ ≤ 1`, the left strip Poisson kernel has total integral `1 - θ` on `ℝ`. -/
theorem integral_stripPoisson₀ {θ : ℝ} (hθ : θ ∈ Ioc 0 1) :
    ∫ t, stripPoisson₀ θ t = 1 - θ := by
  rcases eq_or_lt_of_le hθ.2 with rfl | h1; · simp
  have hsin : 0 < Real.sin (π * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (mul_lt_of_lt_one_right pi_pos h1)
  have htop : Tendsto
      (fun s => π⁻¹ * Real.arctan ((Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ)))
      atTop (𝓝 (2⁻¹ : ℝ)) := by
    have h1' : Tendsto (fun s => (Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ))
        atTop atTop :=
      ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop pi_pos)).atTop_add
        tendsto_const_nhds).atTop_div_const hsin
    rw [← inv_pi_mul_pi_div_two]
    exact ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1').const_mul π⁻¹
  have hbot : Tendsto
      (fun s => π⁻¹ * Real.arctan ((Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ)))
      atBot (𝓝 (θ - 2⁻¹)) := by
    have hexp0 := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot pi_pos)
    have htan : -Real.cos (π * θ) / Real.sin (π * θ) = Real.tan (π * θ - π / 2) := by
      rw [Real.tan_eq_sin_div_cos, Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two]
    have hval : π⁻¹ * Real.arctan ((0 - Real.cos (π * θ)) / Real.sin (π * θ)) = θ - 2⁻¹ := by
      rw [zero_sub, htan, Real.arctan_tan (by nlinarith [pi_pos, hθ.1]) (by nlinarith [pi_pos, h1])]
      field_simp [pi_ne_zero]
    rw [← hval]
    exact ((Real.continuous_arctan.tendsto _).comp ((hexp0.sub_const _).div_const _)).const_mul π⁻¹
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_stripPoisson₀_primitive hsin.ne')
    (integrable_stripPoisson₀ θ) hbot htop]
  ring

/-- For `0 ≤ θ < 1`, the right strip Poisson kernel has total integral `θ` on `ℝ`. -/
theorem integral_stripPoisson₁ {θ : ℝ} (hθ : θ ∈ Ico 0 1) :
    ∫ t, stripPoisson₁ θ t = θ := by
  have hint : ∫ t, stripPoisson₁ θ t = ∫ t, stripPoisson₀ (1 - θ) t := by
    rw [stripPoisson₁_eq_stripPoisson₀_one_sub]
  rw [hint, integral_stripPoisson₀ ⟨sub_pos.2 hθ.2, sub_le_self 1 hθ.1⟩, sub_sub_cancel]

/-- Reflecting the integration variable converts a contracted left-kernel integral of `u ∘ (-·)`
into a right-kernel integral of `u` at `1 - ε`. -/
theorem integral_neg_stripPoisson₀_eq (u : ℝ → ℝ) (ε t : ℝ) :
    ∫ s, (u ∘ Neg.neg) s * stripPoisson₀ ε ((1 - 2 * ε) * (-t) - s) =
      ∫ s, u s * stripPoisson₁ (1 - ε) ((1 - 2 * ε) * t - s) := by
  rw [← MeasureTheory.integral_neg_eq_self
    (fun s : ℝ => u s * stripPoisson₁ (1 - ε) ((1 - 2 * ε) * t - s))]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  have harg : (1 - 2 * ε) * t - -s = -((1 - 2 * ε) * (-t) - s) := by ring
  simp only [Function.comp_apply, stripPoisson₁_one_sub, harg, stripPoisson₀_neg]

/-! ### Holomorphic strip kernel and Poisson approximation -/

section StripKernel

/-- The holomorphic right-boundary strip kernel `I / (1 + exp (I π ζ))`, whose real part on
`0 < re ζ < 1` is `stripPoisson₁ ζ.re ζ.im` (`TauCeti.re_holoPoisson₁`). -/
def holoPoisson₁ (ζ : ℂ) : ℂ :=
  I / (1 + Complex.exp (I * π * ζ))

/-- The holomorphic left-boundary strip kernel `holoPoisson₁ (1 - ζ)`, whose real part on
`0 < re ζ < 1` is `stripPoisson₀ ζ.re ζ.im`. -/
def holoPoisson₀ (ζ : ℂ) : ℂ :=
  holoPoisson₁ (1 - ζ)

private theorem one_add_exp_I_pi_mul_eq (ζ : ℂ) :
    1 + Complex.exp (I * π * ζ) =
      ((1 + Real.exp (-(π * ζ.im)) * Real.cos (π * ζ.re) : ℝ) : ℂ) +
        ((Real.exp (-(π * ζ.im)) * Real.sin (π * ζ.re) : ℝ) : ℂ) * I := by
  have harg : I * π * ζ = ((-(π * ζ.im) : ℝ) : ℂ) + ((π * ζ.re : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [harg, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

private theorem normSq_one_add_exp_I_pi_mul (ζ : ℂ) :
    Complex.normSq (1 + Complex.exp (I * π * ζ)) =
      (Real.exp (-(π * ζ.im)) + Real.cos (π * ζ.re)) ^ 2 + Real.sin (π * ζ.re) ^ 2 := by
  rw [one_add_exp_I_pi_mul_eq, Complex.normSq_add_mul_I]
  linear_combination (Real.exp (-(π * ζ.im)) ^ 2 - 1) * Real.cos_sq_add_sin_sq (π * ζ.re)

private theorem normSq_one_add_exp_eq_two_mul_cosh_add_cos (ζ : ℂ) :
    Complex.normSq (1 + Complex.exp (I * π * ζ)) =
      2 * Real.exp (-(π * ζ.im)) * (Real.cosh (π * ζ.im) + Real.cos (π * ζ.re)) := by
  rw [normSq_one_add_exp_I_pi_mul, Real.cosh_eq]
  have hexp : Real.exp (-(π * ζ.im)) * Real.exp (π * ζ.im) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination Real.cos_sq_add_sin_sq (π * ζ.re) - hexp

private theorem one_add_exp_ne_zero {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    1 + Complex.exp (I * π * ζ) ≠ 0 := by
  have hsin : 0 < Real.sin (π * ζ.re) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hζ.1) (mul_lt_of_lt_one_right pi_pos hζ.2)
  exact Complex.normSq_pos.1 (by rw [normSq_one_add_exp_I_pi_mul]; positivity)

/-- The real part of `holoPoisson₁ ζ` is `stripPoisson₁ ζ.re ζ.im`. -/
theorem re_holoPoisson₁ (ζ : ℂ) :
    (holoPoisson₁ ζ).re = stripPoisson₁ ζ.re ζ.im := by
  rw [holoPoisson₁, Complex.div_re, normSq_one_add_exp_eq_two_mul_cosh_add_cos,
    one_add_exp_I_pi_mul_eq, stripPoisson₁_def]
  simp only [I_re, zero_mul, zero_div, I_im, one_mul, mul_one, zero_add, add_zero, add_im,
    ofReal_im, mul_im, ofReal_re]
  field_simp [(Real.exp_pos (-(π * ζ.im))).ne']

private theorem hasDerivAt_holoPoisson₁ {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    HasDerivAt holoPoisson₁
      (π * Complex.exp (I * π * ζ) / (1 + Complex.exp (I * π * ζ)) ^ 2) ζ := by
  have h1 : HasDerivAt (fun w : ℂ => 1 + Complex.exp (I * π * w))
      (Complex.exp (I * π * ζ) * (I * π)) ζ := by
    simpa using (((hasDerivAt_id ζ).const_mul (I * π)).cexp).const_add 1
  refine ((hasDerivAt_const ζ I).div h1 (one_add_exp_ne_zero hζ)).congr_deriv ?_
  calc (0 * (1 + Complex.exp (I * π * ζ)) - I * (Complex.exp (I * π * ζ) * (I * π))) /
        (1 + Complex.exp (I * π * ζ)) ^ 2
      = (-(I * I) * π * Complex.exp (I * π * ζ)) / (1 + Complex.exp (I * π * ζ)) ^ 2 := by ring
    _ = π * Complex.exp (I * π * ζ) / (1 + Complex.exp (I * π * ζ)) ^ 2 := by rw [I_mul_I]; ring

private theorem norm_deriv_holoPoisson₁_le {a b : ℝ} (ha : 0 < a) (hb : b < 1) {ζ : ℂ}
    (hζ : ζ.re ∈ Icc a b) :
    ‖(π : ℂ) * Complex.exp (I * π * ζ) / (1 + Complex.exp (I * π * ζ)) ^ 2‖ ≤
      π / (2 * (1 + Real.cos (π * b))) := by
  have hcosb : 0 < 1 + Real.cos (π * b) := by
    have hlt := abs_cos_lt_one_of_sin_ne_zero
      (Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos (ha.trans_le (hζ.1.trans hζ.2)))
        (mul_lt_of_lt_one_right pi_pos hb)).ne'
    linarith [neg_abs_le (Real.cos (π * b))]
  have hcos : Real.cos (π * b) ≤ Real.cos (π * ζ.re) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg pi_pos.le (ha.le.trans hζ.1))
      (mul_le_of_le_one_right pi_pos.le hb.le) (mul_le_mul_of_nonneg_left hζ.2 pi_pos.le)
  have hden : 2 * Real.exp (-(π * ζ.im)) * (1 + Real.cos (π * b)) ≤
      ‖1 + Complex.exp (I * π * ζ)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, normSq_one_add_exp_eq_two_mul_cosh_add_cos]
    nlinarith [Real.one_le_cosh (π * ζ.im), Real.exp_pos (-(π * ζ.im))]
  have hre : (I * π * ζ).re = -(π * ζ.im) := by simp
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg pi_pos.le, norm_pow,
    Complex.norm_exp, hre]
  refine (div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans_eq ?_
  field_simp [(Real.exp_pos (-(π * ζ.im))).ne']

private theorem integrable_mul_holoPoisson₁ {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    Integrable (fun s : ℝ => (u s : ℂ) * holoPoisson₁ (ζ - s * I)) :=
  ((continuous_ofReal.comp hu).mul (Continuous.div continuous_const (by fun_prop) fun _ =>
    one_add_exp_ne_zero ⟨by simpa using hζ.1, by simpa using hζ.2⟩)).integrable_of_hasCompactSupport
    (hsupp.comp_left Complex.ofReal_zero).mul_right

private theorem integral_holoPoisson₀_eq (u : ℝ → ℝ) (ζ : ℂ) :
    ∫ s, (u s : ℂ) * holoPoisson₀ (ζ - s * I) =
      ∫ s, (u (-s) : ℂ) * holoPoisson₁ ((1 - ζ) - s * I) := by
  rw [← MeasureTheory.integral_neg_eq_self (fun s : ℝ => (u s : ℂ) * holoPoisson₀ (ζ - s * I))]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  dsimp only [holoPoisson₀]
  have harg : 1 - (ζ - ((-s : ℝ) : ℂ) * I) = (1 - ζ) - (s : ℂ) * I := by push_cast; ring
  rw [harg]

/-- Convolving a continuous compactly supported function `u` with `holoPoisson₁` produces a
holomorphic function on the open vertical strip `0 < re ζ < 1`. -/
theorem differentiableOn_integral_holoPoisson₁ {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) :
    DifferentiableOn ℂ (fun ζ => ∫ s, (u s : ℂ) * holoPoisson₁ (ζ - s * I))
      (verticalStrip 0 1) := by
  intro ζ₀ hζ₀
  let r := min (ζ₀.re / 2) ((1 - ζ₀.re) / 2)
  have hr : 0 < r := lt_min (half_pos hζ₀.1) (half_pos (sub_pos.2 hζ₀.2))
  let a := ζ₀.re - r
  let b := ζ₀.re + r
  have ha : 0 < a := by grind
  have hb : b < 1 := by grind
  have hmem {ζ : ℂ} (hζ : ζ ∈ ball ζ₀ r) (s : ℝ) : (ζ - s * I).re ∈ Icc a b := by
    have hre : |ζ.re - ζ₀.re| < r := (abs_re_le_norm (ζ - ζ₀)).trans_lt (mem_ball_iff_norm.1 hζ)
    simp only [sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      sub_zero, mem_Icc, a, b]
    grind [abs_lt]
  let C := π / (2 * (1 + Real.cos (π * b)))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := ball ζ₀ r)
    (F := fun ζ (s : ℝ) => (u s : ℂ) * holoPoisson₁ (ζ - s * I))
    (F' := fun ζ (s : ℝ) => (u s : ℂ) *
      ((π : ℂ) * Complex.exp (I * π * (ζ - s * I)) / (1 + Complex.exp (I * π * (ζ - s * I))) ^ 2))
    (bound := fun s => |C| * ‖u s‖) (ball_mem_nhds ζ₀ hr) ?_
    (integrable_mul_holoPoisson₁ hu hsupp hζ₀) ?_ ?_
    ((hu.integrable_of_hasCompactSupport hsupp).norm.const_mul |C|) ?_).2.differentiableAt
    |>.differentiableWithinAt
  · filter_upwards [ball_mem_nhds ζ₀ hr] with ζ hζ
    exact ((continuous_ofReal.comp hu).mul (Continuous.div continuous_const (by fun_prop) fun s =>
      one_add_exp_ne_zero ⟨ha.trans_le (hmem hζ s).1, (hmem hζ s).2.trans_lt hb⟩))
      |>.aestronglyMeasurable
  · exact ((continuous_ofReal.comp hu).mul (Continuous.div (by fun_prop) (by fun_prop) fun s =>
      pow_ne_zero 2 (one_add_exp_ne_zero ⟨ha.trans_le (hmem (mem_ball_self hr) s).1,
        (hmem (mem_ball_self hr) s).2.trans_lt hb⟩))).aestronglyMeasurable
  · exact ae_of_all _ fun s ζ hζ => by
      rw [norm_mul, Complex.norm_real, mul_comm]
      exact mul_le_mul_of_nonneg_right
        ((norm_deriv_holoPoisson₁_le ha hb (hmem hζ s)).trans (le_abs_self C)) (norm_nonneg _)
  · exact ae_of_all _ fun s ζ hζ => by
      have hm := hmem hζ s
      simpa using ((hasDerivAt_holoPoisson₁ ⟨ha.trans_le hm.1, hm.2.trans_lt hb⟩).comp ζ
        ((hasDerivAt_id ζ).sub_const _)).const_mul (u s : ℂ)

/-- Convolving a continuous compactly supported function `u` with `holoPoisson₀` produces a
holomorphic function on the open vertical strip `0 < re ζ < 1`. -/
theorem differentiableOn_integral_holoPoisson₀ {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) :
    DifferentiableOn ℂ (fun ζ => ∫ s, (u s : ℂ) * holoPoisson₀ (ζ - s * I))
      (verticalStrip 0 1) := by
  simp_rw [integral_holoPoisson₀_eq]
  have h1 : Differentiable ℂ (fun ζ : ℂ => 1 - ζ) := by fun_prop
  exact (differentiableOn_integral_holoPoisson₁ (hu.comp continuous_neg)
    (hsupp.comp_homeomorph (Homeomorph.neg ℝ))).comp h1.differentiableOn fun _ hζ =>
      one_sub_mem_verticalStrip_iff.2 hζ

/-- The real part of the `holoPoisson₁` convolution of `u` at `ζ ∈ verticalStrip 0 1` is the
`stripPoisson₁` integral of `u`. -/
theorem re_integral_holoPoisson₁ {u : ℝ → ℝ} (hu : Continuous u)
    (hs : HasCompactSupport u) {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    (∫ s, (u s : ℂ) * holoPoisson₁ (ζ - s * I)).re =
      ∫ s, u s * stripPoisson₁ ζ.re (ζ.im - s) := by
  refine (Complex.reCLM.integral_comp_comm (integrable_mul_holoPoisson₁ hu hs hζ)).symm.trans
    (integral_congr_ae (ae_of_all _ fun s => ?_))
  simp [re_holoPoisson₁]

/-- The real part of the `holoPoisson₀` convolution of `u` at `ζ ∈ verticalStrip 0 1` is the
`stripPoisson₀` integral of `u`. -/
theorem re_integral_holoPoisson₀ {u : ℝ → ℝ} (hu : Continuous u)
    (hs : HasCompactSupport u) {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    (∫ s, (u s : ℂ) * holoPoisson₀ (ζ - s * I)).re =
      ∫ s, u s * stripPoisson₀ ζ.re (ζ.im - s) := by
  rw [integral_holoPoisson₀_eq]
  have hrefl :
      (∫ s, (u (-s) : ℂ) * holoPoisson₁ ((1 - ζ) - s * I)).re =
        ∫ s, u (-s) * stripPoisson₁ (1 - ζ).re ((1 - ζ).im - s) := by
    simpa only [Function.comp_apply] using
      re_integral_holoPoisson₁ (hu.comp continuous_neg) (hs.comp_homeomorph (Homeomorph.neg ℝ))
        (one_sub_mem_verticalStrip_iff.2 hζ)
  rw [hrefl,
    ← MeasureTheory.integral_neg_eq_self (fun s : ℝ => u s * stripPoisson₀ ζ.re (ζ.im - s))]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  dsimp only
  have harg : -ζ.im - s = -(ζ.im - -s) := by ring
  rw [sub_re, one_re, sub_im, one_im, zero_sub, stripPoisson₁_one_sub, harg, stripPoisson₀_neg]

/-- For fixed `r > 0`, the mass `∫ y in (-r)..r, stripPoisson₀ ε y` converges to `1` as `ε → 0⁺`. -/
theorem tendsto_intervalIntegral_stripPoisson₀_nhdsGT {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε => ∫ y in (-r)..r, stripPoisson₀ ε y) (𝓝[>] 0) (𝓝 1) := by
  have hsin_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < Real.sin (π * ε) := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    exact Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hε.1) (mul_lt_of_lt_one_right pi_pos hε.2)
  have hinv : Tendsto (fun ε : ℝ => (Real.sin (π * ε))⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2
      ⟨by simpa using ((by fun_prop : Continuous fun ε : ℝ => Real.sin (π * ε)).tendsto 0)
        |>.mono_left nhdsWithin_le_nhds, hsin_pos⟩)
  have hcos : Tendsto (fun ε : ℝ => Real.cos (π * ε)) (𝓝[>] 0) (𝓝 1) := by
    simpa using ((by fun_prop : Continuous fun ε : ℝ => Real.cos (π * ε)).tendsto 0)
      |>.mono_left nhdsWithin_le_nhds
  have hF_top : Tendsto
      (fun ε => π⁻¹ * Real.arctan ((Real.exp (π * r) - Real.cos (π * ε)) / Real.sin (π * ε)))
      (𝓝[>] 0) (𝓝 (2⁻¹ : ℝ)) := by
    rw [← inv_pi_mul_pi_div_two]
    refine ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ?_).const_mul π⁻¹
    simpa only [div_eq_mul_inv] using (tendsto_const_nhds.sub hcos).pos_mul_atTop
      (sub_pos.2 (Real.one_lt_exp_iff.2 (mul_pos pi_pos hr))) hinv
  have hF_bot : Tendsto
      (fun ε => π⁻¹ * Real.arctan ((Real.exp (-(π * r)) - Real.cos (π * ε)) / Real.sin (π * ε)))
      (𝓝[>] 0) (𝓝 (-(2⁻¹ : ℝ))) := by
    have hneg : -(2⁻¹ : ℝ) = π⁻¹ * -(π / 2) := by rw [← inv_pi_mul_pi_div_two]; ring
    rw [hneg]
    refine ((Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (tendsto_neg_atTop_iff.1 ?_)).const_mul π⁻¹
    simpa only [div_eq_mul_inv, ← neg_mul, neg_sub] using
      (hcos.sub tendsto_const_nhds).pos_mul_atTop
        (sub_pos.2 (Real.exp_lt_one_iff.2 (neg_neg_of_pos (mul_pos pi_pos hr)))) hinv
  have hsub : (2⁻¹ : ℝ) - -(2⁻¹ : ℝ) = 1 := by norm_num
  refine (hsub ▸ hF_top.sub hF_bot).congr' ?_
  filter_upwards [hsin_pos] with ε hsin
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_stripPoisson₀_primitive hsin.ne' y)
    (integrable_stripPoisson₀ ε).intervalIntegrable]
  simp [mul_neg]

private theorem mul_le_integral_mul_stripPoisson₀ {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) (hunonneg : ∀ s, 0 ≤ u s) {ε c r a b : ℝ} (hε : ε ∈ Ioo 0 1)
    (ha : 0 ≤ a) (hb : b ≤ ∫ s in Icc (c - r) (c + r), stripPoisson₀ ε (c - s))
    (hpt : ∀ s ∈ Icc (c - r) (c + r), a ≤ u s) :
    a * b ≤ ∫ s, u s * stripPoisson₀ ε (c - s) := by
  have hint : Integrable (fun s => u s * stripPoisson₀ ε (c - s)) :=
    (hu.mul ((continuous_stripPoisson₀ ε).comp (continuous_const.sub continuous_id)))
      |>.integrable_of_hasCompactSupport hsupp.mul_right
  calc a * b ≤ ∫ s in Icc (c - r) (c + r), a * stripPoisson₀ ε (c - s) := by
        rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hb ha
    _ ≤ ∫ s in Icc (c - r) (c + r), u s * stripPoisson₀ ε (c - s) :=
        setIntegral_mono_on
          (((integrable_stripPoisson₀ ε).comp_sub_left c).const_mul a).integrableOn
          hint.integrableOn measurableSet_Icc fun s hs =>
            mul_le_mul_of_nonneg_right (hpt s hs) (stripPoisson₀_pos hε (c - s)).le
    _ ≤ ∫ s, u s * stripPoisson₀ ε (c - s) :=
        setIntegral_le_integral hint
          (ae_of_all _ fun s => mul_nonneg (hunonneg s) (stripPoisson₀_pos hε (c - s)).le)

/-- Approximate identity lower bound of `stripPoisson₀ ε` as `ε → 0⁺` on compact intervals, for a
nonnegative compactly supported continuous function. -/
theorem exists_eps_integral_stripPoisson₀_ge {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) (hunonneg : ∀ s, 0 ≤ u s) {T κ : ℝ} (hκ : 0 < κ) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ t ∈ Icc (-T) T,
      u t - κ ≤ ∫ s, u s * stripPoisson₀ ε (((1 - 2 * ε) * t) - s) := by
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hu
  let U := max M 1
  have hUpos : 0 < U := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨η, hηpos, hη⟩ := Metric.uniformContinuous_iff.1
    (hsupp.uniformContinuous_of_continuous hu) (κ / 3) (by positivity)
  have hκU : 0 < κ / (3 * U) := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁_mem⟩ := Metric.mem_nhdsWithin_iff.1
    ((tendsto_intervalIntegral_stripPoisson₀_nhdsGT (half_pos hηpos)).eventually
      (Ioo_mem_nhds (sub_lt_self 1 hκU) (by norm_num : (1 : ℝ) < 2)))
  refine ⟨min (min δ₁ (2⁻¹ : ℝ)) ((η / 2) / (2 * max T 1)),
    lt_min (lt_min hδ₁ (by norm_num)) (by positivity), fun ε hε t ht => ?_⟩
  have hεI : ε ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.1, (hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))).trans (by norm_num)⟩
  by_cases hsign : u t - κ / 3 ≤ 0
  · exact (by linarith : u t - κ ≤ 0).trans
      (integral_nonneg fun s => mul_nonneg (hunonneg s) (stripPoisson₀_pos hεI _).le)
  have hstep1 : u t - κ ≤ (u t - κ / 3) * (1 - κ / (3 * U)) := by
    have hu_le : u t ≤ U := (le_abs_self (u t)).trans ((hM t).trans (le_max_left _ _))
    have h1 := mul_le_mul_of_nonneg_right (by linarith : u t - κ / 3 ≤ U) hκU.le
    have h2 : U * (κ / (3 * U)) = κ / 3 := by field_simp [hUpos.ne']
    linarith
  refine hstep1.trans (mul_le_integral_mul_stripPoisson₀ (r := η / 2) hu hsupp hunonneg hεI
    (not_le.1 hsign).le ?_ fun s hs => ?_)
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_sub_left (fun y => stripPoisson₀ ε y), sub_add_cancel_left,
      sub_sub_cancel]
    exact (hδ₁_mem ⟨by simp [abs_of_pos hε.1,
      hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))], hε.1⟩).1.le
  · have hMT : 0 < max T 1 := zero_lt_one.trans_le (le_max_right _ _)
    have hεb : ε < (η / 2) / (2 * max T 1) := hε.2.trans_le (min_le_right _ _)
    have hdiff : (1 - 2 * ε) * t - t = -(2 * ε * t) := by ring
    have hεT : |(1 - 2 * ε) * t - t| < η / 2 := calc
      |(1 - 2 * ε) * t - t| = 2 * ε * |t| := by
        rw [hdiff, abs_neg, abs_mul, abs_of_pos (mul_pos zero_lt_two hε.1)]
      _ ≤ 2 * ε * max T 1 := mul_le_mul_of_nonneg_left ((abs_le.2 ht).trans (le_max_left _ _))
          (mul_pos zero_lt_two hε.1).le
      _ < 2 * ((η / 2) / (2 * max T 1)) * max T 1 := by gcongr
      _ = η / 2 := by field_simp [hMT.ne']
    have hs' : |s - (1 - 2 * ε) * t| ≤ η / 2 :=
      abs_sub_le_iff.2 ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hd : dist (u s) (u t) < κ / 3 :=
      hη (by rw [Real.dist_eq]; linarith [abs_sub_le s ((1 - 2 * ε) * t) t])
    rw [Real.dist_eq] at hd
    linarith [(abs_sub_le_iff.1 hd.le).2]

end StripKernel

end TauCeti
