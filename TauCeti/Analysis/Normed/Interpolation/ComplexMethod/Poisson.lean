/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Symmetry

/-!
# Strip Poisson kernels and log-convexity of the complex interpolation norm

On the vertical strip `0 ≤ re z ≤ 1`, bounded harmonic functions are reconstructed from their
boundary values on `re z = 0` and `re z = 1` by the two strip Poisson kernels

* `TauCeti.stripPoisson₀ θ t = sin (π θ) / (2 (cosh (π t) - cos (π θ)))`, of integral `1 - θ`
  for `0 < θ ≤ 1` (`TauCeti.integral_stripPoisson₀`);
* `TauCeti.stripPoisson₁ θ t = sin (π θ) / (2 (cosh (π t) + cos (π θ)))`, of integral `θ`
  for `0 ≤ θ < 1` (`TauCeti.integral_stripPoisson₁`).

Multiplying an admissible strip function `F` by `exp (-Φ ((1 - 2 ε) z + ε))`, where `Φ` is the
holomorphic strip potential of compactly supported logarithmic envelopes of the boundary norms,
and applying Jensen's inequality yields Bergh–Löfström's Poisson estimate for Calderón's complex
method:

* `CompatibleCouple.ComplexMethodSpace.norm_mk_le_integral_stripPoisson`: for `0 < θ < 1`,
  `‖mk θ g‖ ≤ ((1 - θ)⁻¹ ∫ ‖g₀ t‖ P₀(θ, t) dt) ^ (1 - θ) * (θ⁻¹ ∫ ‖g₁ t‖ P₁(θ, t) dt) ^ θ`.
* `CompatibleCouple.ComplexMethodSpace.norm_mk_le_rpow_mul_rpow`: the three-lines bound
  `‖mk θ g‖ ≤ ‖g₀‖ ^ (1 - θ) * ‖g₁‖ ^ θ` in `[X₀, X₁]_θ` for every real `θ`.
* `CompatibleCouple.ComplexMethodSpace.norm_mk_zero` and `norm_mk_one`: endpoint norm formulas.
* `CompatibleCouple.ComplexMethodSpace.exists_stripTraces_smul_of_diffContOnCl`: multiplying an
  admissible trace by a bounded strip-analytic scalar `c` multiplies `mk θ g` by `c θ`.

Because `stripPoisson₀ θ` and `stripPoisson₁ θ` depend only on `(θ, t)`, this yields vector-valued
`Lᵖ` and `ℓ^q` complex interpolation without completeness or duality assumptions.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.3 (Lemma 4.3.2).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Metric Real Set Topology
open scoped ZeroAtInfty

namespace TauCeti

/-! ### The Poisson kernels of the unit vertical strip -/

/-- The left boundary Poisson kernel `P₀(θ, t) = sin (π θ) / (2 (cosh (π t) - cos (π θ)))` of the
vertical strip `0 ≤ re z ≤ 1`. For `0 < θ < 1` it is strictly positive and has integral `1 - θ`
over `ℝ`. -/
def stripPoisson₀ (θ t : ℝ) : ℝ :=
  Real.sin (π * θ) / (2 * (Real.cosh (π * t) - Real.cos (π * θ)))

/-- The right boundary Poisson kernel `P₁(θ, t) = sin (π θ) / (2 (cosh (π t) + cos (π θ)))` of the
vertical strip `0 ≤ re z ≤ 1`. For `0 < θ < 1` it is strictly positive and has integral `θ`
over `ℝ`. -/
def stripPoisson₁ (θ t : ℝ) : ℝ :=
  Real.sin (π * θ) / (2 * (Real.cosh (π * t) + Real.cos (π * θ)))

@[simp]
theorem stripPoisson₀_neg (θ t : ℝ) : stripPoisson₀ θ (-t) = stripPoisson₀ θ t := by
  simp [stripPoisson₀, mul_neg, Real.cosh_neg]

@[simp]
theorem stripPoisson₁_neg (θ t : ℝ) : stripPoisson₁ θ (-t) = stripPoisson₁ θ t := by
  simp [stripPoisson₁, mul_neg, Real.cosh_neg]

/-- Reflecting `θ ↦ 1 - θ` exchanges the two strip Poisson kernels. -/
theorem stripPoisson₀_one_sub (θ t : ℝ) : stripPoisson₀ (1 - θ) t = stripPoisson₁ θ t := by
  rw [stripPoisson₀, stripPoisson₁, show π * (1 - θ) = π - π * θ by ring,
    Real.sin_pi_sub, Real.cos_pi_sub, sub_neg_eq_add]

/-- Reflecting `θ ↦ 1 - θ` exchanges the two strip Poisson kernels. -/
theorem stripPoisson₁_one_sub (θ t : ℝ) : stripPoisson₁ (1 - θ) t = stripPoisson₀ θ t := by
  simpa using (stripPoisson₀_one_sub (1 - θ) t).symm

@[simp]
theorem stripPoisson₀_zero (t : ℝ) : stripPoisson₀ 0 t = 0 := by simp [stripPoisson₀]

@[simp]
theorem stripPoisson₀_one (t : ℝ) : stripPoisson₀ 1 t = 0 := by simp [stripPoisson₀]

@[simp]
theorem stripPoisson₁_zero (t : ℝ) : stripPoisson₁ 0 t = 0 := by simp [stripPoisson₁]

@[simp]
theorem stripPoisson₁_one (t : ℝ) : stripPoisson₁ 1 t = 0 := by simp [stripPoisson₁]

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
  · rw [show stripPoisson₀ θ = 0 by ext t; simp [stripPoisson₀, h]]; exact continuous_const
  exact Continuous.div continuous_const (by fun_prop) fun t =>
    (mul_pos zero_lt_two (cosh_sub_cos_pos_of_sin_ne_zero h t)).ne'

/-- For every real `θ`, `t ↦ stripPoisson₁ θ t` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_stripPoisson₁ (θ : ℝ) : Continuous (stripPoisson₁ θ) := by
  simpa only [show stripPoisson₁ θ = stripPoisson₀ (1 - θ) from
    funext fun t => (stripPoisson₀_one_sub θ t).symm] using continuous_stripPoisson₀ (1 - θ)

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
  rw [stripPoisson₀, hden, Real.exp_neg]
  have hsq : (Real.exp (π * t) - Real.cos (π * θ)) ^ 2 + Real.sin (π * θ) ^ 2 ≠ 0 := by positivity
  field_simp [pi_ne_zero, (Real.exp_pos (π * t)).ne', hsin, hsq]
  ring

/-- For every real `θ`, the left strip Poisson kernel is integrable on `ℝ`. -/
theorem integrable_stripPoisson₀ (θ : ℝ) : Integrable (stripPoisson₀ θ) := by
  by_cases hsin : Real.sin (π * θ) = 0
  · simp [show stripPoisson₀ θ = 0 by ext t; simp [stripPoisson₀, hsin]]
  have hc : 0 < 1 - |Real.cos (π * θ)| := sub_pos.2 (abs_cos_lt_one_of_sin_ne_zero hsin)
  have hIoi : IntegrableOn (stripPoisson₀ θ) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 pi_pos).const_mul
      (|Real.sin (π * θ)| / (1 - |Real.cos (π * θ)|))).mono'
      (continuous_stripPoisson₀ θ).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    have hcosh : Real.exp (π * t) / 2 ≤ Real.cosh (π * t) := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-(π * t))]
    have hden : (1 - |Real.cos (π * θ)|) * Real.exp (π * t) ≤
        2 * (Real.cosh (π * t) - Real.cos (π * θ)) := by
      nlinarith [one_sub_abs_cos_mul_cosh_le (θ := θ) t, hcosh]
    rw [Real.norm_eq_abs, stripPoisson₀, abs_div,
      abs_of_pos (mul_pos zero_lt_two (cosh_sub_cos_pos_of_sin_ne_zero hsin t))]
    refine (div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hc (Real.exp_pos _)) hden).trans_eq ?_
    rw [neg_mul, Real.exp_neg]; field_simp [hc.ne']
  have hIic : IntegrableOn (stripPoisson₀ θ) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ),
      show Measure.map Neg.neg volume = Measure.map (Homeomorph.neg ℝ) volume from rfl,
      (Homeomorph.neg ℝ).measurableEmbedding.integrableOn_map_iff]
    simpa [Function.comp_def, stripPoisson₀_neg, integrableOn_Ici_iff_integrableOn_Ioi] using hIoi
  exact integrableOn_univ.1 (Iic_union_Ioi (a := (0 : ℝ)) ▸ hIic.union hIoi)

/-- For every real `θ`, the right strip Poisson kernel is integrable on `ℝ`. -/
theorem integrable_stripPoisson₁ (θ : ℝ) : Integrable (stripPoisson₁ θ) := by
  simpa only [show stripPoisson₁ θ = stripPoisson₀ (1 - θ) from
    funext fun t => (stripPoisson₀_one_sub θ t).symm] using integrable_stripPoisson₀ (1 - θ)

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
    rw [show (2⁻¹ : ℝ) = π⁻¹ * (π / 2) by field_simp [pi_ne_zero]]
    exact ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1').const_mul π⁻¹
  have hbot : Tendsto
      (fun s => π⁻¹ * Real.arctan ((Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ)))
      atBot (𝓝 (θ - 2⁻¹)) := by
    have hexp0 := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot pi_pos)
    have hval : π⁻¹ * Real.arctan ((0 - Real.cos (π * θ)) / Real.sin (π * θ)) = θ - 2⁻¹ := by
      rw [zero_sub, show -Real.cos (π * θ) / Real.sin (π * θ) = Real.tan (π * θ - π / 2) by
          rw [Real.tan_eq_sin_div_cos, Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two],
        Real.arctan_tan (by nlinarith [pi_pos, hθ.1]) (by nlinarith [pi_pos, h1])]
      field_simp [pi_ne_zero]
    rw [← hval]
    exact ((Real.continuous_arctan.tendsto _).comp ((hexp0.sub_const _).div_const _)).const_mul π⁻¹
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_stripPoisson₀_primitive hsin.ne')
    (integrable_stripPoisson₀ θ) hbot htop]
  ring

/-- For `0 ≤ θ < 1`, the right strip Poisson kernel has total integral `θ` on `ℝ`. -/
theorem integral_stripPoisson₁ {θ : ℝ} (hθ : θ ∈ Ico 0 1) :
    ∫ t, stripPoisson₁ θ t = θ := by
  simpa only [show stripPoisson₁ θ = stripPoisson₀ (1 - θ) from
      funext fun t => (stripPoisson₀_one_sub θ t).symm, sub_sub_cancel] using
    integral_stripPoisson₀ ⟨sub_pos.2 hθ.2, sub_le_self 1 hθ.1⟩

/-! ### Holomorphic strip kernel and Poisson approximation -/

namespace CompatibleCouple

section StripKernel

/-- The holomorphic strip kernel `I / (1 + exp (I π ζ))`, whose real part on `0 < re ζ < 1` is
`stripPoisson₁ ζ.re ζ.im`. -/
private def holoPoisson₁ (ζ : ℂ) : ℂ :=
  I / (1 + Complex.exp (I * π * ζ))

private def holoPoisson₀ (ζ : ℂ) : ℂ :=
  holoPoisson₁ (1 - ζ)

private theorem one_add_exp_I_pi_mul_eq (ζ : ℂ) :
    1 + Complex.exp (I * π * ζ) =
      ((1 + Real.exp (-(π * ζ.im)) * Real.cos (π * ζ.re) : ℝ) : ℂ) +
        ((Real.exp (-(π * ζ.im)) * Real.sin (π * ζ.re) : ℝ) : ℂ) * I := by
  have harg : I * π * ζ = ((-(π * ζ.im) : ℝ) : ℂ) + ((π * ζ.re : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [harg, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

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

private theorem re_holoPoisson₁ (ζ : ℂ) :
    (holoPoisson₁ ζ).re = stripPoisson₁ ζ.re ζ.im := by
  rw [holoPoisson₁, Complex.div_re, normSq_one_add_exp_eq_two_mul_cosh_add_cos,
    one_add_exp_I_pi_mul_eq, stripPoisson₁]
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
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg pi_pos.le, norm_pow,
    Complex.norm_exp, show (I * π * ζ).re = -(π * ζ.im) by simp]
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
  rw [show 1 - (ζ - ((-s : ℝ) : ℂ) * I) = (1 - ζ) - (s : ℂ) * I by push_cast; ring]

private theorem differentiableOn_integral_holoPoisson₁ {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) :
    DifferentiableOn ℂ (fun ζ => ∫ s, (u s : ℂ) * holoPoisson₁ (ζ - s * I))
      (verticalStrip 0 1) := by
  intro ζ₀ hζ₀
  let r := min (ζ₀.re / 2) ((1 - ζ₀.re) / 2)
  have hr : 0 < r := lt_min (half_pos hζ₀.1) (half_pos (sub_pos.2 hζ₀.2))
  let a := ζ₀.re - r; let b := ζ₀.re + r
  have ha : 0 < a := by grind
  have hb : b < 1 := by grind
  have hmem {ζ : ℂ} (hζ : ζ ∈ ball ζ₀ r) (s : ℝ) : (ζ - s * I).re ∈ Icc a b := by
    have hre : |ζ.re - ζ₀.re| < r := (abs_re_le_norm (ζ - ζ₀)).trans_lt (mem_ball_iff_norm.1 hζ)
    simp only [sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      sub_zero, mem_Icc, a, b]; grind [abs_lt]
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

private theorem differentiableOn_integral_holoPoisson₀ {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) :
    DifferentiableOn ℂ (fun ζ => ∫ s, (u s : ℂ) * holoPoisson₀ (ζ - s * I))
      (verticalStrip 0 1) := by
  simp_rw [integral_holoPoisson₀_eq]
  have h1 : Differentiable ℂ (fun ζ : ℂ => 1 - ζ) := by fun_prop
  exact (differentiableOn_integral_holoPoisson₁ (hu.comp continuous_neg)
    (hsupp.comp_homeomorph (Homeomorph.neg ℝ))).comp h1.differentiableOn fun _ hζ =>
      one_sub_mem_verticalStrip_iff.2 hζ

private theorem re_integral_holoPoisson₁ {u : ℝ → ℝ} (hu : Continuous u)
    (hs : HasCompactSupport u) {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    (∫ s, (u s : ℂ) * holoPoisson₁ (ζ - s * I)).re =
      ∫ s, u s * stripPoisson₁ ζ.re (ζ.im - s) := by
  refine (Complex.reCLM.integral_comp_comm (integrable_mul_holoPoisson₁ hu hs hζ)).symm.trans
    (integral_congr_ae (ae_of_all _ fun s => ?_))
  simp [re_holoPoisson₁]

private theorem re_integral_holoPoisson₀ {u : ℝ → ℝ} (hu : Continuous u)
    (hs : HasCompactSupport u) {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    (∫ s, (u s : ℂ) * holoPoisson₀ (ζ - s * I)).re =
      ∫ s, u s * stripPoisson₀ ζ.re (ζ.im - s) := by
  rw [integral_holoPoisson₀_eq]
  change (∫ s, ((u ∘ Neg.neg) s : ℂ) * holoPoisson₁ ((1 - ζ) - s * I)).re = _
  rw [re_integral_holoPoisson₁ (hu.comp continuous_neg) (hs.comp_homeomorph (Homeomorph.neg ℝ))
      (one_sub_mem_verticalStrip_iff.2 hζ),
    ← MeasureTheory.integral_neg_eq_self (fun s : ℝ => u s * stripPoisson₀ ζ.re (ζ.im - s))]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  dsimp only [Function.comp_apply]
  rw [sub_re, one_re, sub_im, one_im, zero_sub, stripPoisson₁_one_sub,
    show -ζ.im - s = -(ζ.im - -s) by ring, stripPoisson₀_neg]

/-- For fixed `r > 0`, the mass `∫ y in (-r)..r, stripPoisson₀ ε y` converges to `1` as `ε → 0⁺`. -/
private theorem tendsto_intervalIntegral_stripPoisson₀_nhdsGT {r : ℝ} (hr : 0 < r) :
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
    rw [show (2⁻¹ : ℝ) = π⁻¹ * (π / 2) by field_simp [pi_ne_zero]]
    refine ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ?_).const_mul π⁻¹
    simpa only [div_eq_mul_inv] using (tendsto_const_nhds.sub hcos).pos_mul_atTop
      (sub_pos.2 (Real.one_lt_exp_iff.2 (mul_pos pi_pos hr))) hinv
  have hF_bot : Tendsto
      (fun ε => π⁻¹ * Real.arctan ((Real.exp (-(π * r)) - Real.cos (π * ε)) / Real.sin (π * ε)))
      (𝓝[>] 0) (𝓝 (-(2⁻¹ : ℝ))) := by
    rw [show -(2⁻¹ : ℝ) = π⁻¹ * -(π / 2) by field_simp [pi_ne_zero]]
    refine ((Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (tendsto_neg_atTop_iff.1 ?_)).const_mul π⁻¹
    simpa only [div_eq_mul_inv, ← neg_mul, neg_sub] using
      (hcos.sub tendsto_const_nhds).pos_mul_atTop
        (sub_pos.2 (Real.exp_lt_one_iff.2 (neg_neg_of_pos (mul_pos pi_pos hr)))) hinv
  refine ((show (2⁻¹ : ℝ) - -(2⁻¹ : ℝ) = 1 by norm_num) ▸ hF_top.sub hF_bot).congr' ?_
  filter_upwards [hsin_pos] with ε hsin
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_stripPoisson₀_primitive hsin.ne' y)
    (integrable_stripPoisson₀ ε).intervalIntegrable]
  simp [mul_neg]

private theorem mul_sub_le_integral_stripPoisson₀ {u : ℝ → ℝ} (hu : Continuous u)
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
private theorem exists_eps_integral_stripPoisson₀_ge {u : ℝ → ℝ} (hu : Continuous u)
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
  refine hstep1.trans (mul_sub_le_integral_stripPoisson₀ (r := η / 2) hu hsupp hunonneg hεI
    (not_le.1 hsign).le ?_ fun s hs => ?_)
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_sub_left (fun y => stripPoisson₀ ε y), sub_add_cancel_left,
      sub_sub_cancel]
    exact (hδ₁_mem ⟨by simp [abs_of_pos hε.1,
      hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))], hε.1⟩).1.le
  · have hMT : 0 < max T 1 := zero_lt_one.trans_le (le_max_right _ _)
    have hεb : ε < (η / 2) / (2 * max T 1) := hε.2.trans_le (min_le_right _ _)
    have hεT : |(1 - 2 * ε) * t - t| < η / 2 := calc
      |(1 - 2 * ε) * t - t| = 2 * ε * |t| := by
        rw [show (1 - 2 * ε) * t - t = -(2 * ε * t) by ring, abs_neg, abs_mul,
          abs_of_pos (mul_pos zero_lt_two hε.1)]
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

/-! ### Stieltjes/Poisson bounds on the complex interpolation norm -/

namespace ComplexMethodSpace

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V}

private def smulC0 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : ℝ → ℂ}
    (hc : Continuous c) {K : ℝ} (hK : ∀ t, ‖c t‖ ≤ K) (f : C₀(ℝ, E)) : C₀(ℝ, E) :=
  ZeroAtInftyContinuousMap.compLeftFamily (fun t => c t • ContinuousLinearMap.id ℂ E)
    (fun _ => hc.smul continuous_const)
    ⟨K, fun t e => by simpa [norm_smul] using mul_le_mul_of_nonneg_right (hK t) (norm_nonneg e)⟩ f

/-- Multiplying an admissible trace pair by a bounded `DiffContOnCl` scalar function `c` on the
open unit strip produces an admissible trace pair whose boundary traces are `c • g` on the two
vertical lines and whose quotient class at `θ ∈ [0, 1]` is `c θ • mk θ g`. -/
theorem exists_stripTraces_smul_of_diffContOnCl (g : C.stripTraces) {c : ℂ → ℂ}
    (hc : DiffContOnCl ℂ c (verticalStrip 0 1)) {K : ℝ}
    (hK : ∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K) :
    ∃ g' : C.stripTraces,
      (∀ t : ℝ, (g' : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t =
        c (t * I) • (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t) ∧
      (∀ t : ℝ, (g' : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t =
        c (1 + t * I) • (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t) ∧
      ∀ ⦃θ : ℝ⦄, θ ∈ Icc 0 1 → mk θ g' = c θ • mk θ g := by
  have hcl {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) : z ∈ closure (verticalStrip 0 1) := by
    rw [verticalStrip, closure_preimage_re, closure_Ioo zero_ne_one]; exact hz
  let g₀' := smulC0 (hc.continuousOn.comp_continuous
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * I) fun _ =>
      hcl (by simp [verticalClosedStrip])) (fun _ => hK _ (by simp [verticalClosedStrip])) g.val.1
  let g₁' := smulC0 (hc.continuousOn.comp_continuous
    (by fun_prop : Continuous fun t : ℝ => 1 + (t : ℂ) * I) fun _ =>
      hcl (by simp [verticalClosedStrip])) (fun _ => hK _ (by simp [verticalClosedStrip])) g.val.2
  have hg₀' (t : ℝ) : g₀' t = c (t * I) • g.val.1 t := by
    simp [g₀', smulC0, ZeroAtInftyContinuousMap.compLeftFamily_apply]
  have hg₁' (t : ℝ) : g₁' t = c (1 + t * I) • g.val.2 t := by
    simp [g₁', smulC0, ZeroAtInftyContinuousMap.compLeftFamily_apply]
  have hF' : C.IsStripFunction (fun z => c z • C.stripFunction g z) (g₀', g₁') :=
    (C.isStripFunction_stripFunction g).smul hc hK hg₀' hg₁'
  refine ⟨⟨(g₀', g₁'), C.mem_stripTraces_iff.2 ⟨_, hF'⟩⟩, hg₀', hg₁',
    fun θ hθ => toSum_injective ?_⟩
  rw [toSum_mk, map_smul, toSum_mk, stripEval_apply, stripEval_apply,
    stripFunction_eq hF' (by simpa [verticalClosedStrip] using hθ)]

/-- Multiplying an admissible trace pair by a bounded holomorphic scalar function `c` on the strip
scales `mk θ g` by `c θ` and bounds its norm by the boundary suprema of `c • g`. -/
private theorem norm_smul_mk_le_of_diffContOnCl {θ : ℝ} (hθ : θ ∈ Icc 0 1) (g : C.stripTraces)
    {c : ℂ → ℂ} (hc : DiffContOnCl ℂ c (verticalStrip 0 1))
    {K B : ℝ} (hK : ∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K) (hB : 0 ≤ B)
    (hb₀ : ∀ t : ℝ, ‖c (t * I) • g.val.1 t‖ ≤ B)
    (hb₁ : ∀ t : ℝ, ‖c (1 + t * I) • g.val.2 t‖ ≤ B) :
    ‖c θ‖ * ‖mk θ g‖ ≤ B := by
  obtain ⟨g', hg₀', hg₁', heq⟩ := exists_stripTraces_smul_of_diffContOnCl g hc hK
  rw [← norm_smul, ← heq hθ]
  refine ((norm_mk_le g').trans_eq (Submodule.norm_coe g').symm).trans (max_le ?_ ?_)
  · exact (ZeroAtInftyContinuousMap.norm_le hB).2 fun t => by rw [hg₀']; exact hb₀ t
  · exact (ZeroAtInftyContinuousMap.norm_le hB).2 fun t => by rw [hg₁']; exact hb₁ t

private theorem norm_exp_quad_mul_le {E : Type*} [NormedAddCommGroup E] {x y : ℝ} {f : C₀(ℝ, E)}
    {ε : ℝ} (hx : 0 < x) (hy : x ≤ y) (hε : 0 < ε) (hA : 2 * ‖f‖ / ε < x) (t : ℝ) :
    Real.exp (-y) * ‖f t‖ ≤ ε / 2 := by
  have h1 : Real.exp (-y) ≤ x⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ hx (by linarith [Real.add_one_le_exp y])
  have h2 : ‖f‖ / x ≤ ε / 2 := (div_le_iff₀ hx).2 (by nlinarith [(div_lt_iff₀ hε).1 hA])
  exact (mul_le_mul h1 (ZeroAtInftyContinuousMap.norm_coe_le_norm f t) (norm_nonneg _)
    (inv_pos.2 hx).le).trans ((inv_mul_eq_div _ _).trans_le h2)

private theorem norm_mk_zero_le (g : C.stripTraces) : ‖mk 0 g‖ ≤ ‖g.val.1 0‖ := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.1
    ((map_continuous g.val.1).continuousAt (x := 0)) (ε / 2) (half_pos hε)
  obtain ⟨A, hAgt⟩ := exists_gt (max 0 (max (2 * ‖g.val.1‖ / (δ ^ 2 * ε)) (2 * ‖g.val.2‖ / ε)))
  have hA : 0 < A := (le_max_left _ _).trans_lt hAgt
  let c : ℂ → ℂ := fun z => Complex.exp ((A : ℂ) * (z ^ 2 - 2 * z))
  have hc_re (z : ℂ) : ((A : ℂ) * (z ^ 2 - 2 * z)).re = A * (z.re ^ 2 - z.im ^ 2 - 2 * z.re) := by
    simp [sq]
  have hc_le (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) : ‖c z‖ ≤ 1 := by
    rw [Complex.norm_exp, hc_re]
    exact Real.exp_le_one_iff.2
      (mul_nonpos_of_nonneg_of_nonpos hA.le (by nlinarith [hz.1, hz.2, sq_nonneg z.im]))
  have hbound := norm_smul_mk_le_of_diffContOnCl ⟨le_rfl, zero_le_one⟩ g
    (by unfold c; fun_prop : Differentiable ℂ c).diffContOnCl hc_le
    (B := ‖g.val.1 0‖ + ε / 2) (by positivity)
    (fun t => by
      rw [norm_smul]
      by_cases ht : |t| < δ
      · have hd := hclose (by simpa [Real.dist_eq] using ht)
        rw [dist_eq_norm] at hd
        exact (mul_le_of_le_one_left (norm_nonneg _)
          (hc_le (t * I) (by simp [verticalClosedStrip]))).trans
          (by linarith [norm_sub_norm_le (g.val.1 t) (g.val.1 0)])
      · have hsq : δ ^ 2 ≤ t ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ hδ.le (not_lt.1 ht) 2
        have hA1 := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hAgt
        have hA1' : 2 * ‖g.val.1‖ / ε < A * δ ^ 2 :=
          (div_lt_iff₀ hε).2 (by nlinarith [(div_lt_iff₀ (by positivity)).1 hA1])
        rw [show ‖c (t * I)‖ = Real.exp (-(A * t ^ 2)) by rw [Complex.norm_exp, hc_re]; simp]
        exact (norm_exp_quad_mul_le (by positivity) (by nlinarith) hε hA1' t).trans
          (le_add_of_nonneg_left (norm_nonneg _)))
    (fun t => by
      rw [norm_smul, show ‖c (1 + t * I)‖ = Real.exp (-(A * (1 + t ^ 2))) by
        rw [Complex.norm_exp, hc_re]; congr 1; simp; ring]
      exact (norm_exp_quad_mul_le hA (by nlinarith [sq_nonneg t]) hε
        (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hAgt) t).trans
        (le_add_of_nonneg_left (norm_nonneg _)))
  have hc0 : ‖c ((0 : ℝ) : ℂ)‖ = 1 := by simp [c]
  rw [hc0, one_mul] at hbound
  linarith [half_lt_self hε]

/-- At `θ = 0`, the quotient norm of an admissible trace pair is the norm in `X₀` of its left
boundary trace at `0`. -/
theorem norm_mk_zero (g : C.stripTraces) :
    ‖mk 0 g‖ = ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0‖ := by
  refine le_antisymm (norm_mk_zero_le g) (le_of_forall_gt fun r hr => ?_)
  obtain ⟨h, heq, hh⟩ := norm_lt_iff.1 hr
  have hsum : C.fstToSum (h.val.1 0) = C.fstToSum (g.val.1 0) := by
    have heval := congrArg toSum heq
    rw [toSum_mk, toSum_mk, stripEval_apply, stripEval_apply, ofReal_zero,
      ← zero_mul I, ← ofReal_zero, C.stripFunction_mul_I, C.stripFunction_mul_I] at heval
    exact heval
  have h0 : h.val.1 0 = g.val.1 0 :=
    C.embed₀_injective (by simpa [C.sumSpaceEmbed_fstToSum] using congrArg C.sumSpaceEmbed hsum)
  rw [← h0]
  exact ((ZeroAtInftyContinuousMap.norm_coe_le_norm _ 0).trans (norm_fst_le h.val)).trans_lt
    (by rwa [Submodule.norm_coe])

/-- At `θ = 1`, the quotient norm of an admissible trace pair is the norm in `X₁` of its right
boundary trace at `0`. -/
theorem norm_mk_one (g : C.stripTraces) :
    ‖mk 1 g‖ = ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 0‖ := by
  rw [← (swap C 1).norm_map (mk 1 g), swap_mk, sub_self, norm_mk_zero]
  simp only [stripTracesSwap_apply_fst, neg_zero]

private theorem exists_abs_ge_norm_le {E : Type*} [NormedAddCommGroup E] (f : C₀(ℝ, E))
    {δ : ℝ} (hδ : 0 < δ) : ∃ T > 0, ∀ s : ℝ, T ≤ |s| → ‖f s‖ ≤ δ := by
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.1
    ((tendsto_zero_iff_norm_tendsto_zero.1 (zero_at_infty f)).eventually (Iio_mem_nhds hδ))
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨max R 0 + 1, by positivity, fun s hs => (hKsub fun hsK => ?_).le⟩
  have hle : |s| ≤ R := by simpa [Real.dist_eq] using mem_closedBall.1 (hR hsK)
  linarith [le_max_left R 0]

private def logMaxDiv {E : Type*} [NormedAddCommGroup E] (f : C₀(ℝ, E)) (δ s : ℝ) : ℝ :=
  Real.log (max ‖f s‖ δ / δ)

private theorem continuous_logMaxDiv {E : Type*} [NormedAddCommGroup E] (f : C₀(ℝ, E))
    {δ : ℝ} (hδ : 0 < δ) : Continuous (logMaxDiv f δ) :=
  Continuous.log (((map_continuous f).norm.max continuous_const).div_const δ) fun _ =>
    (div_pos (hδ.trans_le (le_max_right _ _)) hδ).ne'

private theorem hasCompactSupport_logMaxDiv {E : Type*} [NormedAddCommGroup E] (f : C₀(ℝ, E))
    {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (logMaxDiv f δ) := by
  obtain ⟨T, _, hf⟩ := exists_abs_ge_norm_le f hδ
  refine HasCompactSupport.intro (K := Icc (-T) T) isCompact_Icc fun s hs => ?_
  have habs : T ≤ |s| := le_of_lt (not_le.1 fun h => hs (abs_le.1 h))
  simp [logMaxDiv, max_eq_right (hf s habs), div_self hδ.ne']

private theorem logMaxDiv_nonneg {E : Type*} [NormedAddCommGroup E] (f : C₀(ℝ, E))
    {δ : ℝ} (hδ : 0 < δ) (s : ℝ) : 0 ≤ logMaxDiv f δ s :=
  Real.log_nonneg ((one_le_div hδ).2 (le_max_right _ _))

private theorem log_add_logMaxDiv {E : Type*} [NormedAddCommGroup E] (f : C₀(ℝ, E))
    {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    Real.log δ + logMaxDiv f δ s = Real.log (max ‖f s‖ δ) := by
  rw [logMaxDiv, Real.log_div (hδ.trans_le (le_max_right _ _)).ne' hδ.ne']; ring

private def holoPotential (g : C.stripTraces) (δ : ℝ) (ζ : ℂ) : ℂ :=
  (Real.log δ : ℂ) +
    ((∫ s, (logMaxDiv g.val.1 δ s : ℂ) * holoPoisson₀ (ζ - s * I)) +
      ∫ s, (logMaxDiv g.val.2 δ s : ℂ) * holoPoisson₁ (ζ - s * I))

private theorem differentiableOn_holoPotential (g : C.stripTraces) {δ : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ (holoPotential g δ) (verticalStrip 0 1) :=
  (differentiableOn_const _).add
    ((differentiableOn_integral_holoPoisson₀ (continuous_logMaxDiv g.val.1 hδ)
        (hasCompactSupport_logMaxDiv g.val.1 hδ)).add
      (differentiableOn_integral_holoPoisson₁ (continuous_logMaxDiv g.val.2 hδ)
        (hasCompactSupport_logMaxDiv g.val.2 hδ)))

private theorem re_holoPotential (g : C.stripTraces) {δ : ℝ} (hδ : 0 < δ) {ζ : ℂ}
    (hζ : ζ ∈ verticalStrip 0 1) :
    (holoPotential g δ ζ).re = Real.log δ +
      ((∫ s, logMaxDiv g.val.1 δ s * stripPoisson₀ ζ.re (ζ.im - s)) +
        ∫ s, logMaxDiv g.val.2 δ s * stripPoisson₁ ζ.re (ζ.im - s)) := by
  simp only [holoPotential, add_re, ofReal_re,
    re_integral_holoPoisson₀ (continuous_logMaxDiv g.val.1 hδ)
      (hasCompactSupport_logMaxDiv g.val.1 hδ) hζ,
    re_integral_holoPoisson₁ (continuous_logMaxDiv g.val.2 hδ)
      (hasCompactSupport_logMaxDiv g.val.2 hδ) hζ]

private theorem norm_exp_neg_holoPotential_le (g : C.stripTraces) {δ : ℝ} (hδ : 0 < δ) {ζ : ℂ}
    (hζ : ζ ∈ verticalStrip 0 1) :
    ‖Complex.exp (-holoPotential g δ ζ)‖ ≤ δ⁻¹ := by
  rw [Complex.norm_exp, neg_re, ← Real.exp_log (inv_pos.2 hδ), Real.log_inv,
    re_holoPotential g hδ hζ]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have h0 : 0 ≤ ∫ s, logMaxDiv g.val.1 δ s * stripPoisson₀ ζ.re (ζ.im - s) :=
    integral_nonneg fun s => mul_nonneg (logMaxDiv_nonneg g.val.1 hδ s) (stripPoisson₀_pos hζ _).le
  have h1 : 0 ≤ ∫ s, logMaxDiv g.val.2 δ s * stripPoisson₁ ζ.re (ζ.im - s) :=
    integral_nonneg fun s => mul_nonneg (logMaxDiv_nonneg g.val.2 hδ s) (stripPoisson₁_pos hζ _).le
  linarith

private theorem norm_exp_neg_mul_le_of_re_ge {E : Type*} [NormedAddCommGroup E] {δ κ : ℝ}
    (hδ : 0 < δ) {x : E} {w : ℂ} (hre : Real.log (max ‖x‖ δ) - κ ≤ w.re) :
    ‖Complex.exp (-w)‖ * ‖x‖ ≤ Real.exp κ := by
  have hm : 0 < max ‖x‖ δ := hδ.trans_le (le_max_right _ _)
  calc ‖Complex.exp (-w)‖ * ‖x‖
      ≤ Real.exp (κ - Real.log (max ‖x‖ δ)) * max ‖x‖ δ :=
        mul_le_mul (by rw [Complex.norm_exp, neg_re]; exact Real.exp_le_exp.2 (by linarith))
          (le_max_left _ _) (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp κ := by
        rw [Real.exp_sub, div_mul_eq_mul_div, Real.exp_log hm, mul_div_cancel_right₀ _ hm.ne']

private theorem integral_neg_stripPoisson₀_eq (u : ℝ → ℝ) (ε t : ℝ) :
    ∫ s, (u ∘ Neg.neg) s * stripPoisson₀ ε ((1 - 2 * ε) * (-t) - s) =
      ∫ s, u s * stripPoisson₁ (1 - ε) ((1 - 2 * ε) * t - s) := by
  rw [← MeasureTheory.integral_neg_eq_self
    (fun s : ℝ => u s * stripPoisson₁ (1 - ε) ((1 - 2 * ε) * t - s))]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [Function.comp_apply, stripPoisson₁_one_sub,
    show (1 - 2 * ε) * t - -s = -((1 - 2 * ε) * (-t) - s) by ring, stripPoisson₀_neg]

private theorem norm_mk_le_exp_re_contracted_holoPotential {θ δ T κ ε : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hδ : 0 < δ) (hκ : 0 < κ) (hε : ε ∈ Ioo (0 : ℝ) 4⁻¹) (g : C.stripTraces)
    (hg₀ : ∀ s, T ≤ |s| → ‖g.val.1 s‖ ≤ δ) (hg₁ : ∀ s, T ≤ |s| → ‖g.val.2 s‖ ≤ δ)
    (happrox₀ : ∀ t ∈ Icc (-T) T, logMaxDiv g.val.1 δ t - κ ≤
      ∫ s, logMaxDiv g.val.1 δ s * stripPoisson₀ ε ((1 - 2 * ε) * t - s))
    (happrox₁ : ∀ t ∈ Icc (-T) T, (logMaxDiv g.val.2 δ ∘ Neg.neg) t - κ ≤
      ∫ s, (logMaxDiv g.val.2 δ ∘ Neg.neg) s * stripPoisson₀ ε ((1 - 2 * ε) * t - s)) :
    ‖mk θ g‖ ≤ Real.exp κ *
      Real.exp ((holoPotential g δ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re) := by
  let w : ℂ → ℂ := fun z => (1 - 2 * (ε : ℂ)) * z + ε
  have hw_strip {z : ℂ} (hz : z ∈ {z : ℂ | -(ε / 2) < z.re ∧ z.re < 1 + ε / 2}) :
      w z ∈ verticalStrip 0 1 := by
    rw [mem_verticalStrip_iff, show (w z).re = (1 - 2 * ε) * z.re + ε by simp [w], mem_Ioo]
    exact ⟨by nlinarith [hε.1, hε.2, hz.1], by nlinarith [hε.1, hε.2, hz.2]⟩
  let c : ℂ → ℂ := fun z => Complex.exp (-holoPotential g δ (w z))
  have hc_diff : DiffContOnCl ℂ c (verticalStrip 0 1) :=
    ((((differentiableOn_holoPotential g hδ).comp
      (by unfold w; fun_prop : Differentiable ℂ w).differentiableOn
      fun _ hz => hw_strip hz).neg).cexp.mono ((closure_verticalStrip_subset 0 1).trans fun _ hz =>
        ⟨by linarith [hε.1, hz.1], by linarith [hε.1, hz.2]⟩)).diffContOnCl
  have hc_le (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) : ‖c z‖ ≤ δ⁻¹ :=
    norm_exp_neg_holoPotential_le g hδ
      (hw_strip ⟨by linarith [hε.1, hz.1], by linarith [hε.1, hz.2]⟩)
  have htail {z : ℂ} {x : ℝ} (hz : z ∈ verticalClosedStrip 0 1) (hx0 : 0 ≤ x) (hx : x ≤ δ) :
      ‖c z‖ * x ≤ Real.exp κ :=
    (mul_le_mul (hc_le z hz) hx hx0 (inv_pos.2 hδ).le).trans
      ((inv_mul_cancel₀ hδ.ne').trans_le (Real.one_le_exp hκ.le))
  have hb := norm_smul_mk_le_of_diffContOnCl ⟨hθ.1.le, hθ.2.le⟩ g hc_diff hc_le (Real.exp_pos κ).le
    (fun t => by
      rw [norm_smul]
      by_cases ht : T ≤ |t|
      · exact htail (by simp [verticalClosedStrip]) (norm_nonneg _) (hg₀ t ht)
      refine norm_exp_neg_mul_le_of_re_ge hδ ?_
      rw [re_holoPotential g hδ (hw_strip ⟨by simp [hε.1], by simp; linarith [hε.1]⟩),
        show (w (t * I)).re = ε by simp [w], show (w (t * I)).im = (1 - 2 * ε) * t by simp [w]]
      have h1 : 0 ≤ ∫ s, logMaxDiv g.val.2 δ s * stripPoisson₁ ε ((1 - 2 * ε) * t - s) :=
        integral_nonneg fun s => mul_nonneg (logMaxDiv_nonneg g.val.2 hδ s)
          (stripPoisson₁_pos ⟨hε.1, by linarith [hε.2]⟩ _).le
      linarith [happrox₀ t (abs_le.1 (not_le.1 ht).le), log_add_logMaxDiv g.val.1 hδ t])
    (fun t => by
      rw [norm_smul]
      by_cases ht : T ≤ |t|
      · exact htail (by simp [verticalClosedStrip]) (norm_nonneg _) (hg₁ t ht)
      refine norm_exp_neg_mul_le_of_re_ge hδ ?_
      obtain ⟨ht1, ht2⟩ := abs_le.1 (not_le.1 ht).le
      have hap := happrox₁ (-t) ⟨by linarith, by linarith⟩
      rw [Function.comp_apply, neg_neg, integral_neg_stripPoisson₀_eq] at hap
      rw [re_holoPotential g hδ (hw_strip ⟨by simp; linarith [hε.1], by simp [hε.1]⟩),
        show (w (1 + t * I)).re = 1 - ε by simp [w]; ring,
        show (w (1 + t * I)).im = (1 - 2 * ε) * t by simp [w]]
      have h0 : 0 ≤ ∫ s, logMaxDiv g.val.1 δ s * stripPoisson₀ (1 - ε) ((1 - 2 * ε) * t - s) :=
        integral_nonneg fun s => mul_nonneg (logMaxDiv_nonneg g.val.1 hδ s)
          (stripPoisson₀_pos ⟨by linarith [hε.2], by linarith [hε.1]⟩ _).le
      linarith [log_add_logMaxDiv g.val.2 hδ t])
  rw [show ‖c θ‖ = (Real.exp ((holoPotential g δ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re))⁻¹ by
    simp [c, w, Complex.norm_exp, Real.exp_neg]] at hb
  exact ((inv_mul_le_iff₀ (Real.exp_pos _)).1 hb).trans_eq (mul_comm _ _)

private theorem norm_mk_le_exp_re_holoPotential {θ δ : ℝ} (hθ : θ ∈ Ioo 0 1) (hδ : 0 < δ)
    (g : C.stripTraces) :
    ‖mk θ g‖ ≤ Real.exp (Real.log δ +
      ((∫ s, logMaxDiv g.val.1 δ s * stripPoisson₀ θ s) +
        ∫ s, logMaxDiv g.val.2 δ s * stripPoisson₁ θ s)) := by
  obtain ⟨T₀, _, hg₀⟩ := exists_abs_ge_norm_le g.val.1 hδ
  obtain ⟨T₁, _, hg₁⟩ := exists_abs_ge_norm_le g.val.2 hδ
  let T := max T₀ T₁; let Φ := holoPotential g δ
  have hθstrip : (θ : ℂ) ∈ verticalStrip 0 1 := by simpa [verticalStrip] using hθ
  suffices hκ_le : ∀ κ > 0, ‖mk θ g‖ ≤ Real.exp κ * Real.exp (Φ θ).re by
    have htendκ : Tendsto (fun κ : ℝ => Real.exp κ * Real.exp (Φ θ).re) (𝓝[>] 0)
        (𝓝 (Real.exp (Φ θ).re)) := by
      simpa using ((by fun_prop : Continuous fun κ : ℝ => Real.exp κ * Real.exp (Φ θ).re).tendsto 0)
        |>.mono_left nhdsWithin_le_nhds
    refine (ge_of_tendsto htendκ (eventually_nhdsWithin_of_forall hκ_le)).trans_eq ?_
    simp [Φ, re_holoPotential g hδ hθstrip]
  intro κ hκ
  obtain ⟨ε₀, hε₀, happrox₀⟩ := exists_eps_integral_stripPoisson₀_ge
    (continuous_logMaxDiv g.val.1 hδ) (hasCompactSupport_logMaxDiv g.val.1 hδ)
    (logMaxDiv_nonneg g.val.1 hδ) (T := T) hκ
  obtain ⟨ε₁, hε₁, happrox₁⟩ := exists_eps_integral_stripPoisson₀_ge
    ((continuous_logMaxDiv g.val.2 hδ).comp continuous_neg)
    ((hasCompactSupport_logMaxDiv g.val.2 hδ).comp_homeomorph (Homeomorph.neg ℝ))
    (fun s => logMaxDiv_nonneg g.val.2 hδ (-s)) (T := T) hκ
  have hΦ_cont : ContinuousAt Φ (((1 - 2 * (0 : ℝ)) * θ + (0 : ℝ) : ℝ) : ℂ) := by
    simpa using (differentiableOn_holoPotential g hδ).continuousOn.continuousAt
      ((isOpen_Ioo.preimage continuous_re).mem_nhds hθstrip)
  have hcomp : ContinuousAt (fun ε : ℝ => Φ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)) 0 :=
    ContinuousAt.comp (g := Φ) (f := fun ε : ℝ => (((1 - 2 * ε) * θ + ε : ℝ) : ℂ))
      hΦ_cont ((by fun_prop : Continuous fun ε : ℝ => (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).continuousAt)
  have htend_ε : Tendsto
      (fun ε : ℝ => Real.exp κ * Real.exp ((Φ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re))
      (𝓝[>] 0) (𝓝 (Real.exp κ * Real.exp (Φ θ).re)) := by
    simpa [Function.comp_def] using
      (((Real.continuous_exp.tendsto _).comp ((Complex.continuous_re.tendsto _).comp hcomp.tendsto))
        |>.const_mul (Real.exp κ)).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend_ε ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min (lt_min hε₀ hε₁) (by norm_num : (0 : ℝ) < 4⁻¹))]
    with ε hε
  exact norm_mk_le_exp_re_contracted_holoPotential hθ hδ hκ ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
    g (fun s hs => hg₀ s ((le_max_left _ _).trans hs))
    (fun s hs => hg₁ s ((le_max_right _ _).trans hs))
    (happrox₀ ε ⟨hε.1, hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩)
    (happrox₁ ε ⟨hε.1, hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))⟩)

private theorem integral_log_max_eq {E : Type*} [NormedAddCommGroup E] (f : C₀(ℝ, E)) {δ : ℝ}
    (hδ : 0 < δ) {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_int : Integrable w) :
    (∫ s, Real.log δ * w s) + (∫ s, logMaxDiv f δ s * w s) =
      ∫ s, Real.log (max ‖f s‖ δ) * w s := by
  rw [← integral_add (f := fun s => Real.log δ * w s) (g := fun s => logMaxDiv f δ s * w s)
    (hw_int.const_mul _) (((continuous_logMaxDiv f hδ).mul hw_cont).integrable_of_hasCompactSupport
      (hasCompactSupport_logMaxDiv f hδ).mul_right)]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  dsimp only; rw [← add_mul, log_add_logMaxDiv f hδ]

private theorem norm_mk_le_exp_integral_log_max_of_pos {θ δ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hδ : 0 < δ) (g : C.stripTraces) :
    ‖mk θ g‖ ≤ Real.exp
      ((∫ s, Real.log (max ‖g.val.1 s‖ δ) * stripPoisson₀ θ s) +
        ∫ s, Real.log (max ‖g.val.2 s‖ δ) * stripPoisson₁ θ s) := by
  refine (norm_mk_le_exp_re_holoPotential hθ hδ g).trans_eq (congrArg Real.exp ?_)
  have hlogδ : Real.log δ =
      (∫ s, Real.log δ * stripPoisson₀ θ s) + ∫ s, Real.log δ * stripPoisson₁ θ s := by
    rw [integral_const_mul, integral_const_mul, integral_stripPoisson₀ ⟨hθ.1, hθ.2.le⟩,
      integral_stripPoisson₁ ⟨hθ.1.le, hθ.2⟩]; ring
  linarith [integral_log_max_eq g.val.1 hδ (continuous_stripPoisson₀ θ)
      (integrable_stripPoisson₀ θ),
    integral_log_max_eq g.val.2 hδ (continuous_stripPoisson₁ θ) (integrable_stripPoisson₁ θ)]

private theorem exp_integral_log_mul_le_rpow {φ w : ℝ → ℝ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hw_int : Integrable w) (hw_nonneg : ∀ s, 0 ≤ w s) (hw_sum : ∫ s, w s = α)
    (hφ_ge : ∀ s, δ ≤ φ s) (hφ_int : Integrable (fun s => φ s * w s))
    (hlog_int : Integrable (fun s => Real.log (φ s) * w s)) :
    Real.exp (∫ s, Real.log (φ s) * w s) ≤ (α⁻¹ * ∫ s, φ s * w s) ^ α := by
  let I := α⁻¹ * ∫ s, φ s * w s
  have hI_pos : 0 < I := by
    have hle := integral_mono (hw_int.const_mul δ) hφ_int fun s =>
      mul_le_mul_of_nonneg_right (hφ_ge s) (hw_nonneg s)
    rw [integral_const_mul, hw_sum] at hle
    exact hδ.trans_le ((show δ = α⁻¹ * (δ * α) by field_simp [hα.ne']).trans_le
      (mul_le_mul_of_nonneg_left hle (inv_pos.2 hα).le))
  have hpt (s : ℝ) :
      Real.log (φ s) * w s + (1 - Real.log I) * w s ≤ I⁻¹ * (φ s * w s) := by
    have h1 := Real.add_one_le_exp (Real.log (φ s) - Real.log I)
    rw [Real.exp_sub, Real.exp_log (hδ.trans_le (hφ_ge s)), Real.exp_log hI_pos] at h1
    nlinarith [hw_nonneg s, div_eq_mul_inv (φ s) I]
  have hint := integral_mono (f := fun s => Real.log (φ s) * w s + (1 - Real.log I) * w s)
    (hlog_int.add (hw_int.const_mul (1 - Real.log I))) (hφ_int.const_mul I⁻¹) hpt
  rw [integral_add (f := fun s => Real.log (φ s) * w s) (g := fun s => (1 - Real.log I) * w s)
    hlog_int (hw_int.const_mul _), integral_const_mul, integral_const_mul, hw_sum] at hint
  have hI_cancel : I⁻¹ * ∫ s, φ s * w s = α := by
    have hdef : ∫ s, φ s * w s = α * I := by dsimp [I]; field_simp [hα.ne']
    rw [hdef]; field_simp [hI_pos.ne']
  rw [hI_cancel] at hint
  rw [Real.rpow_def_of_pos hI_pos, mul_comm (Real.log I) α]
  exact Real.exp_le_exp.2 (by linarith)

private theorem exp_integral_log_max_le_rpow {E : Type*} [NormedAddCommGroup E] (f : C₀(ℝ, E))
    {w : ℝ → ℝ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hw_int : Integrable w)
    (hw_nonneg : ∀ s, 0 ≤ w s) (hw_sum : ∫ s, w s = α) :
    Real.exp (∫ s, Real.log (max ‖f s‖ δ) * w s) ≤
      (α⁻¹ * (∫ s, ‖f s‖ * w s) + δ) ^ α := by
  have hf_int : Integrable (fun s => ‖f s‖ * w s) :=
    hw_int.bdd_mul (map_continuous f).norm.aestronglyMeasurable (ae_of_all _ fun s => by
      simpa [Real.norm_of_nonneg (norm_nonneg _)] using
        ZeroAtInftyContinuousMap.norm_coe_le_norm f s)
  have hmax_int : Integrable (fun s => max ‖f s‖ δ * w s) :=
    hw_int.bdd_mul ((map_continuous f).norm.max continuous_const).aestronglyMeasurable
      (ae_of_all _ fun s => by
        rw [Real.norm_of_nonneg (hδ.le.trans (le_max_right _ _))]
        exact max_le_max (ZeroAtInftyContinuousMap.norm_coe_le_norm f s) le_rfl)
  have hlog_int : Integrable (fun s => Real.log (max ‖f s‖ δ) * w s) :=
    hw_int.bdd_mul (Continuous.log ((map_continuous f).norm.max continuous_const) fun _ =>
        (hδ.trans_le (le_max_right _ _)).ne').aestronglyMeasurable
      (ae_of_all _ fun s => abs_le.2 ⟨by
        linarith [Real.log_le_log hδ (le_max_right ‖f s‖ δ), neg_abs_le (Real.log δ),
          le_max_left |Real.log δ| |Real.log (max ‖f‖ δ)|],
        (Real.log_le_log (hδ.trans_le (le_max_right _ _))
          (max_le_max (ZeroAtInftyContinuousMap.norm_coe_le_norm f s) le_rfl)).trans
          ((le_abs_self _).trans (le_max_right _ _))⟩)
  refine (exp_integral_log_mul_le_rpow hα hδ hw_int hw_nonneg hw_sum
    (fun _ => le_max_right _ _) hmax_int hlog_int).trans (Real.rpow_le_rpow
    (mul_nonneg (inv_pos.2 hα).le (integral_nonneg fun s =>
      mul_nonneg (hδ.le.trans (le_max_right _ _)) (hw_nonneg s))) ?_ hα.le)
  have hle : ∫ s, max ‖f s‖ δ * w s ≤ (∫ s, ‖f s‖ * w s) + δ * α := by
    rw [← hw_sum, ← integral_const_mul, ← integral_add hf_int (hw_int.const_mul δ)]
    exact integral_mono hmax_int (hf_int.add (hw_int.const_mul δ)) fun s =>
      (mul_le_mul_of_nonneg_right
        (max_le (le_add_of_nonneg_right hδ.le) (le_add_of_nonneg_left (norm_nonneg _)))
        (hw_nonneg s)).trans_eq (add_mul _ _ _)
  exact (mul_le_mul_of_nonneg_left hle (inv_pos.2 hα).le).trans_eq (by field_simp [hα.ne'])

/-- **Bergh–Löfström Lemma 4.3.2 (Stieltjes/Poisson log-convexity of the complex method norm).**
For `0 < θ < 1` and any admissible trace pair `g = (g₀, g₁)`, the quotient norm in `[X₀, X₁]_θ` is
bounded by the weighted geometric mean of the strip Poisson integrals of `‖g₀‖` and `‖g₁‖`. -/
theorem norm_mk_le_integral_stripPoisson {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (g : C.stripTraces) :
    ‖mk θ g‖ ≤
      ((1 - θ)⁻¹ * ∫ t, ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t‖ * stripPoisson₀ θ t) ^ (1 - θ) *
        (θ⁻¹ * ∫ t, ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t‖ * stripPoisson₁ θ t) ^ θ := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  let I₀ := (1 - θ)⁻¹ * ∫ t, ‖g.val.1 t‖ * stripPoisson₀ θ t
  let I₁ := θ⁻¹ * ∫ t, ‖g.val.2 t‖ * stripPoisson₁ θ t
  have hadd (a : ℝ) : Tendsto (fun δ : ℝ => a + δ) (𝓝[>] 0) (𝓝 a) := by
    simpa using ((by fun_prop : Continuous fun δ : ℝ => a + δ).tendsto 0)
      |>.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto
    (((hadd I₀).rpow_const (Or.inr h1θ.le)).mul ((hadd I₁).rpow_const (Or.inr hθ.1.le))) ?_
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  have hI₀ : 0 ≤ I₀ + δ := add_nonneg (mul_nonneg (inv_pos.2 h1θ).le
    (integral_nonneg fun s => mul_nonneg (norm_nonneg _) (stripPoisson₀_pos hθ s).le)) hδ.le
  refine (norm_mk_le_exp_integral_log_max_of_pos hθ hδ g).trans
    ((Real.exp_add _ _).trans_le (mul_le_mul
      (exp_integral_log_max_le_rpow g.val.1 h1θ hδ (integrable_stripPoisson₀ θ)
        (fun s => (stripPoisson₀_pos hθ s).le) (integral_stripPoisson₀ ⟨hθ.1, hθ.2.le⟩))
      (exp_integral_log_max_le_rpow g.val.2 hθ.1 hδ (integrable_stripPoisson₁ θ)
        (fun s => (stripPoisson₁_pos hθ s).le) (integral_stripPoisson₁ ⟨hθ.1.le, hθ.2⟩))
      (Real.exp_nonneg _) (Real.rpow_nonneg hI₀ _)))

private theorem weighted_integral_rpow_le {E : Type*} [NormedAddCommGroup E] (f : C₀(ℝ, E))
    {w : ℝ → ℝ} {α : ℝ} (hα : 0 < α) (hw_int : Integrable w) (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_sum : ∫ t, w t = α) : (α⁻¹ * ∫ t, ‖f t‖ * w t) ^ α ≤ ‖f‖ ^ α := by
  have hle : ∫ t, ‖f t‖ * w t ≤ ∫ t, ‖f‖ * w t :=
    integral_mono_of_nonneg (ae_of_all _ fun t => mul_nonneg (norm_nonneg _) (hw_nonneg t))
      (hw_int.const_mul ‖f‖) (ae_of_all _ fun t => mul_le_mul_of_nonneg_right
        (ZeroAtInftyContinuousMap.norm_coe_le_norm f t) (hw_nonneg t))
  rw [integral_const_mul, hw_sum] at hle
  exact Real.rpow_le_rpow (mul_nonneg (inv_pos.2 hα).le
      (integral_nonneg fun t => mul_nonneg (norm_nonneg _) (hw_nonneg t)))
    ((mul_le_mul_of_nonneg_left hle (inv_pos.2 hα).le).trans_eq (by field_simp [hα.ne'])) hα.le

/-- **Three-lines bound in `[X₀, X₁]_θ`.** For every real `θ` and admissible trace pair
`g = (g₀, g₁)`, the complex interpolation norm satisfies
`‖mk θ g‖ ≤ ‖g₀‖ ^ (1 - θ) * ‖g₁‖ ^ θ`. -/
theorem norm_mk_le_rpow_mul_rpow (θ : ℝ) (g : C.stripTraces) :
    ‖mk θ g‖ ≤
      ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1‖ ^ (1 - θ) * ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2‖ ^ θ := by
  by_cases hθ : θ ∈ Icc 0 1
  · rcases eq_or_lt_of_le hθ.1 with rfl | hθ0
    · simpa [norm_mk_zero] using ZeroAtInftyContinuousMap.norm_coe_le_norm _ 0
    rcases eq_or_lt_of_le hθ.2 with rfl | hθ1
    · simpa [norm_mk_one] using ZeroAtInftyContinuousMap.norm_coe_le_norm _ 0
    have hθoo : θ ∈ Ioo 0 1 := ⟨hθ0, hθ1⟩
    have h1θ : 0 < 1 - θ := sub_pos.2 hθ1
    refine (norm_mk_le_integral_stripPoisson hθoo g).trans (mul_le_mul
      (weighted_integral_rpow_le g.val.1 h1θ (integrable_stripPoisson₀ θ)
        (fun t => (stripPoisson₀_pos hθoo t).le) (integral_stripPoisson₀ ⟨hθ0, hθ1.le⟩))
      (weighted_integral_rpow_le g.val.2 hθ0 (integrable_stripPoisson₁ θ)
        (fun t => (stripPoisson₁_pos hθoo t).le) (integral_stripPoisson₁ ⟨hθ0.le, hθ1⟩))
      (Real.rpow_nonneg (mul_nonneg (inv_pos.2 hθ0).le
        (integral_nonneg fun t => mul_nonneg (norm_nonneg _) (stripPoisson₁_pos hθoo t).le)) _)
      (Real.rpow_nonneg (norm_nonneg _) _))
  · rw [eq_zero_of_notMem hθ (mk θ g), norm_zero]; positivity

end ComplexMethodSpace

end CompatibleCouple

end TauCeti
