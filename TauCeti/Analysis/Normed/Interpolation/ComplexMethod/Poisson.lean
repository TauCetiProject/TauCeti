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

On the vertical strip `0 ≤ re z ≤ 1`, harmonic functions bounded up to the boundary are
reconstructed from their boundary values on `re z = 0` and `re z = 1` by the two strip Poisson
kernels

* `TauCeti.stripPoisson₀ θ t = sin (π θ) / (2 (cosh (π t) - cos (π θ)))`, of total integral `1 - θ`
  for `0 < θ ≤ 1` (`TauCeti.integral_stripPoisson₀`);
* `TauCeti.stripPoisson₁ θ t = sin (π θ) / (2 (cosh (π t) + cos (π θ)))`, of total integral `θ`
  for `0 ≤ θ < 1` (`TauCeti.integral_stripPoisson₁`).

Multiplying an admissible strip function `F` by `exp (-Φ ((1 - 2 ε) z + ε))`, where `Φ` is the
holomorphic strip potential of compactly supported logarithmic upper envelopes of the boundary trace
norms, and applying Jensen's inequality to the normalized Poisson densities yields Bergh–Löfström's
fundamental Stieltjes/Poisson estimate for Calderón's complex method:

* `CompatibleCouple.ComplexMethodSpace.norm_mk_le_integral_stripPoisson`: for `0 < θ < 1` and
  `g ∈ stripTraces`,
  `‖mk θ g‖ ≤ ((1 - θ)⁻¹ ∫ ‖g₀ t‖ P₀(θ, t) dt) ^ (1 - θ) * (θ⁻¹ ∫ ‖g₁ t‖ P₁(θ, t) dt) ^ θ`.
* `CompatibleCouple.ComplexMethodSpace.norm_mk_le_rpow_mul_rpow`: the multiplicative three-lines
  bound `‖mk θ g‖ ≤ ‖g₀‖ ^ (1 - θ) * ‖g₁‖ ^ θ` in `[X₀, X₁]_θ`, valid for every real `θ`.
* `CompatibleCouple.ComplexMethodSpace.norm_mk_zero` and
  `CompatibleCouple.ComplexMethodSpace.norm_mk_one`: at the endpoints `θ = 0` and `θ = 1`, the
  quotient norm of an admissible trace is the norm of its value at `0` in `X₀` or `X₁`.
* `CompatibleCouple.ComplexMethodSpace.exists_stripTraces_smul_of_diffContOnCl`: multiplying an
  admissible trace by a bounded strip-analytic scalar `c` multiplies `mk θ g` by `c θ`.

Unlike coordinatewise Hahn–Banach functionals, the Poisson weights `stripPoisson₀ θ` and
`stripPoisson₁ θ` depend only on `(θ, t)` and not on the couple `(X₀, X₁)` or the trace `g`. This
uniformity is what makes vector-valued `Lᵖ` and `ℓ^q` complex interpolation work without
completeness or duality assumptions on the endpoints.

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
  have h1 : π * (1 - θ) = π - π * θ := by ring
  rw [stripPoisson₀, stripPoisson₁, h1, Real.sin_pi_sub, Real.cos_pi_sub, sub_neg_eq_add]

/-- Reflecting `θ ↦ 1 - θ` exchanges the two strip Poisson kernels. -/
theorem stripPoisson₁_one_sub (θ t : ℝ) : stripPoisson₁ (1 - θ) t = stripPoisson₀ θ t := by
  simpa using (stripPoisson₀_one_sub (1 - θ) t).symm

@[simp]
theorem stripPoisson₀_zero (t : ℝ) : stripPoisson₀ 0 t = 0 := by
  simp [stripPoisson₀]

@[simp]
theorem stripPoisson₀_one (t : ℝ) : stripPoisson₀ 1 t = 0 := by
  simp [stripPoisson₀]

@[simp]
theorem stripPoisson₁_zero (t : ℝ) : stripPoisson₁ 0 t = 0 := by
  simp [stripPoisson₁]

@[simp]
theorem stripPoisson₁_one (t : ℝ) : stripPoisson₁ 1 t = 0 := by
  simp [stripPoisson₁]

private theorem abs_cos_lt_one_of_sin_ne_zero {x : ℝ} (h : Real.sin x ≠ 0) : |Real.cos x| < 1 := by
  have hsq : Real.cos x ^ 2 < 1 := by
    have hpos : 0 < Real.sin x ^ 2 := sq_pos_of_ne_zero h
    nlinarith [Real.sin_sq_add_cos_sq x]
  simpa [sq_lt_one_iff_abs_lt_one] using hsq

private theorem one_sub_abs_cos_mul_cosh_le {θ : ℝ} (t : ℝ) :
    (1 - |Real.cos (π * θ)|) * Real.cosh (π * t) ≤ Real.cosh (π * t) - Real.cos (π * θ) := by
  have h1 : 1 ≤ Real.cosh (π * t) := Real.one_le_cosh _
  have h2 : Real.cos (π * θ) ≤ |Real.cos (π * θ)| := le_abs_self _
  have h3 : 0 ≤ |Real.cos (π * θ)| * (Real.cosh (π * t) - 1) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.2 h1)
  linarith

private theorem cosh_sub_cos_pos_of_sin_ne_zero {θ : ℝ} (h : Real.sin (π * θ) ≠ 0) (t : ℝ) :
    0 < Real.cosh (π * t) - Real.cos (π * θ) := by
  have hlt : |Real.cos (π * θ)| < 1 := abs_cos_lt_one_of_sin_ne_zero h
  exact lt_of_lt_of_le (mul_pos (sub_pos.2 hlt) (Real.cosh_pos _)) (one_sub_abs_cos_mul_cosh_le t)

/-- On the open interval `0 < θ < 1`, the left strip Poisson kernel is strictly positive. -/
theorem stripPoisson₀_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) : 0 < stripPoisson₀ θ t := by
  have hsin : 0 < Real.sin (π * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (mul_lt_of_lt_one_right pi_pos hθ.2)
  exact div_pos hsin (mul_pos zero_lt_two (cosh_sub_cos_pos_of_sin_ne_zero hsin.ne' t))

/-- On the open interval `0 < θ < 1`, the right strip Poisson kernel is strictly positive. -/
theorem stripPoisson₁_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) : 0 < stripPoisson₁ θ t := by
  rw [← stripPoisson₀_one_sub]
  exact stripPoisson₀_pos ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩ t

/-- On the closed interval `0 ≤ θ ≤ 1`, the left strip Poisson kernel is nonnegative. -/
theorem stripPoisson₀_nonneg {θ : ℝ} (hθ : θ ∈ Icc 0 1) (t : ℝ) : 0 ≤ stripPoisson₀ θ t := by
  rcases eq_or_lt_of_le hθ.1 with rfl | h0
  · simp
  · rcases eq_or_lt_of_le hθ.2 with rfl | h1
    · simp
    · exact (stripPoisson₀_pos ⟨h0, h1⟩ t).le

/-- On the closed interval `0 ≤ θ ≤ 1`, the right strip Poisson kernel is nonnegative. -/
theorem stripPoisson₁_nonneg {θ : ℝ} (hθ : θ ∈ Icc 0 1) (t : ℝ) : 0 ≤ stripPoisson₁ θ t := by
  rw [← stripPoisson₀_one_sub]
  exact stripPoisson₀_nonneg ⟨sub_nonneg.2 hθ.2, sub_le_self 1 hθ.1⟩ t

/-- For every real `θ`, `t ↦ stripPoisson₀ θ t` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_stripPoisson₀ (θ : ℝ) : Continuous (stripPoisson₀ θ) := by
  by_cases h : Real.sin (π * θ) = 0
  · have hzero : stripPoisson₀ θ = 0 := by ext t; simp [stripPoisson₀, h]
    rw [hzero]
    exact continuous_const
  · refine Continuous.div continuous_const (by fun_prop) fun t => ?_
    exact (mul_pos zero_lt_two (cosh_sub_cos_pos_of_sin_ne_zero h t)).ne'

/-- For every real `θ`, `t ↦ stripPoisson₁ θ t` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_stripPoisson₁ (θ : ℝ) : Continuous (stripPoisson₁ θ) := by
  have heq : stripPoisson₁ θ = stripPoisson₀ (1 - θ) :=
    funext fun t => (stripPoisson₀_one_sub θ t).symm
  rw [heq]
  exact continuous_stripPoisson₀ (1 - θ)

private theorem two_mul_cosh_sub_cos_eq (θ t : ℝ) :
    2 * (Real.cosh (π * t) - Real.cos (π * θ)) =
      Real.exp (-(π * t)) * ((Real.exp (π * t) - Real.cos (π * θ)) ^ 2 + Real.sin (π * θ) ^ 2) := by
  rw [Real.cosh_eq]
  have hexp : Real.exp (-(π * t)) * Real.exp (π * t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hsq : Real.cos (π * θ) ^ 2 + Real.sin (π * θ) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  calc 2 * ((Real.exp (π * t) + Real.exp (-(π * t))) / 2 - Real.cos (π * θ))
      = Real.exp (π * t) + Real.exp (-(π * t)) - 2 * Real.cos (π * θ) := by ring
    _ = Real.exp (-(π * t)) * (Real.exp (π * t) ^ 2 - 2 * Real.cos (π * θ) * Real.exp (π * t) +
          (Real.cos (π * θ) ^ 2 + Real.sin (π * θ) ^ 2)) := by
        rw [hsq]
        linear_combination (-(Real.exp (π * t) - 2 * Real.cos (π * θ))) * hexp
    _ = Real.exp (-(π * t)) *
          ((Real.exp (π * t) - Real.cos (π * θ)) ^ 2 + Real.sin (π * θ) ^ 2) := by ring

private theorem hasDerivAt_stripPoisson₀_primitive {θ : ℝ} (hsin : Real.sin (π * θ) ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun s => π⁻¹ * Real.arctan ((Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ)))
      (stripPoisson₀ θ t) t := by
  have hlin : HasDerivAt (fun s => (Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ))
      (π * Real.exp (π * t) / Real.sin (π * θ)) t := by
    have h1 := ((hasDerivAt_id t).const_mul π).exp.sub_const (Real.cos (π * θ))
    simpa [mul_comm] using h1.div_const (Real.sin (π * θ))
  have harc := ((Real.hasDerivAt_arctan _).comp t hlin).const_mul π⁻¹
  refine harc.congr_deriv ?_
  rw [stripPoisson₀, two_mul_cosh_sub_cos_eq, Real.exp_neg]
  have hpi : π ≠ 0 := pi_ne_zero
  have hexp : Real.exp (π * t) ≠ 0 := (Real.exp_pos _).ne'
  have hden : (Real.exp (π * t) - Real.cos (π * θ)) ^ 2 + Real.sin (π * θ) ^ 2 ≠ 0 := by
    positivity
  field_simp
  ring

private theorem integrable_exp_neg_pi_mul_abs :
    Integrable (fun t : ℝ => Real.exp (-(π * |t|))) := by
  have hIoi : IntegrableOn (fun t : ℝ => Real.exp (-(π * |t|))) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 pi_pos).congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    rw [abs_of_pos (mem_Ioi.1 ht), neg_mul]
  have hIic : IntegrableOn (fun t : ℝ => Real.exp (-(π * |t|))) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    change IntegrableOn _ _ (Measure.map (Homeomorph.neg ℝ) volume)
    rw [(Homeomorph.neg ℝ).measurableEmbedding.integrableOn_map_iff]
    change IntegrableOn (fun t : ℝ => Real.exp (-(π * |-t|))) (Neg.neg ⁻¹' Iic 0) volume
    simp only [abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hIoi
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

/-- For every real `θ`, the left strip Poisson kernel is integrable on `ℝ`. -/
theorem integrable_stripPoisson₀ (θ : ℝ) : Integrable (stripPoisson₀ θ) := by
  by_cases hsin : Real.sin (π * θ) = 0
  · have hzero : stripPoisson₀ θ = 0 := by ext t; simp [stripPoisson₀, hsin]
    rw [hzero]
    exact integrable_zero _ _ _
  · have hc : 0 < 1 - |Real.cos (π * θ)| := sub_pos.2 (abs_cos_lt_one_of_sin_ne_zero hsin)
    refine (integrable_exp_neg_pi_mul_abs.const_mul
      (|Real.sin (π * θ)| / (1 - |Real.cos (π * θ)|))).mono'
      (continuous_stripPoisson₀ θ).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    have hcosh : Real.exp (π * |t|) / 2 ≤ Real.cosh (π * t) := by
      rcases le_total 0 t with ht | ht
      · rw [abs_of_nonneg ht, Real.cosh_eq]
        linarith [Real.exp_pos (-(π * t))]
      · rw [abs_of_nonpos ht, mul_neg, Real.cosh_eq]
        linarith [Real.exp_pos (π * t)]
    have hden : (1 - |Real.cos (π * θ)|) * Real.exp (π * |t|) ≤
        2 * (Real.cosh (π * t) - Real.cos (π * θ)) := by
      nlinarith [one_sub_abs_cos_mul_cosh_le (θ := θ) t, hcosh]
    calc ‖stripPoisson₀ θ t‖
        = |Real.sin (π * θ)| / (2 * (Real.cosh (π * t) - Real.cos (π * θ))) := by
          rw [Real.norm_eq_abs, stripPoisson₀, abs_div,
            abs_of_pos (mul_pos zero_lt_two (cosh_sub_cos_pos_of_sin_ne_zero hsin t))]
      _ ≤ |Real.sin (π * θ)| / ((1 - |Real.cos (π * θ)|) * Real.exp (π * |t|)) :=
          div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hc (Real.exp_pos _)) hden
      _ = |Real.sin (π * θ)| / (1 - |Real.cos (π * θ)|) * Real.exp (-(π * |t|)) := by
          rw [Real.exp_neg]
          field_simp [hc.ne']

/-- For every real `θ`, the right strip Poisson kernel is integrable on `ℝ`. -/
theorem integrable_stripPoisson₁ (θ : ℝ) : Integrable (stripPoisson₁ θ) := by
  have heq : stripPoisson₁ θ = stripPoisson₀ (1 - θ) :=
    funext fun t => (stripPoisson₀_one_sub θ t).symm
  rw [heq]
  exact integrable_stripPoisson₀ (1 - θ)

/-- For `0 < θ ≤ 1`, the left strip Poisson kernel has total integral `1 - θ` on `ℝ`. -/
theorem integral_stripPoisson₀ {θ : ℝ} (hθ : θ ∈ Ioc 0 1) :
    ∫ t, stripPoisson₀ θ t = 1 - θ := by
  rcases eq_or_lt_of_le hθ.2 with rfl | h1
  · simp
  have hsin : 0 < Real.sin (π * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (mul_lt_of_lt_one_right pi_pos h1)
  have htop : Tendsto
      (fun s => π⁻¹ * Real.arctan ((Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ)))
      atTop (𝓝 (2⁻¹ : ℝ)) := by
    have h1' : Tendsto (fun s => (Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ))
        atTop atTop :=
      ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop pi_pos)).atTop_add
        tendsto_const_nhds).atTop_div_const hsin
    have h2' : π⁻¹ * (π / 2) = (2⁻¹ : ℝ) := by field_simp [pi_ne_zero]
    rw [← h2']
    exact ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1').const_mul π⁻¹
  have hbot : Tendsto
      (fun s => π⁻¹ * Real.arctan ((Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ)))
      atBot (𝓝 (θ - 2⁻¹)) := by
    have hexp0 : Tendsto (fun s => Real.exp (π * s)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot pi_pos)
    have hlim : Tendsto
        (fun s => π⁻¹ * Real.arctan ((Real.exp (π * s) - Real.cos (π * θ)) / Real.sin (π * θ)))
        atBot (𝓝 (π⁻¹ * Real.arctan ((0 - Real.cos (π * θ)) / Real.sin (π * θ)))) :=
      ((Real.continuous_arctan.tendsto _).comp ((hexp0.sub_const _).div_const _)).const_mul π⁻¹
    have htan : (0 - Real.cos (π * θ)) / Real.sin (π * θ) = Real.tan (π * θ - π / 2) := by
      rw [zero_sub, Real.tan_eq_sin_div_cos, Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two]
    have harctan : Real.arctan (Real.tan (π * θ - π / 2)) = π * θ - π / 2 :=
      Real.arctan_tan (by nlinarith [pi_pos, hθ.1]) (by nlinarith [pi_pos, h1])
    have hval : π⁻¹ * Real.arctan ((0 - Real.cos (π * θ)) / Real.sin (π * θ)) = θ - 2⁻¹ := by
      rw [htan, harctan]
      field_simp [pi_ne_zero]
    rwa [hval] at hlim
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_stripPoisson₀_primitive hsin.ne')
    (integrable_stripPoisson₀ θ) hbot htop]
  ring

/-- For `0 ≤ θ < 1`, the right strip Poisson kernel has total integral `θ` on `ℝ`. -/
theorem integral_stripPoisson₁ {θ : ℝ} (hθ : θ ∈ Ico 0 1) :
    ∫ t, stripPoisson₁ θ t = θ := by
  have heq : stripPoisson₁ θ = stripPoisson₀ (1 - θ) :=
    funext fun t => (stripPoisson₀_one_sub θ t).symm
  rw [heq, integral_stripPoisson₀ ⟨sub_pos.2 hθ.2, sub_le_self 1 hθ.1⟩]
  ring

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
  rw [harg, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  push_cast
  ring

private theorem normSq_one_add_exp_I_pi_mul (ζ : ℂ) :
    Complex.normSq (1 + Complex.exp (I * π * ζ)) =
      (Real.exp (-(π * ζ.im)) + Real.cos (π * ζ.re)) ^ 2 + Real.sin (π * ζ.re) ^ 2 := by
  rw [one_add_exp_I_pi_mul_eq, Complex.normSq_add_mul_I]
  have hsq := Real.cos_sq_add_sin_sq (π * ζ.re)
  linear_combination (Real.exp (-(π * ζ.im)) ^ 2 - 1) * hsq

private theorem normSq_one_add_exp_eq_two_mul_cosh_add_cos (ζ : ℂ) :
    Complex.normSq (1 + Complex.exp (I * π * ζ)) =
      2 * Real.exp (-(π * ζ.im)) * (Real.cosh (π * ζ.im) + Real.cos (π * ζ.re)) := by
  rw [normSq_one_add_exp_I_pi_mul, Real.cosh_eq]
  have hexp : Real.exp (-(π * ζ.im)) * Real.exp (π * ζ.im) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hsq := Real.cos_sq_add_sin_sq (π * ζ.re)
  linear_combination hsq - hexp

private theorem sin_le_norm_one_add_exp {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    Real.sin (π * ζ.re) ≤ ‖1 + Complex.exp (I * π * ζ)‖ := by
  have hsin : 0 < Real.sin (π * ζ.re) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hζ.1) (mul_lt_of_lt_one_right pi_pos hζ.2)
  rw [Complex.norm_def, ← Real.sqrt_sq hsin.le]
  apply Real.sqrt_le_sqrt
  rw [normSq_one_add_exp_I_pi_mul]
  linarith [sq_nonneg (Real.exp (-(π * ζ.im)) + Real.cos (π * ζ.re))]

private theorem one_add_exp_ne_zero {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    1 + Complex.exp (I * π * ζ) ≠ 0 := by
  have hsin : 0 < Real.sin (π * ζ.re) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hζ.1) (mul_lt_of_lt_one_right pi_pos hζ.2)
  exact norm_pos_iff.1 (hsin.trans_le (sin_le_norm_one_add_exp hζ))

private theorem re_holoPoisson₁ (ζ : ℂ) :
    (holoPoisson₁ ζ).re = stripPoisson₁ ζ.re ζ.im := by
  rw [holoPoisson₁, Complex.div_re, normSq_one_add_exp_eq_two_mul_cosh_add_cos,
    one_add_exp_I_pi_mul_eq]
  simp only [I_re, zero_mul, zero_div, I_im, one_mul, mul_one, zero_add, add_zero, add_im,
    ofReal_im, mul_im, ofReal_re]
  rw [stripPoisson₁]
  field_simp [(Real.exp_pos (-(π * ζ.im))).ne']

private theorem re_holoPoisson₀ (ζ : ℂ) :
    (holoPoisson₀ ζ).re = stripPoisson₀ ζ.re ζ.im := by
  rw [holoPoisson₀, re_holoPoisson₁, sub_re, one_re, sub_im, one_im, zero_sub,
    stripPoisson₁_neg, stripPoisson₁_one_sub]

private theorem hasDerivAt_holoPoisson₁ {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    HasDerivAt holoPoisson₁
      (π * Complex.exp (I * π * ζ) / (1 + Complex.exp (I * π * ζ)) ^ 2) ζ := by
  have h1 : HasDerivAt (fun w : ℂ => 1 + Complex.exp (I * π * w))
      (Complex.exp (I * π * ζ) * (I * π)) ζ := by
    simpa using (((hasDerivAt_id ζ).const_mul (I * π)).cexp).const_add 1
  have h2 := (hasDerivAt_const ζ I).div h1 (one_add_exp_ne_zero hζ)
  refine h2.congr_deriv ?_
  have hI : I * I = -1 := I_mul_I
  calc (0 * (1 + Complex.exp (I * π * ζ)) - I * (Complex.exp (I * π * ζ) * (I * π))) /
        (1 + Complex.exp (I * π * ζ)) ^ 2
      = (-(I * I) * π * Complex.exp (I * π * ζ)) / (1 + Complex.exp (I * π * ζ)) ^ 2 := by ring
    _ = π * Complex.exp (I * π * ζ) / (1 + Complex.exp (I * π * ζ)) ^ 2 := by
        rw [hI]
        ring

private theorem norm_deriv_holoPoisson₁_le {a b : ℝ} (ha : 0 < a) (hb : b < 1) {ζ : ℂ}
    (hζ : ζ.re ∈ Icc a b) :
    ‖(π : ℂ) * Complex.exp (I * π * ζ) / (1 + Complex.exp (I * π * ζ)) ^ 2‖ ≤
      π / (2 * (1 + Real.cos (π * b))) := by
  have hb_pos : 0 < b := ha.trans_le (hζ.1.trans hζ.2)
  have hcosb : 0 < 1 + Real.cos (π * b) := by
    have hlt : |Real.cos (π * b)| < 1 := abs_cos_lt_one_of_sin_ne_zero
      (Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hb_pos) (mul_lt_of_lt_one_right pi_pos hb)).ne'
    linarith [neg_abs_le (Real.cos (π * b))]
  have hcos : Real.cos (π * b) ≤ Real.cos (π * ζ.re) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg pi_pos.le (ha.le.trans hζ.1))
      (mul_le_of_le_one_right pi_pos.le hb.le) (mul_le_mul_of_nonneg_left hζ.2 pi_pos.le)
  have hexp_norm : ‖Complex.exp (I * π * ζ)‖ = Real.exp (-(π * ζ.im)) := by
    have harg : (I * π * ζ).re = -(π * ζ.im) := by simp
    rw [Complex.norm_exp, harg]
  have hden : 2 * Real.exp (-(π * ζ.im)) * (1 + Real.cos (π * b)) ≤
      ‖1 + Complex.exp (I * π * ζ)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, normSq_one_add_exp_eq_two_mul_cosh_add_cos]
    have h1 : 1 ≤ Real.cosh (π * ζ.im) := Real.one_le_cosh _
    nlinarith [Real.exp_pos (-(π * ζ.im))]
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg pi_pos.le, norm_pow, hexp_norm]
  have hpos : 0 < 2 * Real.exp (-(π * ζ.im)) * (1 + Real.cos (π * b)) := by positivity
  calc π * Real.exp (-(π * ζ.im)) / ‖1 + Complex.exp (I * π * ζ)‖ ^ 2
      ≤ π * Real.exp (-(π * ζ.im)) / (2 * Real.exp (-(π * ζ.im)) * (1 + Real.cos (π * b))) :=
        div_le_div_of_nonneg_left (by positivity) hpos hden
    _ = π / (2 * (1 + Real.cos (π * b))) := by
        have hexp : Real.exp (-(π * ζ.im)) ≠ 0 := (Real.exp_pos _).ne'
        field_simp [hexp]

private theorem integrable_mul_holoPoisson₁ {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    Integrable (fun s : ℝ => (u s : ℂ) * holoPoisson₁ (ζ - s * I)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_
    ((hsupp.comp_left Complex.ofReal_zero).mul_right)
  refine (continuous_ofReal.comp hu).mul ?_
  unfold holoPoisson₁
  exact Continuous.div continuous_const (by fun_prop) fun _ =>
    one_add_exp_ne_zero ⟨by simpa using hζ.1, by simpa using hζ.2⟩

private theorem integrable_mul_holoPoisson₀ {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    Integrable (fun s : ℝ => (u s : ℂ) * holoPoisson₀ (ζ - s * I)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_
    ((hsupp.comp_left Complex.ofReal_zero).mul_right)
  refine (continuous_ofReal.comp hu).mul ?_
  unfold holoPoisson₀ holoPoisson₁
  exact Continuous.div continuous_const (by fun_prop) fun _ =>
    one_add_exp_ne_zero ⟨by simpa using sub_pos.2 hζ.2, by simpa using sub_lt_self 1 hζ.1⟩

private theorem differentiableOn_integral_holoPoisson₁ {u : ℝ → ℝ} (hu : Continuous u)
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
  have hmem_Icc {ζ : ℂ} (hζ : ζ ∈ ball ζ₀ r) (s : ℝ) : (ζ - s * I).re ∈ Icc a b := by
    have hre : |ζ.re - ζ₀.re| < r := (abs_re_le_norm (ζ - ζ₀)).trans_lt (mem_ball_iff_norm.1 hζ)
    simp only [sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      sub_zero, mem_Icc, a, b]
    grind [abs_lt]
  have huint : Integrable u := hu.integrable_of_hasCompactSupport hsupp
  let C := π / (2 * (1 + Real.cos (π * b)))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := ball ζ₀ r)
    (F := fun ζ (s : ℝ) => (u s : ℂ) * holoPoisson₁ (ζ - s * I))
    (F' := fun ζ (s : ℝ) => (u s : ℂ) *
      ((π : ℂ) * Complex.exp (I * π * (ζ - s * I)) / (1 + Complex.exp (I * π * (ζ - s * I))) ^ 2))
    (bound := fun s => |C| * ‖u s‖) (ball_mem_nhds ζ₀ hr) ?_
    (integrable_mul_holoPoisson₁ hu hsupp hζ₀) ?_ ?_
    (huint.norm.const_mul |C|) ?_).2.differentiableAt.differentiableWithinAt
  · filter_upwards [ball_mem_nhds ζ₀ hr] with ζ hζ
    refine Continuous.aestronglyMeasurable ((continuous_ofReal.comp hu).mul ?_)
    unfold holoPoisson₁
    exact Continuous.div continuous_const (by fun_prop) fun s =>
      one_add_exp_ne_zero ⟨ha.trans_le (hmem_Icc hζ s).1, (hmem_Icc hζ s).2.trans_lt hb⟩
  · refine Continuous.aestronglyMeasurable ((continuous_ofReal.comp hu).mul ?_)
    refine Continuous.div (by fun_prop) (by fun_prop) fun s =>
      pow_ne_zero 2 (one_add_exp_ne_zero
        ⟨ha.trans_le (hmem_Icc (mem_ball_self hr) s).1,
          (hmem_Icc (mem_ball_self hr) s).2.trans_lt hb⟩)
  · exact ae_of_all _ fun s ζ hζ => by
      rw [norm_mul, Complex.norm_real, mul_comm]
      exact mul_le_mul_of_nonneg_right
        ((norm_deriv_holoPoisson₁_le ha hb (hmem_Icc hζ s)).trans (le_abs_self C)) (norm_nonneg _)
  · exact ae_of_all _ fun s ζ hζ => by
      have hm := hmem_Icc hζ s
      have hsub : HasDerivAt (fun w : ℂ => w - s * I) 1 ζ := (hasDerivAt_id ζ).sub_const _
      simpa using ((hasDerivAt_holoPoisson₁ ⟨ha.trans_le hm.1, hm.2.trans_lt hb⟩).comp ζ
        hsub).const_mul (u s : ℂ)

private theorem differentiableOn_integral_holoPoisson₀ {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) :
    DifferentiableOn ℂ (fun ζ => ∫ s, (u s : ℂ) * holoPoisson₀ (ζ - s * I))
      (verticalStrip 0 1) := by
  have heq : (fun ζ => ∫ s, (u s : ℂ) * holoPoisson₀ (ζ - s * I)) =
      fun ζ => ∫ s, (u (-s) : ℂ) * holoPoisson₁ ((1 - ζ) - s * I) := by
    ext ζ
    rw [← MeasureTheory.integral_neg_eq_self
      (fun s : ℝ => (u s : ℂ) * holoPoisson₀ (ζ - s * I))]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    dsimp only
    have harg : 1 - (ζ - ((-s : ℝ) : ℂ) * I) = (1 - ζ) - (s : ℂ) * I := by push_cast; ring
    rw [holoPoisson₀, harg]
  rw [heq]
  have h1 : Differentiable ℂ (fun ζ : ℂ => 1 - ζ) := by fun_prop
  exact (differentiableOn_integral_holoPoisson₁ (hu.comp continuous_neg)
    (hsupp.comp_homeomorph (Homeomorph.neg ℝ))).comp h1.differentiableOn fun _ hζ =>
      one_sub_mem_verticalStrip_iff.2 hζ

private theorem re_integral_holoPoisson₁ {u : ℝ → ℝ} (hu : Continuous u)
    (hs : HasCompactSupport u) {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    (∫ s, (u s : ℂ) * holoPoisson₁ (ζ - s * I)).re =
      ∫ s, u s * stripPoisson₁ ζ.re (ζ.im - s) := by
  have hre := (Complex.reCLM.integral_comp_comm (integrable_mul_holoPoisson₁ hu hs hζ)).symm
  refine Eq.trans hre (integral_congr_ae (ae_of_all _ fun s => ?_))
  simp [re_holoPoisson₁]

private theorem re_integral_holoPoisson₀ {u : ℝ → ℝ} (hu : Continuous u)
    (hs : HasCompactSupport u) {ζ : ℂ} (hζ : ζ ∈ verticalStrip 0 1) :
    (∫ s, (u s : ℂ) * holoPoisson₀ (ζ - s * I)).re =
      ∫ s, u s * stripPoisson₀ ζ.re (ζ.im - s) := by
  have hre := (Complex.reCLM.integral_comp_comm (integrable_mul_holoPoisson₀ hu hs hζ)).symm
  refine Eq.trans hre (integral_congr_ae (ae_of_all _ fun s => ?_))
  simp [re_holoPoisson₀]

/-- For fixed `r > 0`, the mass `∫ y in (-r)..r, stripPoisson₀ ε y` converges to `1` as `ε → 0⁺`. -/
private theorem tendsto_intervalIntegral_stripPoisson₀_nhdsGT {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε => ∫ y in (-r)..r, stripPoisson₀ ε y) (𝓝[>] 0) (𝓝 1) := by
  have hsin_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < Real.sin (π * ε) := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    exact Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hε.1) (mul_lt_of_lt_one_right pi_pos hε.2)
  have hcsin : Continuous (fun ε : ℝ => Real.sin (π * ε)) := by fun_prop
  have hccos : Continuous (fun ε : ℝ => Real.cos (π * ε)) := by fun_prop
  have hinv : Tendsto (fun ε : ℝ => (Real.sin (π * ε))⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2
      ⟨by simpa using (hcsin.tendsto 0).mono_left nhdsWithin_le_nhds, hsin_pos⟩)
  have hcos : Tendsto (fun ε : ℝ => Real.cos (π * ε)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hccos.tendsto 0).mono_left nhdsWithin_le_nhds
  have hF_top : Tendsto
      (fun ε : ℝ => π⁻¹ * Real.arctan ((Real.exp (π * r) - Real.cos (π * ε)) / Real.sin (π * ε)))
      (𝓝[>] 0) (𝓝 (2⁻¹ : ℝ)) := by
    have hpos : 0 < Real.exp (π * r) - 1 := sub_pos.2 (Real.one_lt_exp_iff.2 (mul_pos pi_pos hr))
    have hdiv : Tendsto (fun ε : ℝ => (Real.exp (π * r) - Real.cos (π * ε)) / Real.sin (π * ε))
        (𝓝[>] 0) atTop := by
      simpa only [div_eq_mul_inv] using (tendsto_const_nhds.sub hcos).pos_mul_atTop hpos hinv
    rw [show (2⁻¹ : ℝ) = π⁻¹ * (π / 2) by field_simp [pi_ne_zero]]
    exact ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hdiv).const_mul π⁻¹
  have hF_bot : Tendsto
      (fun ε : ℝ => π⁻¹ * Real.arctan ((Real.exp (-(π * r)) - Real.cos (π * ε)) /
        Real.sin (π * ε))) (𝓝[>] 0) (𝓝 (-(2⁻¹ : ℝ))) := by
    have hpos : 0 < 1 - Real.exp (-(π * r)) :=
      sub_pos.2 (Real.exp_lt_one_iff.2 (neg_neg_of_pos (mul_pos pi_pos hr)))
    have hdiv_pos : Tendsto (fun ε : ℝ => (Real.cos (π * ε) - Real.exp (-(π * r))) /
        Real.sin (π * ε)) (𝓝[>] 0) atTop := by
      simpa only [div_eq_mul_inv] using (hcos.sub tendsto_const_nhds).pos_mul_atTop hpos hinv
    have hdiv : Tendsto (fun ε : ℝ => (Real.exp (-(π * r)) - Real.cos (π * ε)) / Real.sin (π * ε))
        (𝓝[>] 0) atBot :=
      tendsto_neg_atTop_iff.1 (hdiv_pos.congr fun _ => by ring)
    rw [show -(2⁻¹ : ℝ) = π⁻¹ * -(π / 2) by field_simp [pi_ne_zero]]
    exact ((Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp hdiv).const_mul π⁻¹
  refine ((show (2⁻¹ : ℝ) - -(2⁻¹ : ℝ) = 1 by norm_num) ▸ hF_top.sub hF_bot).congr' ?_
  filter_upwards [hsin_pos] with ε hsin
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_stripPoisson₀_primitive hsin.ne' y)
    (integrable_stripPoisson₀ ε).intervalIntegrable]
  simp [mul_neg]

private theorem integral_Icc_stripPoisson₀_sub {ε r : ℝ} (hr : 0 ≤ r) (c : ℝ) :
    ∫ s in Icc (c - r) (c + r), stripPoisson₀ ε (c - s) =
      ∫ y in (-r)..r, stripPoisson₀ ε y := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : c - r ≤ c + r),
    intervalIntegral.integral_comp_sub_left (fun y => stripPoisson₀ ε y) c]
  simp [sub_add_cancel_left]

private theorem dist_lt_of_mem_Icc_contracted {T η ε t s : ℝ} (hε0 : 0 < ε)
    (hεb : ε < (η / 2) / (2 * max T 1)) (ht : t ∈ Icc (-T) T)
    (hs : s ∈ Icc ((1 - 2 * ε) * t - η / 2) ((1 - 2 * ε) * t + η / 2)) :
    dist s t < η := by
  have hMT : 0 < max T 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hεT : |(1 - 2 * ε) * t - t| < η / 2 := calc
    |(1 - 2 * ε) * t - t| = 2 * ε * |t| := by
      rw [show (1 - 2 * ε) * t - t = -(2 * ε * t) by ring, abs_neg, abs_mul,
        abs_of_pos (mul_pos zero_lt_two hε0)]
    _ ≤ 2 * ε * max T 1 :=
      mul_le_mul_of_nonneg_left ((abs_le.2 ht).trans (le_max_left _ _))
        (mul_pos zero_lt_two hε0).le
    _ < 2 * ((η / 2) / (2 * max T 1)) * max T 1 :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hεb zero_lt_two) hMT
    _ = η / 2 := by field_simp [hMT.ne']
  have hs' : |s - (1 - 2 * ε) * t| ≤ η / 2 :=
    abs_sub_le_iff.2 ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [Real.dist_eq]
  linarith [abs_sub_le s ((1 - 2 * ε) * t) t]

private theorem mul_sub_le_integral_stripPoisson₀ {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) (hunonneg : ∀ s, 0 ≤ u s) {ε c r a b : ℝ} (hε : ε ∈ Ioo 0 1)
    (ha : 0 ≤ a) (hb : b ≤ ∫ s in Icc (c - r) (c + r), stripPoisson₀ ε (c - s))
    (hpt : ∀ s ∈ Icc (c - r) (c + r), a ≤ u s) :
    a * b ≤ ∫ s, u s * stripPoisson₀ ε (c - s) := by
  have hint_prod : Integrable (fun s => u s * stripPoisson₀ ε (c - s)) :=
    hu.mul ((continuous_stripPoisson₀ ε).comp (continuous_const.sub continuous_id))
      |>.integrable_of_hasCompactSupport hsupp.mul_right
  calc a * b ≤ a * ∫ s in Icc (c - r) (c + r), stripPoisson₀ ε (c - s) :=
        mul_le_mul_of_nonneg_left hb ha
    _ = ∫ s in Icc (c - r) (c + r), a * stripPoisson₀ ε (c - s) := (integral_const_mul _ _).symm
    _ ≤ ∫ s in Icc (c - r) (c + r), u s * stripPoisson₀ ε (c - s) := by
        have ha_int := (((integrable_stripPoisson₀ ε).comp_sub_left c).const_mul a).integrableOn
          (s := Icc (c - r) (c + r))
        exact setIntegral_mono_on ha_int hint_prod.integrableOn measurableSet_Icc fun s hs =>
          mul_le_mul_of_nonneg_right (hpt s hs) (stripPoisson₀_pos hε (c - s)).le
    _ ≤ ∫ s, u s * stripPoisson₀ ε (c - s) :=
        setIntegral_le_integral hint_prod
          (ae_of_all _ fun s => mul_nonneg (hunonneg s) (stripPoisson₀_pos hε (c - s)).le)

/-- Approximate identity lower bound of `stripPoisson₀ ε` as `ε → 0⁺` on compact intervals, for a
nonnegative compactly supported continuous function. -/
private theorem exists_eps_integral_stripPoisson₀_ge {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) (hunonneg : ∀ s, 0 ≤ u s) {T κ : ℝ} (hκ : 0 < κ) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ t ∈ Icc (-T) T,
      u t - κ ≤ ∫ s, u s * stripPoisson₀ ε (((1 - 2 * ε) * t) - s) := by
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hu
  let U := max M 1
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hu_le (s : ℝ) : u s ≤ U := (le_abs_self (u s)).trans ((hM s).trans (le_max_left _ _))
  obtain ⟨η, hηpos, hη⟩ := Metric.uniformContinuous_iff.1
    (hsupp.uniformContinuous_of_continuous hu) (κ / 3) (by positivity)
  have hκU_pos : 0 < κ / (3 * U) := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁_mem⟩ := Metric.mem_nhdsWithin_iff.1
    ((tendsto_intervalIntegral_stripPoisson₀_nhdsGT (half_pos hηpos)).eventually
      (Ioo_mem_nhds (sub_lt_self 1 hκU_pos) (by norm_num : (1 : ℝ) < 2)))
  refine ⟨min (min δ₁ (2⁻¹ : ℝ)) ((η / 2) / (2 * max T 1)),
    lt_min (lt_min hδ₁ (by norm_num)) (by positivity), fun ε hε t ht => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 :=
    (hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))).trans (by norm_num)
  by_cases hsign : u t - κ / 3 ≤ 0
  · exact (by linarith : u t - κ ≤ 0).trans
      (integral_nonneg fun s => mul_nonneg (hunonneg s) (stripPoisson₀_pos ⟨hε0, hε1⟩ _).le)
  have hstep1 : u t - κ ≤ (u t - κ / 3) * (1 - κ / (3 * U)) := by
    have h1 := mul_le_mul_of_nonneg_right (by linarith [hu_le t] : u t - κ / 3 ≤ U) hκU_pos.le
    have h2 : U * (κ / (3 * U)) = κ / 3 := by field_simp [hUpos.ne']
    linarith
  refine hstep1.trans (mul_sub_le_integral_stripPoisson₀ (r := η / 2) hu hsupp hunonneg ⟨hε0, hε1⟩
    (not_le.1 hsign).le ?_ fun s hs => ?_)
  · rw [integral_Icc_stripPoisson₀_sub (half_pos hηpos).le]
    exact (hδ₁_mem ⟨by simp [abs_of_pos hε0,
      hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))], hε0⟩).1.le
  · have hd : dist (u s) (u t) < κ / 3 :=
      hη (dist_lt_of_mem_Icc_contracted hε0 (hε.2.trans_le (min_le_right _ _)) ht hs)
    linarith [(abs_sub_le_iff.1 (Real.dist_eq (u s) (u t) ▸ hd.le)).2]

end StripKernel

/-! ### Stieltjes/Poisson bounds on the complex interpolation norm -/

namespace ComplexMethodSpace

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V}

private theorem mul_I_mem_closure_verticalStrip (t : ℝ) :
    (t : ℂ) * I ∈ closure (verticalStrip 0 1) := by
  rw [verticalStrip, closure_preimage_re, closure_Ioo zero_ne_one]
  simp

private theorem one_add_mul_I_mem_closure_verticalStrip (t : ℝ) :
    1 + (t : ℂ) * I ∈ closure (verticalStrip 0 1) := by
  rw [verticalStrip, closure_preimage_re, closure_Ioo zero_ne_one]
  simp

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
  have hc0 : Continuous (fun t : ℝ => c ((t : ℂ) * I)) :=
    hc.continuousOn.comp_continuous (by fun_prop) mul_I_mem_closure_verticalStrip
  have hc1 : Continuous (fun t : ℝ => c (1 + (t : ℂ) * I)) :=
    hc.continuousOn.comp_continuous (by fun_prop) one_add_mul_I_mem_closure_verticalStrip
  let g₀' : C₀(ℝ, X₀) := ZeroAtInftyContinuousMap.compLeftFamily
    (fun t : ℝ => c ((t : ℂ) * I) • ContinuousLinearMap.id ℂ X₀)
    (fun _ => hc0.smul continuous_const)
    ⟨K, fun t e => by
      simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, norm_smul]
      exact mul_le_mul_of_nonneg_right (hK ((t : ℂ) * I) (by simp [verticalClosedStrip]))
        (norm_nonneg e)⟩
    (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1
  let g₁' : C₀(ℝ, X₁) := ZeroAtInftyContinuousMap.compLeftFamily
    (fun t : ℝ => c (1 + (t : ℂ) * I) • ContinuousLinearMap.id ℂ X₁)
    (fun _ => hc1.smul continuous_const)
    ⟨K, fun t e => by
      simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, norm_smul]
      exact mul_le_mul_of_nonneg_right (hK (1 + (t : ℂ) * I) (by simp [verticalClosedStrip]))
        (norm_nonneg e)⟩
    (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2
  have hF' : C.IsStripFunction (fun z => c z • C.stripFunction g z) (g₀', g₁') :=
    (C.isStripFunction_stripFunction g).smul hc hK
      (fun t => by simp [g₀', ZeroAtInftyContinuousMap.compLeftFamily_apply])
      (fun t => by simp [g₁', ZeroAtInftyContinuousMap.compLeftFamily_apply])
  refine ⟨⟨(g₀', g₁'), C.mem_stripTraces_iff.2 ⟨_, hF'⟩⟩,
    fun t => by simp [g₀', ZeroAtInftyContinuousMap.compLeftFamily_apply],
    fun t => by simp [g₁', ZeroAtInftyContinuousMap.compLeftFamily_apply],
    fun θ hθ => toSum_injective ?_⟩
  have hθstrip : (θ : ℂ) ∈ verticalClosedStrip 0 1 := by simpa [verticalClosedStrip] using hθ
  rw [toSum_mk, map_smul, toSum_mk, stripEval_apply, stripEval_apply,
    stripFunction_eq hF' hθstrip]

/-- Multiplying an admissible trace pair by a bounded holomorphic scalar function `c` on the strip
scales `mk θ g` by `c θ` and bounds its norm by the boundary suprema of `c • g`. -/
private theorem norm_smul_mk_le_of_diffContOnCl {θ : ℝ} (hθ : θ ∈ Icc 0 1) (g : C.stripTraces)
    {c : ℂ → ℂ} (hc : DiffContOnCl ℂ c (verticalStrip 0 1))
    {K B : ℝ} (hK : ∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K) (hB : 0 ≤ B)
    (hb₀ : ∀ t : ℝ, ‖c (t * I) • (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t‖ ≤ B)
    (hb₁ : ∀ t : ℝ, ‖c (1 + t * I) • (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t‖ ≤ B) :
    ‖c θ‖ * ‖mk θ g‖ ≤ B := by
  obtain ⟨g', hg₀', hg₁', heq⟩ := exists_stripTraces_smul_of_diffContOnCl g hc hK
  rw [← norm_smul, ← heq hθ]
  refine ((norm_mk_le g').trans_eq (Submodule.norm_coe g').symm).trans (max_le ?_ ?_)
  · exact (ZeroAtInftyContinuousMap.norm_le hB).2 fun t => by rw [hg₀']; exact hb₀ t
  · exact (ZeroAtInftyContinuousMap.norm_le hB).2 fun t => by rw [hg₁']; exact hb₁ t

private theorem norm_mk_le_rpow_mul_rpow_of_lt {θ M₀ M₁ : ℝ} (hθ : θ ∈ Icc 0 1)
    (g : C.stripTraces) (h₀ : ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1‖ < M₀)
    (h₁ : ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2‖ < M₁) :
    ‖mk θ g‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  have hM₀ : 0 < M₀ := (norm_nonneg _).trans_lt h₀
  have hM₁ : 0 < M₁ := (norm_nonneg _).trans_lt h₁
  let c : ℂ → ℂ := fun z => Complex.exp ((z - 1) * Real.log M₀ - z * Real.log M₁)
  have hc_diff : Differentiable ℂ c := by unfold c; fun_prop
  have hc_norm (z : ℂ) : ‖c z‖ = M₀ ^ (z.re - 1) * M₁ ^ (-z.re) := by
    rw [Complex.norm_exp]
    simp only [sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, one_re]
    rw [Real.rpow_def_of_pos hM₀, Real.rpow_def_of_pos hM₁, ← Real.exp_add]
    congr 1
    ring
  have hK (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) : ‖c z‖ ≤ max M₀⁻¹ M₁⁻¹ := by
    rw [hc_norm]
    calc M₀ ^ (z.re - 1) * M₁ ^ (-z.re)
        = (M₀⁻¹) ^ (1 - z.re) * (M₁⁻¹) ^ z.re := by
          rw [Real.inv_rpow hM₀.le, Real.inv_rpow hM₁.le, ← Real.rpow_neg hM₀.le,
            ← Real.rpow_neg hM₁.le]
          ring_nf
      _ ≤ (max M₀⁻¹ M₁⁻¹) ^ (1 - z.re) * (max M₀⁻¹ M₁⁻¹) ^ z.re := by
          gcongr
          · exact sub_nonneg.2 hz.2
          · exact le_max_left _ _
          · exact hz.1
          · exact le_max_right _ _
      _ = max M₀⁻¹ M₁⁻¹ := by
          rw [← Real.rpow_add (lt_of_lt_of_le (inv_pos.2 hM₀) (le_max_left _ _)),
            sub_add_cancel, Real.rpow_one]
  have hbound := norm_smul_mk_le_of_diffContOnCl hθ g hc_diff.diffContOnCl hK zero_le_one
    (fun t => by
      rw [norm_smul, hc_norm]
      simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        zero_sub, neg_zero, Real.rpow_neg_one, Real.rpow_zero, mul_one]
      exact (inv_mul_le_one₀ hM₀).2 ((ZeroAtInftyContinuousMap.norm_coe_le_norm _ t).trans h₀.le))
    (fun t => by
      rw [norm_smul, hc_norm]
      simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, Real.rpow_zero, one_mul, Real.rpow_neg_one]
      exact (inv_mul_le_one₀ hM₁).2 ((ZeroAtInftyContinuousMap.norm_coe_le_norm _ t).trans h₁.le))
  rw [hc_norm, ofReal_re] at hbound
  calc ‖mk θ g‖ = (M₀ ^ (1 - θ) * M₁ ^ θ) * (M₀ ^ (θ - 1) * M₁ ^ (-θ) * ‖mk θ g‖) := by
        rw [← mul_assoc, mul_mul_mul_comm, ← Real.rpow_add hM₀, ← Real.rpow_add hM₁]; simp
    _ ≤ (M₀ ^ (1 - θ) * M₁ ^ θ) * 1 := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = M₀ ^ (1 - θ) * M₁ ^ θ := mul_one _

/-- **Three-lines bound in `[X₀, X₁]_θ`.** For every real `θ` and admissible trace pair
`g = (g₀, g₁)`, the complex interpolation norm satisfies
`‖mk θ g‖ ≤ ‖g₀‖ ^ (1 - θ) * ‖g₁‖ ^ θ`. -/
theorem norm_mk_le_rpow_mul_rpow (θ : ℝ) (g : C.stripTraces) :
    ‖mk θ g‖ ≤
      ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1‖ ^ (1 - θ) * ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2‖ ^ θ := by
  by_cases hθ : θ ∈ Icc 0 1
  · have htend : Tendsto
        (fun δ : ℝ => (‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1‖ + δ) ^ (1 - θ) *
          (‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2‖ + δ) ^ θ)
        (𝓝[>] 0)
        (𝓝 (‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1‖ ^ (1 - θ) *
          ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2‖ ^ θ)) := by
      have hc0 : Continuous (fun δ : ℝ => ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1‖ + δ) := by fun_prop
      have hc1 : Continuous (fun δ : ℝ => ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2‖ + δ) := by fun_prop
      have h0 : Tendsto (fun δ : ℝ => ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1‖ + δ) (𝓝[>] 0)
          (𝓝 ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1‖) := by
        simpa using (hc0.tendsto 0).mono_left nhdsWithin_le_nhds
      have h1 : Tendsto (fun δ : ℝ => ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2‖ + δ) (𝓝[>] 0)
          (𝓝 ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2‖) := by
        simpa using (hc1.tendsto 0).mono_left nhdsWithin_le_nhds
      exact (h0.rpow_const (Or.inr (sub_nonneg.2 hθ.2))).mul (h1.rpow_const (Or.inr hθ.1))
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    exact norm_mk_le_rpow_mul_rpow_of_lt hθ g (by linarith) (by linarith)
  · rw [eq_zero_of_notMem hθ (mk θ g), norm_zero]
    positivity

private theorem diffContOnCl_inv_one_add_mul {A : ℝ} (hA : 0 < A) :
    DiffContOnCl ℂ (fun z : ℂ => (1 + (A : ℂ) * z)⁻¹) (verticalStrip 0 1) := by
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => (1 + (A : ℂ) * z)⁻¹)
      {z : ℂ | -(2 * A)⁻¹ < z.re} := by
    refine DifferentiableOn.inv (by fun_prop) fun z hz => ?_
    have hmul : -(2⁻¹ : ℝ) < A * z.re := by
      have h1 := mul_lt_mul_of_pos_left hz.out hA
      have h2 : A * -(2 * A)⁻¹ = -(2⁻¹ : ℝ) := by field_simp [hA.ne']
      rwa [h2] at h1
    have hre : (2⁻¹ : ℝ) < (1 + (A : ℂ) * z).re := by simp; linarith
    exact norm_pos_iff.1 ((by norm_num : (0 : ℝ) < 2⁻¹).trans_le
      (hre.le.trans (Complex.re_le_norm _)))
  exact DifferentiableOn.diffContOnCl (hdiff.mono ((closure_verticalStrip_subset 0 1).trans
    fun _ hz => (neg_neg_of_pos (by positivity)).trans_le hz.1))

private theorem norm_mk_zero_lt_of_aux (g : C.stripTraces) {ε δ A : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hA : 0 < A)
    (hclose : ∀ ⦃t : ℝ⦄, dist t 0 < δ →
      dist ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t) ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0) < ε / 2)
    (hA1 : 2 * ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1‖ / (δ * ε) < A)
    (hA2 : 2 * ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2‖ / ε < A) :
    ‖mk 0 g‖ < ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0‖ + ε := by
  have hc_le (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) : ‖(1 + (A : ℂ) * z)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    refine inv_le_one_of_one_le₀ (le_trans ?_ (Complex.re_le_norm _))
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith [hz.1]
  have hb := norm_smul_mk_le_of_diffContOnCl ⟨le_rfl, zero_le_one⟩ g
    (diffContOnCl_inv_one_add_mul hA) hc_le
    (B := ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0‖ + ε / 2) (by positivity)
    (fun t => by
      rw [norm_smul]
      by_cases ht : |t| < δ
      · have hd := hclose (by simpa [Real.dist_eq] using ht)
        rw [dist_eq_norm] at hd
        have htri := norm_sub_norm_le ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t)
          ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0)
        exact (mul_le_of_le_one_left (norm_nonneg _)
          (hc_le (t * I) (by simp [verticalClosedStrip]))).trans (by linarith)
      · have hnorm : A * δ ≤ ‖1 + (A : ℂ) * (t * I)‖ :=
          (mul_le_mul_of_nonneg_left (not_lt.1 ht) hA.le).trans
            ((by simp [abs_mul, abs_of_pos hA] :
              A * |t| = |(1 + (A : ℂ) * (t * I)).im|).trans_le (abs_im_le_norm _))
        have hsmall : ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1‖ / (A * δ) ≤ ε / 2 :=
          (div_le_iff₀ (by positivity)).2 (by nlinarith [(div_lt_iff₀ (by positivity)).1 hA1])
        rw [norm_inv]
        exact (mul_le_mul (inv_anti₀ (by positivity) hnorm)
          (ZeroAtInftyContinuousMap.norm_coe_le_norm _ t) (norm_nonneg _) (by positivity)).trans
          ((inv_mul_eq_div _ _).trans_le (hsmall.trans (le_add_of_nonneg_left (norm_nonneg _)))))
    (fun t => by
      rw [norm_smul, norm_inv]
      have hsmall : ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2‖ / A ≤ ε / 2 :=
        (div_le_iff₀ hA).2 (by nlinarith [(div_lt_iff₀ hε).1 hA2])
      exact (mul_le_mul (inv_anti₀ hA (le_trans (by simp) (Complex.re_le_norm _)))
        (ZeroAtInftyContinuousMap.norm_coe_le_norm _ t) (norm_nonneg _) (inv_pos.2 hA).le).trans
        ((inv_mul_eq_div _ _).trans_le (hsmall.trans (le_add_of_nonneg_left (norm_nonneg _)))))
  have hc0 : ‖((1 + (A : ℂ) * ((0 : ℝ) : ℂ))⁻¹ : ℂ)‖ = 1 := by simp
  rw [hc0, one_mul] at hb
  linarith [half_lt_self hε]

private theorem norm_mk_zero_le (g : C.stripTraces) :
    ‖mk 0 g‖ ≤ ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0‖ := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.1
    ((map_continuous (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1).continuousAt (x := 0)) (ε / 2) (half_pos hε)
  obtain ⟨A, hA⟩ := exists_gt
    (max 0 (max (2 * ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1‖ / (δ * ε))
      (2 * ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2‖ / ε)))
  exact norm_mk_zero_lt_of_aux g hε hδ ((le_max_left _ _).trans_lt hA) hclose
    (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hA)
    (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hA)

/-- At `θ = 0`, the quotient norm of an admissible trace pair is the norm in `X₀` of its left
boundary trace at `0`. -/
theorem norm_mk_zero (g : C.stripTraces) :
    ‖mk 0 g‖ = ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0‖ := by
  refine le_antisymm (norm_mk_zero_le g) (le_of_forall_gt fun r hr => ?_)
  obtain ⟨h, heq, hh⟩ := norm_lt_iff.1 hr
  have hsum : C.fstToSum ((h : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0) =
      C.fstToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0) := by
    have heval := congrArg toSum heq
    rw [toSum_mk, toSum_mk, stripEval_apply, stripEval_apply, ofReal_zero,
      ← zero_mul I, ← ofReal_zero, C.stripFunction_mul_I, C.stripFunction_mul_I] at heval
    exact heval
  have h0 : (h : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0 = (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0 := by
    apply C.embed₀_injective
    have hv := congrArg C.sumSpaceEmbed hsum
    rwa [C.sumSpaceEmbed_fstToSum, C.sumSpaceEmbed_fstToSum] at hv
  rw [← h0]
  have h1 := ZeroAtInftyContinuousMap.norm_coe_le_norm (h : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0
  have h2 := norm_fst_le (h : C₀(ℝ, X₀) × C₀(ℝ, X₁))
  exact (h1.trans h2).trans_lt (by rwa [Submodule.norm_coe])

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

private def holoPotential (δ : ℝ) (u₀ u₁ : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  (Real.log δ : ℂ) +
    ((∫ s, (u₀ s : ℂ) * holoPoisson₀ (ζ - s * I)) + ∫ s, (u₁ s : ℂ) * holoPoisson₁ (ζ - s * I))

private theorem differentiableOn_holoPotential {δ : ℝ} {u₀ u₁ : ℝ → ℝ} (hu₀ : Continuous u₀)
    (hu₁ : Continuous u₁) (hs₀ : HasCompactSupport u₀) (hs₁ : HasCompactSupport u₁) :
    DifferentiableOn ℂ (holoPotential δ u₀ u₁) (verticalStrip 0 1) :=
  (differentiableOn_const _).add ((differentiableOn_integral_holoPoisson₀ hu₀ hs₀).add
    (differentiableOn_integral_holoPoisson₁ hu₁ hs₁))

private theorem re_holoPotential {δ : ℝ} {u₀ u₁ : ℝ → ℝ} (hu₀ : Continuous u₀)
    (hu₁ : Continuous u₁) (hs₀ : HasCompactSupport u₀) (hs₁ : HasCompactSupport u₁) {ζ : ℂ}
    (hζ : ζ ∈ verticalStrip 0 1) :
    (holoPotential δ u₀ u₁ ζ).re = Real.log δ +
      ((∫ s, u₀ s * stripPoisson₀ ζ.re (ζ.im - s)) +
        ∫ s, u₁ s * stripPoisson₁ ζ.re (ζ.im - s)) := by
  simp only [holoPotential, add_re, ofReal_re, re_integral_holoPoisson₀ hu₀ hs₀ hζ,
    re_integral_holoPoisson₁ hu₁ hs₁ hζ]

omit [NormedSpace ℂ X₀] in
private theorem norm_exp_neg_holoPotential_mul_left_le {δ T κ ε : ℝ} (hδ : 0 < δ) (hκ : 0 < κ)
    (hε : ε ∈ Ioo (0 : ℝ) 4⁻¹) {f : C₀(ℝ, X₀)} (hf : ∀ s, T ≤ |s| → ‖f s‖ ≤ δ)
    {u₀ u₁ : ℝ → ℝ} (hu₀_cont : Continuous u₀) (hu₁_cont : Continuous u₁)
    (hu₀_nonneg : ∀ s, 0 ≤ u₀ s) (hu₁_nonneg : ∀ s, 0 ≤ u₁ s)
    (hu₀_supp : HasCompactSupport u₀) (hu₁_supp : HasCompactSupport u₁)
    (hu₀_eq : ∀ s, Real.log δ + u₀ s = Real.log (max ‖f s‖ δ))
    (happrox₀ : ∀ t ∈ Icc (-T) T, u₀ t - κ ≤ ∫ s, u₀ s * stripPoisson₀ ε ((1 - 2 * ε) * t - s))
    (t : ℝ) :
    ‖Complex.exp (-holoPotential δ u₀ u₁ ((1 - 2 * (ε : ℂ)) * (t * I) + ε))‖ * ‖f t‖ ≤
      Real.exp κ := by
  have hε0 : 0 < ε := hε.1
  have hε14 : ε < 4⁻¹ := hε.2
  let ζ : ℂ := (1 - 2 * (ε : ℂ)) * (t * I) + ε
  have hζ : ζ ∈ verticalStrip 0 1 := by
    rw [mem_verticalStrip_iff, show ζ.re = ε by simp [ζ], mem_Ioo]
    exact ⟨hε0, by linarith⟩
  by_cases ht : T ≤ |t|
  · have hc_le : ‖Complex.exp (-holoPotential δ u₀ u₁ ζ)‖ ≤ δ⁻¹ := by
      rw [Complex.norm_exp, neg_re, ← Real.exp_log (inv_pos.2 hδ), Real.log_inv,
        re_holoPotential hu₀_cont hu₁_cont hu₀_supp hu₁_supp hζ]
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      have h0 : 0 ≤ ∫ s, u₀ s * stripPoisson₀ ζ.re (ζ.im - s) := integral_nonneg fun s =>
        mul_nonneg (hu₀_nonneg s) (stripPoisson₀_pos hζ (ζ.im - s)).le
      have h1 : 0 ≤ ∫ s, u₁ s * stripPoisson₁ ζ.re (ζ.im - s) := integral_nonneg fun s =>
        mul_nonneg (hu₁_nonneg s) (stripPoisson₁_pos hζ (ζ.im - s)).le
      linarith
    exact (mul_le_mul hc_le (hf t ht) (norm_nonneg _) (inv_pos.2 hδ).le).trans
      ((inv_mul_cancel₀ hδ.ne').trans_le (Real.one_le_exp hκ.le))
  · have hap := happrox₀ t (abs_le.1 (not_le.1 ht).le)
    have hpos1 : 0 ≤ ∫ s, u₁ s * stripPoisson₁ ε ((1 - 2 * ε) * t - s) :=
      integral_nonneg fun s =>
        mul_nonneg (hu₁_nonneg s) (stripPoisson₁_pos ⟨hε0, by linarith⟩ ((1 - 2 * ε) * t - s)).le
    have hre0 : Real.log (max ‖f t‖ δ) - κ ≤ (holoPotential δ u₀ u₁ ζ).re := by
      rw [re_holoPotential hu₀_cont hu₁_cont hu₀_supp hu₁_supp hζ,
        show ζ.re = ε by simp [ζ], show ζ.im = (1 - 2 * ε) * t by simp [ζ]]
      linarith [hu₀_eq t]
    have hm := lt_of_lt_of_le hδ (le_max_right ‖f t‖ δ)
    calc ‖Complex.exp (-holoPotential δ u₀ u₁ ζ)‖ * ‖f t‖
        ≤ Real.exp (κ - Real.log (max ‖f t‖ δ)) * max ‖f t‖ δ :=
          mul_le_mul (by rw [Complex.norm_exp, neg_re]; exact Real.exp_le_exp.2 (by linarith))
            (le_max_left _ _) (norm_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp κ := by
          rw [Real.exp_sub, div_mul_eq_mul_div, Real.exp_log hm, mul_div_cancel_right₀ _ hm.ne']

omit [NormedSpace ℂ X₁] in
private theorem norm_exp_neg_holoPotential_mul_right_le {δ T κ ε : ℝ} (hδ : 0 < δ) (hκ : 0 < κ)
    (hε : ε ∈ Ioo (0 : ℝ) 4⁻¹) {f : C₀(ℝ, X₁)} (hf : ∀ s, T ≤ |s| → ‖f s‖ ≤ δ)
    {u₀ u₁ : ℝ → ℝ} (hu₀_cont : Continuous u₀) (hu₁_cont : Continuous u₁)
    (hu₀_nonneg : ∀ s, 0 ≤ u₀ s) (hu₁_nonneg : ∀ s, 0 ≤ u₁ s)
    (hu₀_supp : HasCompactSupport u₀) (hu₁_supp : HasCompactSupport u₁)
    (hu₁_eq : ∀ s, Real.log δ + u₁ s = Real.log (max ‖f s‖ δ))
    (happrox₁ : ∀ t ∈ Icc (-T) T,
      (u₁ ∘ Neg.neg) t - κ ≤ ∫ s, (u₁ ∘ Neg.neg) s * stripPoisson₀ ε ((1 - 2 * ε) * t - s))
    (t : ℝ) :
    ‖Complex.exp (-holoPotential δ u₀ u₁ ((1 - 2 * (ε : ℂ)) * (1 + t * I) + ε))‖ * ‖f t‖ ≤
      Real.exp κ := by
  have hε0 : 0 < ε := hε.1
  have hε14 : ε < 4⁻¹ := hε.2
  let ζ : ℂ := (1 - 2 * (ε : ℂ)) * (1 + t * I) + ε
  have hζ : ζ ∈ verticalStrip 0 1 := by
    rw [mem_verticalStrip_iff, show ζ.re = 1 - ε by simp [ζ]; ring, mem_Ioo]
    exact ⟨by linarith, by linarith⟩
  by_cases ht : T ≤ |t|
  · have hc_le : ‖Complex.exp (-holoPotential δ u₀ u₁ ζ)‖ ≤ δ⁻¹ := by
      rw [Complex.norm_exp, neg_re, ← Real.exp_log (inv_pos.2 hδ), Real.log_inv,
        re_holoPotential hu₀_cont hu₁_cont hu₀_supp hu₁_supp hζ]
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      have h0 : 0 ≤ ∫ s, u₀ s * stripPoisson₀ ζ.re (ζ.im - s) := integral_nonneg fun s =>
        mul_nonneg (hu₀_nonneg s) (stripPoisson₀_pos hζ (ζ.im - s)).le
      have h1 : 0 ≤ ∫ s, u₁ s * stripPoisson₁ ζ.re (ζ.im - s) := integral_nonneg fun s =>
        mul_nonneg (hu₁_nonneg s) (stripPoisson₁_pos hζ (ζ.im - s)).le
      linarith
    exact (mul_le_mul hc_le (hf t ht) (norm_nonneg _) (inv_pos.2 hδ).le).trans
      ((inv_mul_cancel₀ hδ.ne').trans_le (Real.one_le_exp hκ.le))
  · obtain ⟨ht1, ht2⟩ := abs_le.1 (not_le.1 ht).le
    have hap := happrox₁ (-t) ⟨by linarith, by linarith⟩
    have hcov : ∫ s, (u₁ ∘ Neg.neg) s * stripPoisson₀ ε ((1 - 2 * ε) * (-t) - s) =
        ∫ s, u₁ s * stripPoisson₁ (1 - ε) ((1 - 2 * ε) * t - s) := by
      rw [← MeasureTheory.integral_neg_eq_self
        (fun s : ℝ => u₁ s * stripPoisson₁ (1 - ε) ((1 - 2 * ε) * t - s))]
      refine integral_congr_ae (ae_of_all _ fun s => ?_)
      dsimp only [Function.comp_apply]
      rw [stripPoisson₁_one_sub, show (1 - 2 * ε) * t - -s = -((1 - 2 * ε) * (-t) - s) by ring,
        stripPoisson₀_neg]
    rw [Function.comp_apply, neg_neg, hcov] at hap
    have hpos0 : 0 ≤ ∫ s, u₀ s * stripPoisson₀ (1 - ε) ((1 - 2 * ε) * t - s) :=
      integral_nonneg fun s =>
        mul_nonneg (hu₀_nonneg s)
          (stripPoisson₀_pos ⟨by linarith, by linarith⟩ ((1 - 2 * ε) * t - s)).le
    have hre1 : Real.log (max ‖f t‖ δ) - κ ≤ (holoPotential δ u₀ u₁ ζ).re := by
      rw [re_holoPotential hu₀_cont hu₁_cont hu₀_supp hu₁_supp hζ,
        show ζ.re = 1 - ε by simp [ζ]; ring, show ζ.im = (1 - 2 * ε) * t by simp [ζ]]
      linarith [hu₁_eq t]
    have hm := lt_of_lt_of_le hδ (le_max_right ‖f t‖ δ)
    calc ‖Complex.exp (-holoPotential δ u₀ u₁ ζ)‖ * ‖f t‖
        ≤ Real.exp (κ - Real.log (max ‖f t‖ δ)) * max ‖f t‖ δ :=
          mul_le_mul (by rw [Complex.norm_exp, neg_re]; exact Real.exp_le_exp.2 (by linarith))
            (le_max_left _ _) (norm_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp κ := by
          rw [Real.exp_sub, div_mul_eq_mul_div, Real.exp_log hm, mul_div_cancel_right₀ _ hm.ne']

private theorem norm_mk_le_exp_re_contracted_holoPotential {θ δ T κ ε : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hδ : 0 < δ) (hκ : 0 < κ) (hε : ε ∈ Ioo (0 : ℝ) 4⁻¹) (g : C.stripTraces)
    (hg₀ : ∀ s, T ≤ |s| → ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 s‖ ≤ δ)
    (hg₁ : ∀ s, T ≤ |s| → ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 s‖ ≤ δ)
    {u₀ u₁ : ℝ → ℝ} (hu₀_cont : Continuous u₀) (hu₁_cont : Continuous u₁)
    (hu₀_nonneg : ∀ s, 0 ≤ u₀ s) (hu₁_nonneg : ∀ s, 0 ≤ u₁ s)
    (hu₀_supp : HasCompactSupport u₀) (hu₁_supp : HasCompactSupport u₁)
    (hu₀_eq : ∀ s, Real.log δ + u₀ s = Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 s‖ δ))
    (hu₁_eq : ∀ s, Real.log δ + u₁ s = Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 s‖ δ))
    (happrox₀ : ∀ t ∈ Icc (-T) T, u₀ t - κ ≤ ∫ s, u₀ s * stripPoisson₀ ε ((1 - 2 * ε) * t - s))
    (happrox₁ : ∀ t ∈ Icc (-T) T,
      (u₁ ∘ Neg.neg) t - κ ≤ ∫ s, (u₁ ∘ Neg.neg) s * stripPoisson₀ ε ((1 - 2 * ε) * t - s)) :
    ‖mk θ g‖ ≤ Real.exp κ *
      Real.exp ((holoPotential δ u₀ u₁ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re) := by
  have hε0 : 0 < ε := hε.1
  have hε14 : ε < 4⁻¹ := hε.2
  let w : ℂ → ℂ := fun z => (1 - 2 * (ε : ℂ)) * z + ε
  have hw_strip {z : ℂ} (hz : z ∈ {z : ℂ | -(ε / 2) < z.re ∧ z.re < 1 + ε / 2}) :
      w z ∈ verticalStrip 0 1 := by
    rw [mem_verticalStrip_iff, show (w z).re = (1 - 2 * ε) * z.re + ε by simp [w], mem_Ioo]
    exact ⟨by nlinarith [hz.1], by nlinarith [hz.2]⟩
  have hw_diff : Differentiable ℂ w := by unfold w; fun_prop
  have hΦ_diff := differentiableOn_holoPotential (δ := δ) hu₀_cont hu₁_cont hu₀_supp hu₁_supp
  let c : ℂ → ℂ := fun z => Complex.exp (-holoPotential δ u₀ u₁ (w z))
  have hc_diff : DiffContOnCl ℂ c (verticalStrip 0 1) :=
    DifferentiableOn.diffContOnCl
      (((hΦ_diff.comp hw_diff.differentiableOn fun _ hz => hw_strip hz).neg).cexp.mono
        ((closure_verticalStrip_subset 0 1).trans fun _ hz =>
          ⟨by linarith [hz.1], by linarith [hz.2]⟩))
  have hc_le (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) : ‖c z‖ ≤ δ⁻¹ := by
    have hwz : w z ∈ verticalStrip 0 1 := hw_strip ⟨by linarith [hz.1], by linarith [hz.2]⟩
    rw [Complex.norm_exp, neg_re, ← Real.exp_log (inv_pos.2 hδ), Real.log_inv,
      re_holoPotential hu₀_cont hu₁_cont hu₀_supp hu₁_supp hwz]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have h0 : 0 ≤ ∫ s, u₀ s * stripPoisson₀ (w z).re ((w z).im - s) := integral_nonneg fun s =>
      mul_nonneg (hu₀_nonneg s) (stripPoisson₀_pos hwz ((w z).im - s)).le
    have h1 : 0 ≤ ∫ s, u₁ s * stripPoisson₁ (w z).re ((w z).im - s) := integral_nonneg fun s =>
      mul_nonneg (hu₁_nonneg s) (stripPoisson₁_pos hwz ((w z).im - s)).le
    linarith
  have hb := norm_smul_mk_le_of_diffContOnCl ⟨hθ.1.le, hθ.2.le⟩ g hc_diff hc_le (Real.exp_pos κ).le
    (fun t => by
      rw [norm_smul]
      exact norm_exp_neg_holoPotential_mul_left_le hδ hκ hε hg₀ hu₀_cont hu₁_cont hu₀_nonneg
        hu₁_nonneg hu₀_supp hu₁_supp hu₀_eq happrox₀ t)
    (fun t => by
      rw [norm_smul]
      exact norm_exp_neg_holoPotential_mul_right_le hδ hκ hε hg₁ hu₀_cont hu₁_cont hu₀_nonneg
        hu₁_nonneg hu₀_supp hu₁_supp hu₁_eq happrox₁ t)
  have hcθ : ‖c θ‖ =
      (Real.exp ((holoPotential δ u₀ u₁ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re))⁻¹ := by
    dsimp only [c]
    rw [show w θ = (((1 - 2 * ε) * θ + ε : ℝ) : ℂ) by simp [w], Complex.norm_exp, neg_re,
      Real.exp_neg]
  rw [hcθ] at hb
  exact ((inv_mul_le_iff₀ (Real.exp_pos _)).1 hb).trans_eq (mul_comm _ _)

/-- Holomorphic strip bound for any pair of nonnegative compactly supported continuous log-envelopes
`u₀`, `u₁`. -/
private theorem norm_mk_le_exp_re_holoPotential {θ δ T : ℝ} (hθ : θ ∈ Ioo 0 1) (hδ : 0 < δ)
    (g : C.stripTraces) (hg₀ : ∀ s, T ≤ |s| → ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 s‖ ≤ δ)
    (hg₁ : ∀ s, T ≤ |s| → ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 s‖ ≤ δ)
    {u₀ u₁ : ℝ → ℝ} (hu₀_cont : Continuous u₀) (hu₁_cont : Continuous u₁)
    (hu₀_nonneg : ∀ s, 0 ≤ u₀ s) (hu₁_nonneg : ∀ s, 0 ≤ u₁ s)
    (hu₀_supp : HasCompactSupport u₀) (hu₁_supp : HasCompactSupport u₁)
    (hu₀_eq : ∀ s, Real.log δ + u₀ s = Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 s‖ δ))
    (hu₁_eq : ∀ s, Real.log δ + u₁ s = Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 s‖ δ)) :
    ‖mk θ g‖ ≤ Real.exp (Real.log δ +
      ((∫ s, u₀ s * stripPoisson₀ θ s) + ∫ s, u₁ s * stripPoisson₁ θ s)) := by
  let Φ := holoPotential δ u₀ u₁
  have hΦ_diff := differentiableOn_holoPotential (δ := δ) hu₀_cont hu₁_cont hu₀_supp hu₁_supp
  have hθstrip : (θ : ℂ) ∈ verticalStrip 0 1 := by simpa [verticalStrip] using hθ
  suffices hκ_le : ∀ κ > 0, ‖mk θ g‖ ≤ Real.exp κ * Real.exp (Φ θ).re by
    have hc : Continuous (fun κ : ℝ => Real.exp κ * Real.exp (Φ θ).re) := by fun_prop
    have htendκ : Tendsto (fun κ : ℝ => Real.exp κ * Real.exp (Φ θ).re) (𝓝[>] 0)
        (𝓝 (Real.exp (Φ θ).re)) := by
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine (ge_of_tendsto htendκ (eventually_nhdsWithin_of_forall hκ_le)).trans_eq ?_
    simp [Φ, re_holoPotential hu₀_cont hu₁_cont hu₀_supp hu₁_supp hθstrip]
  intro κ hκ
  obtain ⟨ε₀, hε₀, happrox₀⟩ :=
    exists_eps_integral_stripPoisson₀_ge hu₀_cont hu₀_supp hu₀_nonneg (T := T) hκ
  obtain ⟨ε₁, hε₁, happrox₁⟩ :=
    exists_eps_integral_stripPoisson₀_ge (hu₁_cont.comp continuous_neg)
      (hu₁_supp.comp_homeomorph (Homeomorph.neg ℝ)) (fun s => hu₁_nonneg (-s)) (T := T) hκ
  have hΦ_cont : ContinuousAt Φ (((1 - 2 * (0 : ℝ)) * θ + (0 : ℝ) : ℝ) : ℂ) := by
    simpa using hΦ_diff.continuousOn.continuousAt
      ((isOpen_Ioo.preimage continuous_re).mem_nhds hθstrip)
  have hw : Continuous (fun ε : ℝ => (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)) := by fun_prop
  have hcomp : ContinuousAt (fun ε : ℝ => Φ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)) 0 :=
    ContinuousAt.comp (g := Φ) (f := fun ε : ℝ => (((1 - 2 * ε) * θ + ε : ℝ) : ℂ))
      hΦ_cont (hw.continuousAt (x := 0))
  have hcont_θ : ContinuousAt
      (fun ε : ℝ => Real.exp κ * Real.exp ((Φ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re)) 0 :=
    continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
      (Complex.continuous_re.continuousAt.comp hcomp))
  have htend_ε : Tendsto
      (fun ε : ℝ => Real.exp κ * Real.exp ((Φ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re))
      (𝓝[>] 0) (𝓝 (Real.exp κ * Real.exp (Φ θ).re)) := by
    simpa using hcont_θ.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend_ε ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min (lt_min hε₀ hε₁) (by norm_num : (0 : ℝ) < 4⁻¹))]
    with ε hε
  exact norm_mk_le_exp_re_contracted_holoPotential hθ hδ hκ ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
    g hg₀ hg₁ hu₀_cont hu₁_cont hu₀_nonneg hu₁_nonneg hu₀_supp hu₁_supp hu₀_eq hu₁_eq
    (happrox₀ ε ⟨hε.1, hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩)
    (happrox₁ ε ⟨hε.1, hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))⟩)

private theorem continuous_and_hasCompactSupport_log_max_div {E : Type*} [NormedAddCommGroup E]
    (f : C₀(ℝ, E)) {δ T : ℝ} (hδ : 0 < δ) (hf : ∀ s, T ≤ |s| → ‖f s‖ ≤ δ) :
    Continuous (fun s => Real.log (max ‖f s‖ δ / δ)) ∧
      HasCompactSupport (fun s => Real.log (max ‖f s‖ δ / δ)) := by
  refine ⟨Continuous.log (((map_continuous f).norm.max continuous_const).div_const δ) fun _ =>
      (div_pos (lt_of_lt_of_le hδ (le_max_right _ _)) hδ).ne',
    HasCompactSupport.intro (K := Icc (-T) T) isCompact_Icc fun s hs => ?_⟩
  have habs : T ≤ |s| := le_of_lt (not_le.1 fun h => hs (abs_le.1 h))
  simp [max_eq_right (hf s habs), div_self hδ.ne']

private theorem norm_mk_le_exp_integral_log_max_of_pos {θ δ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hδ : 0 < δ) (g : C.stripTraces) :
    ‖mk θ g‖ ≤ Real.exp
      ((∫ s, Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 s‖ δ) * stripPoisson₀ θ s) +
        ∫ s, Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 s‖ δ) * stripPoisson₁ θ s) := by
  obtain ⟨T₀, _, hg₀⟩ := exists_abs_ge_norm_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 hδ
  obtain ⟨T₁, _, hg₁⟩ := exists_abs_ge_norm_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 hδ
  let T := max T₀ T₁
  let u₀ : ℝ → ℝ := fun s => Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 s‖ δ / δ)
  let u₁ : ℝ → ℝ := fun s => Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 s‖ δ / δ)
  have hg₀' (s : ℝ) (hs : T ≤ |s|) := hg₀ s ((le_max_left _ _).trans hs)
  have hg₁' (s : ℝ) (hs : T ≤ |s|) := hg₁ s ((le_max_right _ _).trans hs)
  have hu₀_props := continuous_and_hasCompactSupport_log_max_div _ hδ hg₀'
  have hu₁_props := continuous_and_hasCompactSupport_log_max_div _ hδ hg₁'
  have hu₀_cont : Continuous u₀ := hu₀_props.1
  have hu₀_supp : HasCompactSupport u₀ := hu₀_props.2
  have hu₁_cont : Continuous u₁ := hu₁_props.1
  have hu₁_supp : HasCompactSupport u₁ := hu₁_props.2
  have hmain := norm_mk_le_exp_re_holoPotential hθ hδ g hg₀' hg₁' hu₀_cont hu₁_cont
    (fun _ => Real.log_nonneg ((one_le_div hδ).2 (le_max_right _ _)))
    (fun _ => Real.log_nonneg ((one_le_div hδ).2 (le_max_right _ _))) hu₀_supp hu₁_supp
    (fun s => by
      dsimp only [u₀]
      rw [Real.log_div (lt_of_lt_of_le hδ (le_max_right _ _)).ne' hδ.ne']; ring)
    (fun s => by
      dsimp only [u₁]
      rw [Real.log_div (lt_of_lt_of_le hδ (le_max_right _ _)).ne' hδ.ne']; ring)
  refine hmain.trans_eq (congrArg Real.exp ?_)
  have hlogδ : Real.log δ =
      (∫ s, Real.log δ * stripPoisson₀ θ s) + ∫ s, Real.log δ * stripPoisson₁ θ s := by
    rw [integral_const_mul, integral_const_mul, integral_stripPoisson₀ ⟨hθ.1, hθ.2.le⟩,
      integral_stripPoisson₁ ⟨hθ.1.le, hθ.2⟩]
    ring
  have hcomb₀ : (∫ s, Real.log δ * stripPoisson₀ θ s) + (∫ s, u₀ s * stripPoisson₀ θ s) =
      ∫ s, Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 s‖ δ) * stripPoisson₀ θ s := by
    rw [← integral_add (f := fun s => Real.log δ * stripPoisson₀ θ s)
      (g := fun s => u₀ s * stripPoisson₀ θ s) ((integrable_stripPoisson₀ θ).const_mul _)
      (hu₀_cont.mul (continuous_stripPoisson₀ θ) |>.integrable_of_hasCompactSupport
        hu₀_supp.mul_right)]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    dsimp only [u₀]
    rw [← add_mul, Real.log_div (lt_of_lt_of_le hδ (le_max_right _ _)).ne' hδ.ne']
    ring
  have hcomb₁ : (∫ s, Real.log δ * stripPoisson₁ θ s) + (∫ s, u₁ s * stripPoisson₁ θ s) =
      ∫ s, Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 s‖ δ) * stripPoisson₁ θ s := by
    rw [← integral_add (f := fun s => Real.log δ * stripPoisson₁ θ s)
      (g := fun s => u₁ s * stripPoisson₁ θ s) ((integrable_stripPoisson₁ θ).const_mul _)
      (hu₁_cont.mul (continuous_stripPoisson₁ θ) |>.integrable_of_hasCompactSupport
        hu₁_supp.mul_right)]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    dsimp only [u₁]
    rw [← add_mul, Real.log_div (lt_of_lt_of_le hδ (le_max_right _ _)).ne' hδ.ne']
    ring
  linarith

private theorem exp_integral_log_mul_le_rpow {φ w : ℝ → ℝ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hw_int : Integrable w) (hw_nonneg : ∀ s, 0 ≤ w s) (hw_sum : ∫ s, w s = α)
    (hφ_ge : ∀ s, δ ≤ φ s) (hφ_int : Integrable (fun s => φ s * w s))
    (hlog_int : Integrable (fun s => Real.log (φ s) * w s)) :
    Real.exp (∫ s, Real.log (φ s) * w s) ≤ (α⁻¹ * ∫ s, φ s * w s) ^ α := by
  let I := α⁻¹ * ∫ s, φ s * w s
  have hI_pos : 0 < I := by
    have hle : ∫ s, δ * w s ≤ ∫ s, φ s * w s :=
      integral_mono (hw_int.const_mul δ) hφ_int fun s =>
        mul_le_mul_of_nonneg_right (hφ_ge s) (hw_nonneg s)
    rw [integral_const_mul, hw_sum] at hle
    exact hδ.trans_le ((show δ = α⁻¹ * (δ * α) by field_simp [hα.ne']).trans_le
      (mul_le_mul_of_nonneg_left hle (inv_pos.2 hα).le))
  have hpt (s : ℝ) :
      Real.log (φ s) * w s + (1 - Real.log I) * w s ≤ I⁻¹ * (φ s * w s) := by
    have h1 := Real.add_one_le_exp (Real.log (φ s) - Real.log I)
    rw [Real.exp_sub, Real.exp_log (hδ.trans_le (hφ_ge s)), Real.exp_log hI_pos] at h1
    calc Real.log (φ s) * w s + (1 - Real.log I) * w s
        = (Real.log (φ s) - Real.log I + 1) * w s := by ring
      _ ≤ (φ s / I) * w s := mul_le_mul_of_nonneg_right h1 (hw_nonneg s)
      _ = I⁻¹ * (φ s * w s) := by ring
  have hint := integral_mono
    (f := fun s => Real.log (φ s) * w s + (1 - Real.log I) * w s)
    (hlog_int.add (hw_int.const_mul (1 - Real.log I))) (hφ_int.const_mul I⁻¹) hpt
  rw [integral_add (f := fun s => Real.log (φ s) * w s)
    (g := fun s => (1 - Real.log I) * w s) hlog_int (hw_int.const_mul _),
    integral_const_mul, integral_const_mul, hw_sum] at hint
  have hI_cancel : I⁻¹ * ∫ s, φ s * w s = α := by
    have hdef : ∫ s, φ s * w s = α * I := by dsimp [I]; field_simp [hα.ne']
    rw [hdef]
    field_simp [hI_pos.ne']
  rw [hI_cancel] at hint
  rw [Real.rpow_def_of_pos hI_pos, mul_comm (Real.log I) α]
  exact Real.exp_le_exp.2 (by linarith)

private theorem exp_integral_log_max_le_rpow {E : Type*} [NormedAddCommGroup E] (f : C₀(ℝ, E))
    {w : ℝ → ℝ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hw_cont : Continuous w)
    (hw_int : Integrable w) (hw_nonneg : ∀ s, 0 ≤ w s) (hw_sum : ∫ s, w s = α) :
    Real.exp (∫ s, Real.log (max ‖f s‖ δ) * w s) ≤
      (α⁻¹ * (∫ s, ‖f s‖ * w s) + δ) ^ α := by
  have hf_int : Integrable (fun s => ‖f s‖ * w s) := by
    refine (hw_int.const_mul ‖f‖).mono'
      (((map_continuous f).norm.mul hw_cont).aestronglyMeasurable) (ae_of_all _ fun s => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hw_nonneg s))]
    exact mul_le_mul_of_nonneg_right (ZeroAtInftyContinuousMap.norm_coe_le_norm f s) (hw_nonneg s)
  have hmax_int : Integrable (fun s => max ‖f s‖ δ * w s) := by
    refine (hw_int.const_mul (max ‖f‖ δ)).mono'
      ((((map_continuous f).norm.max continuous_const).mul hw_cont).aestronglyMeasurable)
      (ae_of_all _ fun s => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hδ.le.trans (le_max_right _ _)) (hw_nonneg s))]
    exact mul_le_mul_of_nonneg_right
      (max_le_max (ZeroAtInftyContinuousMap.norm_coe_le_norm f s) le_rfl) (hw_nonneg s)
  have hlog_int : Integrable (fun s => Real.log (max ‖f s‖ δ) * w s) := by
    let B := max |Real.log δ| |Real.log (max ‖f‖ δ)|
    refine (hw_int.const_mul B).mono'
      ((((Continuous.log ((map_continuous f).norm.max continuous_const) fun _ =>
        (hδ.trans_le (le_max_right _ _)).ne').mul hw_cont)).aestronglyMeasurable)
      (ae_of_all _ fun s => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hw_nonneg s)]
    refine mul_le_mul_of_nonneg_right (abs_le.2 ⟨?_, ?_⟩) (hw_nonneg s)
    · linarith [Real.log_le_log hδ (le_max_right ‖f s‖ δ), neg_abs_le (Real.log δ),
        le_max_left |Real.log δ| |Real.log (max ‖f‖ δ)|]
    · exact (Real.log_le_log (hδ.trans_le (le_max_right _ _))
        (max_le_max (ZeroAtInftyContinuousMap.norm_coe_le_norm f s) le_rfl)).trans
        ((le_abs_self _).trans (le_max_right _ _))
  have hj := exp_integral_log_mul_le_rpow hα hδ hw_int hw_nonneg hw_sum
    (fun _ => le_max_right _ _) hmax_int hlog_int
  refine hj.trans (Real.rpow_le_rpow (mul_nonneg (inv_pos.2 hα).le
    (integral_nonneg fun s => mul_nonneg (hδ.le.trans (le_max_right _ _)) (hw_nonneg s))) ?_ hα.le)
  have hle : ∫ s, max ‖f s‖ δ * w s ≤ (∫ s, ‖f s‖ * w s) + δ * α := by
    rw [← hw_sum, ← integral_const_mul,
      ← integral_add (f := fun s => ‖f s‖ * w s) (g := fun s => δ * w s) hf_int
        (hw_int.const_mul δ)]
    exact integral_mono hmax_int (hf_int.add (hw_int.const_mul δ)) fun s =>
      (mul_le_mul_of_nonneg_right
        (max_le (le_add_of_nonneg_right hδ.le) (le_add_of_nonneg_left (norm_nonneg _)))
        (hw_nonneg s)).trans_eq (add_mul _ _ _)
  calc α⁻¹ * ∫ s, max ‖f s‖ δ * w s
      ≤ α⁻¹ * ((∫ s, ‖f s‖ * w s) + δ * α) := mul_le_mul_of_nonneg_left hle (inv_pos.2 hα).le
    _ = α⁻¹ * (∫ s, ‖f s‖ * w s) + δ := by field_simp [hα.ne']

/-- **Bergh–Löfström Lemma 4.3.2 (Stieltjes/Poisson log-convexity of the complex method norm).**
For `0 < θ < 1` and any admissible trace pair `g = (g₀, g₁)`, the quotient norm in `[X₀, X₁]_θ` is
bounded by the weighted geometric mean of the strip Poisson integrals of `‖g₀‖` and `‖g₁‖`. -/
theorem norm_mk_le_integral_stripPoisson {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (g : C.stripTraces) :
    ‖mk θ g‖ ≤
      ((1 - θ)⁻¹ * ∫ t, ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t‖ * stripPoisson₀ θ t) ^ (1 - θ) *
        (θ⁻¹ * ∫ t, ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t‖ * stripPoisson₁ θ t) ^ θ := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  let I₀ := (1 - θ)⁻¹ * ∫ t, ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t‖ * stripPoisson₀ θ t
  let I₁ := θ⁻¹ * ∫ t, ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t‖ * stripPoisson₁ θ t
  have htend : Tendsto (fun δ : ℝ => (I₀ + δ) ^ (1 - θ) * (I₁ + δ) ^ θ) (𝓝[>] 0)
      (𝓝 (I₀ ^ (1 - θ) * I₁ ^ θ)) := by
    have hc0 : Continuous (fun δ : ℝ => I₀ + δ) := by fun_prop
    have hc1 : Continuous (fun δ : ℝ => I₁ + δ) := by fun_prop
    have h0 : Tendsto (fun δ : ℝ => I₀ + δ) (𝓝[>] 0) (𝓝 I₀) := by
      simpa using (hc0.tendsto 0).mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun δ : ℝ => I₁ + δ) (𝓝[>] 0) (𝓝 I₁) := by
      simpa using (hc1.tendsto 0).mono_left nhdsWithin_le_nhds
    exact (h0.rpow_const (Or.inr h1θ.le)).mul (h1.rpow_const (Or.inr hθ.1.le))
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  calc ‖mk θ g‖
      ≤ Real.exp
          ((∫ s, Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 s‖ δ) * stripPoisson₀ θ s) +
            ∫ s, Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 s‖ δ) * stripPoisson₁ θ s) :=
        norm_mk_le_exp_integral_log_max_of_pos hθ hδ g
    _ = Real.exp (∫ s, Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 s‖ δ) * stripPoisson₀ θ s) *
          Real.exp (∫ s, Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 s‖ δ) * stripPoisson₁ θ s) :=
        Real.exp_add _ _
    _ ≤ (I₀ + δ) ^ (1 - θ) * (I₁ + δ) ^ θ :=
        mul_le_mul
          (exp_integral_log_max_le_rpow _ h1θ hδ (continuous_stripPoisson₀ θ)
            (integrable_stripPoisson₀ θ) (fun s => (stripPoisson₀_pos hθ s).le)
            (integral_stripPoisson₀ ⟨hθ.1, hθ.2.le⟩))
          (exp_integral_log_max_le_rpow _ hθ.1 hδ (continuous_stripPoisson₁ θ)
            (integrable_stripPoisson₁ θ) (fun s => (stripPoisson₁_pos hθ s).le)
            (integral_stripPoisson₁ ⟨hθ.1.le, hθ.2⟩))
          (Real.exp_nonneg _)
          (Real.rpow_nonneg (add_nonneg (mul_nonneg (inv_pos.2 h1θ).le
            (integral_nonneg fun s => mul_nonneg (norm_nonneg _)
              (stripPoisson₀_pos hθ s).le)) hδ.le) _)

end ComplexMethodSpace

end CompatibleCouple

end TauCeti
