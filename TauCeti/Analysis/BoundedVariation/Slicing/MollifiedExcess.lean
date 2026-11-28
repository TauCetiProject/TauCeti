/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import TauCeti.Analysis.BoundedVariation.Slicing.Excess
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Distribution.TestFunction.Convolution
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Trace
import TauCeti.Analysis.Real.Sqrt
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Mollified slicing excess inequality

When a finite-volume Lebesgue-measurable set `s` has finite perimeter, testing the localized
joint slicing inequality
(`TauCeti.two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter`)
against mollified regularized gradient vector fields for a radial smooth bump `ρ` on `(ℝ ∙ e)ᗮ`
and applying Cauchy–Schwarz yields the mollified slicing excess bound
(`MeasureTheory.NullMeasurableSet.mul_integral_sqrt_sq_add_norm_fderiv_sq_add_two_mul_sq_le`):
writing `D = {y ∈ H | 0 < |s_y|}`, `v(y) = |s_y|`, `d = ρ ⋆ (2 · 1_D)`, `w = ρ ⋆ v`,
`a = ρ ⋆ 1_A`, and `M = 2 |D| + |Dv|`,

`M ∫ √(d² + ‖Dw‖²) + 2 (∫ a √d)² ≤ M P(s)`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 and §3.11, for one-dimensional variation and slicing.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), §1.2, for the interval-section condition.
-/

public section

open ContinuousLinearMap Filter InnerProductSpace MeasureTheory Metric Set TestFunction
  TopologicalSpace
open scoped Convolution Distributions ENNReal Pointwise RealInnerProductSpace Topology

namespace TauCeti

section MollifiedExcess

noncomputable section

/-- Smoothness of the regularized gradient-density integrand `√(d² + ‖Dw‖² + δ²)`. -/
private theorem contDiff_sqrt_sq_add_norm_fderiv_sq_add_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    {d w : H → ℝ} (hd : ContDiff ℝ (⊤ : ℕ∞) d) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : H ↦ √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δ ^ 2)) := by
  let gradW : H → H := fun y ↦ (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ w y)
  have hgradW_smooth : ContDiff ℝ (⊤ : ℕ∞) gradW :=
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearMap.contDiff.comp
      (hw.fderiv_right (by simp))
  have hinner : ContDiff ℝ (⊤ : ℕ∞) fun y : H ↦ d y ^ 2 + ⟪gradW y, gradW y⟫_ℝ + δ ^ 2 :=
    ((hd.pow 2).add (hgradW_smooth.inner ℝ hgradW_smooth)).add contDiff_const
  have hrad : (fun y : H ↦ d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δ ^ 2) =
      fun y : H ↦ d y ^ 2 + ⟪gradW y, gradW y⟫_ℝ + δ ^ 2 :=
    funext fun y ↦ by rw [real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]
  rw [contDiff_iff_contDiffAt]
  exact fun y ↦ (Real.contDiffAt_sqrt (by positivity)).comp y (hrad ▸ hinner.contDiffAt)

/-- Mollification `ρ ⋆ (2 · 1_D)` of twice the indicator of the positive-section set `D`. -/
noncomputable abbrev mollD {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (s : Set E) (e : E) (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) : (ℝ ∙ e)ᗮ → ℝ :=
  ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
    {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}.indicator (fun _ ↦ (2 : ℝ))

/-- Mollification `ρ ⋆ v` of the real line-section length `v(y) = |s_y|`. -/
noncomputable abbrev mollW {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (s : Set E) (e : E) (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) : (ℝ ∙ e)ᗮ → ℝ :=
  ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
    (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})

/-- Mollification `ρ ⋆ 1_A` of the indicator of a transverse subset `A ⊆ (ℝ ∙ e)ᗮ`. -/
noncomputable abbrev mollA {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (e : E) (A : Set (ℝ ∙ e)ᗮ) (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) : (ℝ ∙ e)ᗮ → ℝ :=
  ρ.normed volume ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ ↦ (1 : ℝ))

private noncomputable abbrev mollGradW {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (s : Set E) (e : E) (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) : (ℝ ∙ e)ᗮ → (ℝ ∙ e)ᗮ :=
  fun y ↦ (InnerProductSpace.toDual ℝ (ℝ ∙ e)ᗮ).symm (fderiv ℝ (mollW s e ρ) y)

/-- Bundled measurability, finiteness, and integrability data for the line sections of `s` along
`e` and a noninterval section subset `A`. -/
structure MollifiedSetup {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (s : Set E) (e : E) (A : Set (ℝ ∙ e)ᗮ) : Prop where
  /-- The set of transverse points whose line sections have positive length is null-measurable. -/
  hD : NullMeasurableSet {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} volume
  /-- The set `A` of noninterval sections is null-measurable. -/
  hA : NullMeasurableSet A volume
  /-- The set of positive-length line sections has finite transverse measure. -/
  hDfin : volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} ≠ ∞
  /-- The family `A` of noninterval sections has finite transverse measure. -/
  hAfin : volume A ≠ ∞
  /-- Almost every point of `A` has positive line-section length. -/
  hAD : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
    y ∈ {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  /-- The section-length function has finite total variation on the hyperplane. -/
  hv_tv_fin : totalVariationOn volume ⊤
    (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}) ≠ ∞
  /-- The section-length function is integrable on the hyperplane. -/
  hv_int : Integrable (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}) volume
  /-- The weighted positive-section indicator `2 · 1_D` is integrable. -/
  hD_ind_int : Integrable
    ({y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}.indicator (fun _ ↦ (2 : ℝ))) volume
  /-- The noninterval indicator `1_A` is integrable. -/
  hA_ind_int : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) volume

namespace MollifiedSetup

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {s : Set E} {e : E} {A : Set (ℝ ∙ e)ᗮ} (S : MollifiedSetup s e A)
  (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ))
include S

/-- Smoothness of `mollD s e ρ`. -/
theorem d_smooth : ContDiff ℝ (⊤ : ℕ∞) (mollD s e ρ) :=
  ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ρ.contDiff_normed
    S.hD_ind_int.locallyIntegrable

/-- Smoothness of `mollW s e ρ`. -/
theorem w_smooth : ContDiff ℝ (⊤ : ℕ∞) (mollW s e ρ) :=
  ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ρ.contDiff_normed
    S.hv_int.locallyIntegrable

private theorem a_smooth : ContDiff ℝ (⊤ : ℕ∞) (mollA e A ρ) :=
  ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ρ.contDiff_normed
    S.hA_ind_int.locallyIntegrable

/-- Integrability of `mollD s e ρ`. -/
theorem d_int : Integrable (mollD s e ρ) volume :=
  ρ.integrable_normed.integrable_convolution _ S.hD_ind_int

/-- Integrability of `mollW s e ρ`. -/
theorem w_int : Integrable (mollW s e ρ) volume :=
  ρ.integrable_normed.integrable_convolution _ S.hv_int

private theorem a_int : Integrable (mollA e A ρ) volume :=
  ρ.integrable_normed.integrable_convolution _ S.hA_ind_int

/-- Pointwise `[0, 2]` bound for `mollD s e ρ`. -/
theorem d_mem (y : (ℝ ∙ e)ᗮ) : mollD s e ρ y ∈ Icc (0 : ℝ) 2 :=
  ρ.normed_convolution_indicator_mem_Icc zero_le_two S.hD_ind_int.locallyIntegrable y

private theorem a_mem (y : (ℝ ∙ e)ᗮ) : mollA e A ρ y ∈ Icc (0 : ℝ) 1 :=
  ρ.normed_convolution_indicator_mem_Icc zero_le_one S.hA_ind_int.locallyIntegrable y

private theorem d_int_eq : ∫ y : (ℝ ∙ e)ᗮ, mollD s e ρ y =
    2 * volume.real {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} := by
  rw [integral_convolution (lsmul ℝ ℝ) ρ.integrable_normed S.hD_ind_int, lsmul_apply,
    ρ.integral_normed, one_smul, integral_indicator₀ S.hD, setIntegral_const, smul_eq_mul,
    mul_comm]

private theorem a_int_eq : ∫ y : (ℝ ∙ e)ᗮ, mollA e A ρ y = volume.real A := by
  rw [integral_convolution (lsmul ℝ ℝ) ρ.integrable_normed S.hA_ind_int, lsmul_apply,
    ρ.integral_normed, one_smul, integral_indicator₀ S.hA, setIntegral_const, smul_eq_mul,
    mul_one]

private theorem gradW_smooth : ContDiff ℝ (⊤ : ℕ∞) (mollGradW s e ρ) :=
  (InnerProductSpace.toDual ℝ (ℝ ∙ e)ᗮ).symm.toContinuousLinearMap.contDiff.comp
    ((S.w_smooth ρ).fderiv_right (by simp))

private theorem gradW_cont : Continuous (fun y : (ℝ ∙ e)ᗮ ↦ ‖fderiv ℝ (mollW s e ρ) y‖) :=
  (((S.w_smooth ρ).of_le (by simp)).continuous_fderiv one_ne_zero).norm

/-- Integrability of `‖fderiv ℝ (mollW s e ρ) ·‖`. -/
theorem gradW_int : Integrable (fun y : (ℝ ∙ e)ᗮ ↦ ‖fderiv ℝ (mollW s e ρ) y‖) volume :=
  ρ.integrable_norm_fderiv_normed_convolution S.hv_int.locallyIntegrable S.hv_tv_fin

private theorem gradW_int_le : ∫ y : (ℝ ∙ e)ᗮ, ‖fderiv ℝ (mollW s e ρ) y‖ ≤
    (totalVariationOn volume ⊤
      (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})).toReal :=
  ρ.integral_norm_fderiv_normed_convolution_le S.hv_int.locallyIntegrable S.hv_tv_fin

end

/-- Pairing the `2 · 1_D` indicator with the mollification of `η * (d / g)` moves the bump onto
`2 · 1_D` to produce `∫ η * d² / g`. -/
private theorem pair_D {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} {e : E} {A : Set (ℝ ∙ e)ᗮ} (S : MollifiedSetup s e A)
    (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) (η : ContDiffBump (0 : (ℝ ∙ e)ᗮ))
    {g : (ℝ ∙ e)ᗮ → ℝ} (hg_cont : Continuous g) (hg_pos : ∀ y, 0 < g y)
    (hψ₀_mem : ∀ y, η y * (mollD s e ρ y / g y) ∈ Icc (0 : ℝ) 1) :
    ∫ y : (ℝ ∙ e)ᗮ,
        {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}.indicator (fun _ ↦ (2 : ℝ)) y *
          (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] (fun y ↦ η y * (mollD s e ρ y / g y))) y =
      ∫ y : (ℝ ∙ e)ᗮ, η y * mollD s e ρ y ^ 2 / g y := by
  have hcont : Continuous fun y ↦ η y * (mollD s e ρ y / g y) :=
    η.continuous.mul ((S.d_smooth ρ).continuous.div hg_cont fun y ↦ (hg_pos y).ne')
  rw [ρ.integral_mul_normed_convolution_eq_of_bdd S.hD_ind_int hcont.aestronglyMeasurable
    (C := 1) fun y ↦ by rw [Real.norm_of_nonneg (hψ₀_mem y).1]; exact (hψ₀_mem y).2]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  ring

/-- Pairing the `1_A` indicator with the mollification of `d / g` moves the bump onto `1_A` to
produce `∫ a * (d / g)`. -/
private theorem pair_A {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} {e : E} {A : Set (ℝ ∙ e)ᗮ} (S : MollifiedSetup s e A)
    (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) {g : (ℝ ∙ e)ᗮ → ℝ}
    (hdg_cont : Continuous (fun y ↦ mollD s e ρ y / g y))
    (hdg_mem : ∀ y, mollD s e ρ y / g y ∈ Icc (0 : ℝ) 1) :
    ∫ y : (ℝ ∙ e)ᗮ, A.indicator (fun _ ↦ (1 : ℝ)) y *
        (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] (fun y ↦ mollD s e ρ y / g y)) y =
      ∫ y : (ℝ ∙ e)ᗮ, mollA e A ρ y * (mollD s e ρ y / g y) :=
  ρ.integral_mul_normed_convolution_eq_of_bdd S.hA_ind_int hdg_cont.aestronglyMeasurable
    (C := 1) fun y ↦ by rw [Real.norm_of_nonneg (hdg_mem y).1]; exact (hdg_mem y).2

/-- Pairing `div (ρ ⋆ φ₀)` against `v` moves the mollifier onto `v` and integrates by parts
against `w = ρ ⋆ v`, yielding `∫ η * ‖Dw‖² / g`. -/
private theorem pair_div {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} {e : E} {A : Set (ℝ ∙ e)ᗮ} (S : MollifiedSetup s e A)
    (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) (η : ContDiffBump (0 : (ℝ ∙ e)ᗮ))
    {g : (ℝ ∙ e)ᗮ → ℝ} (φ₀ : 𝓓(⊤, (ℝ ∙ e)ᗮ))
    (hφ₀_apply : ∀ y, φ₀ y = (-(η y * (g y)⁻¹)) • mollGradW s e ρ y) :
    ∫ y : (ℝ ∙ e)ᗮ,
        divergenceCLM (TestFunction.mollify φ₀ volume ρ (subset_univ _)) y *
          volume.real {t : ℝ | (y : E) + t • e ∈ s} =
      ∫ y : (ℝ ∙ e)ᗮ, η y * ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2 / g y := by
  let H := (ℝ ∙ e)ᗮ
  let v : H → ℝ := fun y ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}
  obtain ⟨C, hC⟩ := (divergenceCLM φ₀).continuous.bounded_above_of_compact_support
    (divergenceCLM φ₀).hasCompactSupport
  have h1 : ∫ y : H,
        divergenceCLM (TestFunction.mollify φ₀ volume ρ (subset_univ _)) y * v y =
      ∫ y : H, v y * (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] (divergenceCLM φ₀ : H → ℝ)) y :=
    integral_congr_ae (.of_forall fun y ↦ by
      dsimp only; rw [mul_comm, divergenceCLM_mollify])
  have h2 : ∀ y : H, mollW s e ρ y * (divergenceCLM φ₀) y =
      (divergenceCLM φ₀) y • mollW s e ρ y := fun y ↦ by rw [mul_comm, smul_eq_mul]
  rw [h1, ρ.integral_mul_normed_convolution_eq_of_bdd S.hv_int
    (divergenceCLM φ₀).continuous.aestronglyMeasurable hC,
    integral_congr_ae (.of_forall h2),
    (((S.w_smooth ρ).of_le (by simp)).contDiffOn.hasWeakFDerivOn_fderiv
      (μ := volume) (Ω := ⊤)).integral_divergenceCLM_smul_eq_neg_integral φ₀,
    ← integral_neg]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  dsimp only
  rw [(InnerProductSpace.toDual_symm_apply (y := fderiv ℝ (mollW s e ρ) y) (x := φ₀ y)).symm,
    hφ₀_apply y]
  dsimp only [mollGradW]
  rw [inner_smul_right, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map, div_eq_mul_inv]
  ring

/-- Bounded-test pairing for the regularized slicing estimate against a compactly supported
cutoff `η` on `(ℝ ∙ e)ᗮ`. -/
private theorem integral_cutoff_mul_div_sqrt_add_two_mul_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) {e : E} (he : ‖e‖ = 1)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (S : MollifiedSetup s e A) (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ))
    (η : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) {δ : ℝ} (hδ : 0 < δ) :
    let g : (ℝ ∙ e)ᗮ → ℝ := fun y ↦ √(mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2 + δ ^ 2)
    (∫ y : (ℝ ∙ e)ᗮ, η y * (mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2) / g y) +
        2 * (∫ y : (ℝ ∙ e)ᗮ, mollA e A ρ y * (mollD s e ρ y / g y)) ≤
      (perimeter volume ⊤ s).toReal := by
  intro g
  let H := (ℝ ∙ e)ᗮ
  let D : Set H := {y : H | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  let κ : H → ℝ := ρ.normed volume
  have hg_pos (y : H) : 0 < g y := Real.sqrt_pos.2 (by positivity)
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    contDiff_sqrt_sq_add_norm_fderiv_sq_add_sq (S.d_smooth ρ) (S.w_smooth ρ) hδ
  have hdg_mem (y : H) : mollD s e ρ y / g y ∈ Icc (0 : ℝ) 1 :=
    Real.div_sqrt_sq_add_sq_add_sq_mem_Icc (S.d_mem ρ y).1 ‖fderiv ℝ (mollW s e ρ) y‖ δ
  -- Build the regularized test field `φ₀ = -η / g • gradW` and its scalar companion `ψ₀ = η d / g`.
  let ψ₀ : H → ℝ := fun y ↦ η y * (mollD s e ρ y / g y)
  let φ₀_fun : H → H := fun y ↦ (-(η y * (g y)⁻¹)) • mollGradW s e ρ y
  let φ₀ : 𝓓(⊤, H) := ⟨φ₀_fun,
    ((η.contDiff.mul (hg_smooth.inv fun y ↦ (hg_pos y).ne')).neg).smul (S.gradW_smooth ρ),
    (η.hasCompactSupport.mul_right.neg).smul_right, subset_univ _⟩
  have hφ₀_apply (y : H) : φ₀ y = (-(η y * (g y)⁻¹)) • mollGradW s e ρ y := by
    simp only [φ₀, φ₀_fun, TestFunction.coe_mk]
  let φ : 𝓓(⊤, H) := TestFunction.mollify φ₀ volume ρ (subset_univ _)
  let ψ : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] ψ₀
  let α : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] (fun y ↦ mollD s e ρ y / g y)
  have hdg_cont : Continuous (fun y : H ↦ mollD s e ρ y / g y) :=
    (S.d_smooth ρ).continuous.div hg_smooth.continuous fun y ↦ (hg_pos y).ne'
  have hψ₀_cont : Continuous ψ₀ := η.continuous.mul hdg_cont
  have hψ₀_mem (y : H) : ψ₀ y ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg η.nonneg (hdg_mem y).1,
      (mul_le_mul η.le_one (hdg_mem y).2 (hdg_mem y).1 zero_le_one).trans_eq (one_mul 1)⟩
  -- Pointwise norm bounds: `(d/g)² + ‖φ₀‖² ≤ 1` and `ψ₀² + ‖φ₀‖² ≤ 1`, hence `‖φ‖ ≤ 1`.
  have hsq_α (y : H) : (mollD s e ρ y / g y) ^ 2 + ‖φ₀ y‖ ^ 2 ≤ 1 := by
    have hnorm : ‖φ₀ y‖ = η y * ‖fderiv ℝ (mollW s e ρ) y‖ / g y := by
      rw [hφ₀_apply, norm_smul, norm_neg,
        Real.norm_of_nonneg (mul_nonneg η.nonneg (inv_nonneg.2 (hg_pos y).le)),
        LinearIsometryEquiv.norm_map, div_eq_mul_inv]
      ring
    rw [hnorm, div_pow, div_pow, mul_pow, ← add_div, div_le_one (sq_pos_of_pos (hg_pos y)),
      Real.sq_sqrt (by positivity)]
    have hη1 : η y ^ 2 ≤ 1 := by nlinarith [η.nonneg (x := y), η.le_one (x := y)]
    nlinarith [sq_nonneg ‖fderiv ℝ (mollW s e ρ) y‖, sq_nonneg δ]
  have hsq_ψ (y : H) : ψ₀ y ^ 2 + ‖φ₀ y‖ ^ 2 ≤ 1 := by
    have hψle : ψ₀ y ^ 2 ≤ (mollD s e ρ y / g y) ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _)
        (by nlinarith [η.nonneg (x := y), η.le_one (x := y)])
    exact (add_le_add hψle le_rfl).trans (hsq_α y)
  have hφ_le (y : H) : ‖φ y‖ ≤ 1 := by
    rw [TestFunction.mollify_apply]
    exact ρ.norm_normed_convolution_le (.of_forall fun z ↦ by
      nlinarith [hsq_α z, sq_nonneg (mollD s e ρ z / g z), norm_nonneg (φ₀ z)]) y
  -- Pair the mollified fields against the localized joint slicing inequality.
  have hpair_D := S.pair_D ρ η hg_smooth.continuous hg_pos hψ₀_mem
  have hpair_A := S.pair_A ρ hdg_cont hdg_mem
  have hpair_div := S.pair_div ρ η φ₀ hφ₀_apply
  have htermD : ENNReal.ofReal (∫ y : H, D.indicator (fun _ ↦ (2 : ℝ)) y * ψ y) ≤
      2 * ∫⁻ y in D, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
    simpa only [ENNReal.ofReal_ofNat, φ, ψ, TestFunction.mollify_apply] using
      ρ.ofReal_integral_indicator_mul_convolution_le φ₀.continuous S.hD zero_le_two S.hD_ind_int
        hψ₀_cont hψ₀_mem hsq_ψ
  have htermA : ENNReal.ofReal (2 * ∫ y : H, A.indicator (fun _ ↦ (1 : ℝ)) y * α y) ≤
      2 * ∫⁻ y in A, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
    rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
    refine mul_le_mul_right ?_ 2
    simpa only [ENNReal.ofReal_one, one_mul, φ, α, TestFunction.mollify_apply] using
      ρ.ofReal_integral_indicator_mul_convolution_le φ₀.continuous hA zero_le_one S.hA_ind_int
        hdg_cont hdg_mem hsq_α
  -- Split `∫ η (d² + ‖Dw‖²) / g` into its two integrable summands and conclude.
  have hI1 : Integrable (fun y : H ↦ η y * mollD s e ρ y ^ 2 / g y) volume :=
    (S.d_int ρ).mono' (((η.continuous.mul ((S.d_smooth ρ).continuous.pow 2)).div
      hg_smooth.continuous fun y ↦ (hg_pos y).ne').aestronglyMeasurable) (.of_forall fun y ↦ by
        have hfac : η y * mollD s e ρ y ^ 2 / g y = ψ₀ y * mollD s e ρ y := by
          dsimp only [ψ₀]; ring
        rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg η.nonneg (sq_nonneg _)) (hg_pos y).le),
          hfac]
        exact mul_le_of_le_one_left (S.d_mem ρ y).1 (hψ₀_mem y).2)
  have hI2 : Integrable (fun y : H ↦ η y * ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2 / g y) volume :=
    (S.gradW_int ρ).mono' (((η.continuous.mul ((S.gradW_cont ρ).pow 2)).div
      hg_smooth.continuous fun y ↦ (hg_pos y).ne').aestronglyMeasurable) (.of_forall fun y ↦ by
        have hfac : η y * ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2 / g y =
            (η y * (‖fderiv ℝ (mollW s e ρ) y‖ / g y)) * ‖fderiv ℝ (mollW s e ρ) y‖ := by ring
        rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg η.nonneg (sq_nonneg _)) (hg_pos y).le),
          hfac]
        have hle1 : ‖fderiv ℝ (mollW s e ρ) y‖ / g y ≤ 1 := by
          simpa only [add_comm (‖fderiv ℝ (mollW s e ρ) y‖ ^ 2)] using
            (Real.div_sqrt_sq_add_sq_add_sq_mem_Icc (opNorm_nonneg (fderiv ℝ (mollW s e ρ) y))
              (mollD s e ρ y) δ).2
        exact mul_le_of_le_one_left (opNorm_nonneg _)
          ((mul_le_mul η.le_one hle1 (div_nonneg (opNorm_nonneg _) (hg_pos y).le)
            zero_le_one).trans_eq (one_mul 1)))
  have hsplit : (∫ y : H, η y * (mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2) / g y) =
      (∫ y : H, η y * mollD s e ρ y ^ 2 / g y) +
        ∫ y : H, η y * ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2 / g y := by
    rw [← integral_add hI1 hI2]
    exact integral_congr_ae (.of_forall fun _ ↦ by ring)
  rw [hsplit]
  refine (ENNReal.ofReal_le_iff_le_toReal hP).1 ?_
  rw [add_right_comm]
  exact (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)).trans <| by
    rw [← hpair_D, ← hpair_A, ← hpair_div]
    exact (add_le_add (add_le_add htermD htermA) le_rfl).trans
      (two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
        hs hfin e he hA hbad φ hφ_le)

/-- Regularized (`δ > 0`) mollified slicing excess inequality, obtained by exhausting `(ℝ ∙ e)ᗮ`
with radial cutoff bumps and applying Cauchy–Schwarz to `∫ a √d`. -/
private theorem mul_integral_reg_add_two_mul_sq_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) {e : E} (he : ‖e‖ = 1)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (S : MollifiedSetup s e A) (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ))
    {δ : ℝ} (hδ : 0 < δ) :
    let H := (ℝ ∙ e)ᗮ
    let D : Set H := {y : H | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
    let v : H → ℝ := fun y ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}
    let Mδ : ℝ := 2 * volume.real D + (totalVariationOn volume ⊤ v).toReal + δ * volume.real A
    let g : H → ℝ := fun y ↦ √(mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2 + δ ^ 2)
    Mδ * (∫ y : H, (mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2) / g y) +
        2 * (∫ y : H, mollA e A ρ y * √(mollD s e ρ y)) ^ 2 ≤
      Mδ * (perimeter volume ⊤ s).toReal := by
  intro H D v Mδ g
  have hg_pos (y : H) : 0 < g y := Real.sqrt_pos.2 (by positivity)
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    contDiff_sqrt_sq_add_norm_fderiv_sq_add_sq (S.d_smooth ρ) (S.w_smooth ρ) hδ
  -- Exhaust `H` with bumps `ηseq m ↑ 1` by dominated convergence.
  let ηseq : ℕ → ContDiffBump (0 : H) := fun m ↦
    ⟨(m : ℝ) + 1, (m : ℝ) + 2, by positivity, by linarith⟩
  have hη_lim : Tendsto
      (fun m ↦ ∫ y : H, ηseq m y * (mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2) / g y)
      atTop (𝓝 (∫ y : H, (mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2) / g y)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y ↦ mollD s e ρ y + ‖fderiv ℝ (mollW s e ρ) y‖)
      (fun m ↦ (((ηseq m).continuous.mul (((S.d_smooth ρ).continuous.pow 2).add
        ((S.gradW_cont ρ).pow 2))).div hg_smooth.continuous
        fun y ↦ (hg_pos y).ne').aestronglyMeasurable)
      ((S.d_int ρ).add (S.gradW_int ρ)) (fun m ↦ .of_forall fun y ↦ ?_) (.of_forall fun y ↦ ?_)
    · have hq0 : 0 ≤ (mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2) / g y :=
        div_nonneg (by positivity) (hg_pos y).le
      rw [mul_div_assoc, Real.norm_of_nonneg (mul_nonneg (ηseq m).nonneg hq0)]
      refine (mul_le_of_le_one_left hq0 (ηseq m).le_one).trans ?_
      simpa only [abs_of_nonneg (S.d_mem ρ y).1, abs_of_nonneg (opNorm_nonneg _)] using
        Real.div_sqrt_sq_add_sq_add_le (mollD s e ρ y) ‖fderiv ℝ (mollW s e ρ) y‖ (sq_nonneg δ)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (Nat.ceil ‖y‖)] with m hm
      have hball : y ∈ closedBall (0 : H) (ηseq m).rIn := by
        rw [mem_closedBall_zero_iff]
        have h1 : ‖y‖ ≤ (m : ℝ) := (Nat.le_ceil ‖y‖).trans (Nat.cast_le.2 hm)
        dsimp only [ηseq]; linarith
      rw [(ηseq m).one_of_mem_closedBall hball, one_mul]
  have heta (m : ℕ) :
      (∫ y : H, ηseq m y * (mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2) / g y) +
        2 * (∫ y : H, mollA e A ρ y * (mollD s e ρ y / g y)) ≤ (perimeter volume ⊤ s).toReal :=
    S.integral_cutoff_mul_div_sqrt_add_two_mul_le hs hfin hP he hA hbad ρ (ηseq m) hδ
  have hfull : (∫ y : H, (mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2) / g y) +
      2 * (∫ y : H, mollA e A ρ y * (mollD s e ρ y / g y)) ≤ (perimeter volume ⊤ s).toReal :=
    le_of_tendsto (hη_lim.add tendsto_const_nhds) (.of_forall heta)
  -- Bound `∫ a g ≤ Mδ` and apply Cauchy–Schwarz to `(∫ a √d)² ≤ (∫ a (d/g)) (∫ a g)`.
  have hle_M : (∫ y : H, mollD s e ρ y) + (∫ y : H, ‖fderiv ℝ (mollW s e ρ) y‖) +
      δ * ∫ y : H, mollA e A ρ y ≤ Mδ := by
    rw [S.d_int_eq ρ, S.a_int_eq ρ]; dsimp only [Mδ]; linarith [S.gradW_int_le ρ]
  have hadg_int : Integrable (fun y : H ↦ mollA e A ρ y * (mollD s e ρ y / g y)) volume :=
    (S.a_int ρ).mul_bdd (c := 1) ((S.d_smooth ρ).continuous.div hg_smooth.continuous
      fun y ↦ (hg_pos y).ne').aestronglyMeasurable
      (.of_forall fun y ↦ by
        have hm := Real.div_sqrt_sq_add_sq_add_sq_mem_Icc (S.d_mem ρ y).1
          ‖fderiv ℝ (mollW s e ρ) y‖ δ
        rw [Real.norm_of_nonneg hm.1]; exact hm.2)
  have hdg_int : Integrable (fun y : H ↦ mollD s e ρ y + ‖fderiv ℝ (mollW s e ρ) y‖) volume :=
    (S.d_int ρ).add (S.gradW_int ρ)
  have hag_pt (y : H) :
      mollA e A ρ y * g y ≤ mollD s e ρ y + ‖fderiv ℝ (mollW s e ρ) y‖ + δ * mollA e A ρ y := by
    have hg_le : g y ≤ mollD s e ρ y + ‖fderiv ℝ (mollW s e ρ) y‖ + δ := by
      simpa only [abs_of_nonneg (S.d_mem ρ y).1, abs_of_nonneg (opNorm_nonneg _), abs_of_pos hδ]
        using Real.sqrt_sq_add_sq_add_sq_le (mollD s e ρ y) ‖fderiv ℝ (mollW s e ρ) y‖ δ
    nlinarith [mul_le_mul_of_nonneg_left hg_le (S.a_mem ρ y).1, (S.a_mem ρ y).2, (S.d_mem ρ y).1,
      opNorm_nonneg (fderiv ℝ (mollW s e ρ) y)]
  have hag_int : Integrable (fun y : H ↦ mollA e A ρ y * g y) volume :=
    (hdg_int.add ((S.a_int ρ).const_mul δ)).mono'
      ((S.a_smooth ρ).continuous.mul hg_smooth.continuous).aestronglyMeasurable
      (.of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (S.a_mem ρ y).1 (hg_pos y).le)]; exact hag_pt y)
  have hag_le : ∫ y : H, mollA e A ρ y * g y ≤ Mδ := by
    calc ∫ y : H, mollA e A ρ y * g y
        ≤ ∫ y : H, (mollD s e ρ y + ‖fderiv ℝ (mollW s e ρ) y‖ + δ * mollA e A ρ y) :=
          integral_mono hag_int (hdg_int.add ((S.a_int ρ).const_mul δ)) hag_pt
      _ = (∫ y : H, mollD s e ρ y) + (∫ y : H, ‖fderiv ℝ (mollW s e ρ) y‖) +
            δ * ∫ y : H, mollA e A ρ y := by
          rw [integral_add hdg_int ((S.a_int ρ).const_mul δ),
            integral_add (S.d_int ρ) (S.gradW_int ρ), integral_const_mul]
      _ ≤ Mδ := hle_M
  have hcs := TauCeti.sq_integral_mul_sqrt_le_integral_mul_div_mul
    (.of_forall fun y ↦ (S.a_mem ρ y).1) (.of_forall fun y ↦ (S.d_mem ρ y).1)
    (.of_forall hg_pos) hadg_int hag_int
  have hcs' : (∫ y : H, mollA e A ρ y * √(mollD s e ρ y)) ^ 2 ≤
      (∫ y : H, mollA e A ρ y * (mollD s e ρ y / g y)) * Mδ :=
    hcs.trans (mul_le_mul_of_nonneg_left hag_le (integral_nonneg fun y ↦
      mul_nonneg (S.a_mem ρ y).1
        (Real.div_sqrt_sq_add_sq_add_sq_mem_Icc (S.d_mem ρ y).1
          ‖fderiv ℝ (mollW s e ρ) y‖ δ).1))
  have hMδ_nonneg : 0 ≤ Mδ := by dsimp [Mδ]; positivity
  nlinarith [mul_le_mul_of_nonneg_left hfull hMδ_nonneg]

end MollifiedSetup

end

end MollifiedExcess

end TauCeti

namespace MeasureTheory.NullMeasurableSet

open TauCeti

/-- Construct the bundled slicing setup from finite volume, finite perimeter, and noninterval
section hypotheses. -/
theorem mkMollifiedSetup {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) {e : E} (he : ‖e‖ = 1)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    MollifiedSetup s e A :=
  let H := (ℝ ∙ e)ᗮ
  let D : Set H := {y : H | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  let v : H → ℝ := fun y ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}
  have hD : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hDfin : volume D ≠ ∞ := hs.volume_setOf_pos_volume_lineSection_ne_top hfin hP e he
  have hAfin : volume A ≠ ∞ := hs.volume_ne_top_of_noninterval_lineSection hfin hP e he hA hbad
  have hv_tv_fin : totalVariationOn volume ⊤ v ≠ ∞ :=
    ne_top_of_le_ne_top hP (totalVariationOn_measureReal_lineSection_le hs hfin e he)
  have hv_int : Integrable v volume := hs.integrable_measureReal_lineSection hfin e he
  { hD, hA, hDfin, hAfin, hv_tv_fin, hv_int
    hAD := by
      filter_upwards [hbad] with y hy hyA
      by_contra hyD
      exact hy hyA ∅ ordConnected_empty (ae_eq_empty.2 (nonpos_iff_eq_zero.1 (not_lt.1 hyD)))
    hD_ind_int := (integrableOn_const hDfin).integrable_indicator₀ hD
    hA_ind_int := (integrableOn_const hAfin).integrable_indicator₀ hA }

/-- **Mollified slicing excess inequality.** Let `s` be a Lebesgue-measurable set of finite volume
and finite perimeter, `e` a unit vector with orthogonal hyperplane `H = (ℝ ∙ e)ᗮ`, `A ⊆ H` a
null-measurable family of noninterval line sections of `s`, and `ρ` a radial smooth bump on `H`.
Writing `D = {y ∈ H | 0 < |s_y|}`, `v(y) = |s_y|`, `d = ρ ⋆ (2 · 1_D)`, `w = ρ ⋆ v`,
`a = ρ ⋆ 1_A`, and `M = 2 |D| + |Dv|`, we have

`M ∫ √(d² + ‖Dw‖²) + 2 (∫ a √d)² ≤ M P(s)`. -/
theorem mul_integral_sqrt_sq_add_norm_fderiv_sq_add_two_mul_sq_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) (e : E) (he : ‖e‖ = 1)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) :
    (2 * volume.real {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} +
        (totalVariationOn volume ⊤
          (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})).toReal) *
      (∫ y : (ℝ ∙ e)ᗮ,
        √((ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
            {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}.indicator
              (fun _ ↦ (2 : ℝ))) y ^ 2 +
          ‖fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
            (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})) y‖ ^ 2)) +
      2 * (∫ y : (ℝ ∙ e)ᗮ,
        (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ ↦ (1 : ℝ))) y *
          √((ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
            {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}.indicator
              (fun _ ↦ (2 : ℝ))) y)) ^ 2 ≤
    (2 * volume.real {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} +
        (totalVariationOn volume ⊤
          (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})).toReal) *
      (perimeter volume ⊤ s).toReal := by
  let H := (ℝ ∙ e)ᗮ
  let D : Set H := {y : H | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  let v : H → ℝ := fun y ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let M : ℝ := 2 * volume.real D + (totalVariationOn volume ⊤ v).toReal
  have S := hs.mkMollifiedSetup hfin hP he hA hbad
  -- Pass `δ = 1 / (k + 1) → 0⁺` in the regularized estimate by dominated convergence.
  let δseq : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hδpos (k : ℕ) : 0 < δseq k := by positivity
  have hδlim : Tendsto δseq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hM_lim : Tendsto (fun k ↦ M + δseq k * volume.real A) atTop (𝓝 M) := by
    simpa only [zero_mul, add_zero] using (hδlim.mul_const (volume.real A)).const_add M
  have hint_lim : Tendsto
      (fun k ↦ ∫ y : H, (mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2) /
        √(mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2 + δseq k ^ 2))
      atTop (𝓝 (∫ y : H, √(mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y ↦ mollD s e ρ y + ‖fderiv ℝ (mollW s e ρ) y‖)
      (fun k ↦ ((((S.d_smooth ρ).continuous.pow 2).add
        ((((S.w_smooth ρ).of_le (by simp)).continuous_fderiv one_ne_zero).norm.pow 2)).div
        (Real.continuous_sqrt.comp ((((S.d_smooth ρ).continuous.pow 2).add
          ((((S.w_smooth ρ).of_le (by simp)).continuous_fderiv one_ne_zero).norm.pow 2)).add
          continuous_const)) fun y ↦ (Real.sqrt_pos.2
            (add_pos_of_nonneg_of_pos (add_nonneg (sq_nonneg _) (sq_nonneg _))
              (sq_pos_of_pos (hδpos k)))).ne').aestronglyMeasurable)
      ((S.d_int ρ).add (S.gradW_int ρ))
      (fun k ↦ .of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        simpa only [abs_of_nonneg (S.d_mem ρ y).1, abs_of_nonneg (opNorm_nonneg _)] using
          Real.div_sqrt_sq_add_sq_add_le (mollD s e ρ y) ‖fderiv ℝ (mollW s e ρ) y‖
            (sq_nonneg (δseq k)))
      (.of_forall fun y ↦ ?_)
    set x : ℝ := mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2
    have hx_nonneg : 0 ≤ x := by positivity
    rcases eq_or_lt_of_le hx_nonneg with hx0 | hxpos
    · simp [← hx0]
    · have hden : Tendsto (fun k ↦ √(x + δseq k ^ 2)) atTop (𝓝 √x) :=
        (Real.continuous_sqrt.tendsto x).comp <| by
          simpa only [zero_pow two_ne_zero, add_zero] using (hδlim.pow 2).const_add x
      have hq := (tendsto_const_nhds (x := x)).div hden (Real.sqrt_pos.2 hxpos).ne'
      rwa [Real.div_sqrt] at hq
  exact le_of_tendsto_of_tendsto ((hM_lim.mul hint_lim).add tendsto_const_nhds)
    (hM_lim.mul_const (perimeter volume ⊤ s).toReal)
    (.of_forall fun k ↦ S.mul_integral_reg_add_two_mul_sq_le hs hfin hP he hA hbad ρ (hδpos k))

end MeasureTheory.NullMeasurableSet
