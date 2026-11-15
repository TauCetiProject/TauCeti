/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import TauCeti.Analysis.BoundedVariation.PolarDecomposition
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.WithDensity
import TauCeti.Analysis.Distribution.AELeOfIntegral
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Lebesgue decomposition of the BV derivative

For a locally integrable function of locally finite variation, write `Du = σ |Du|` using
`polarDensity`. Relative to a σ-finite reference measure `ν` on the open domain, the absolutely
continuous part of `Du` has density `acDerivativeDensity μ Ω u ν = (d|Du|/dν) σ`. The remaining
part is `σ (|Du|.singularPart ν)`. We prove the distributional identity for their sum and the
splitting of the variation measure, including local integrability of the density. Taking
`ν = μ.comap Subtype.val` gives the usual absolutely continuous/singular decomposition on the
domain. No global finiteness of `|Du|` or integrability of `u` is required.

The variation measure satisfies
`|Du| = ν.withDensity (fun x => ‖acDerivativeDensity μ Ω u ν x‖ₑ) + |Du|.singularPart ν`
(`withDensity_enorm_acDerivativeDensity_add_singularPart`). The second measure is mutually
singular to `ν` by Mathlib's `Measure.mutuallySingular_singularPart`. The distributional
identity describes the derivative through its action on test fields; no globally finite
vector measure is imposed on an unbounded domain. The density is unique `ν`-almost everywhere
among locally integrable densities in such a decomposition (`ae_eq_acDerivativeDensity`),
including when the competing singular reference measure is not σ-finite.

Convolving a locally integrable `u` with a compactly supported `C¹` kernel `ρ` separates the two
parts pointwise (`fderiv_convolution_lsmul_apply_eq`): at any `y` with `y - tsupport ρ ⊆ Ω`,
`fderiv (ρ ⋆ u) y` is the sum of the `ρ`-mollified absolutely continuous derivative and the
`ρ`-mollified singular derivative. When `ρ` is nonnegative, the operator norm of `fderiv (ρ ⋆ u) y`
is therefore bounded by `(ρ ⋆ ‖acDerivativeDensity‖) y` plus the integral of `ρ (y - ·)` against
`|Du|.singularPart ν` (`norm_fderiv_convolution_lsmul_le`,
`norm_fderiv_convolution_lsmul_top_le`).

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1 (Lebesgue decomposition of the derivative).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace TestFunction Set
open scoped Convolution ENNReal Distributions RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {u : E → ℝ}

/-- The density of the absolutely continuous part of `Du` relative to `ν` on `Ω`.
It is the Radon–Nikodym density of `|Du|` multiplied by its polar field. -/
def acDerivativeDensity (μ : Measure E) (Ω : Opens E) (u : E → ℝ) (ν : Measure Ω) : Ω → E :=
  fun x => ((variationMeasure μ Ω u).rnDeriv ν x).toReal • polarDensity μ Ω u x

/-- The defining formula for the absolutely continuous derivative density. -/
theorem acDerivativeDensity_def (ν : Measure Ω) (x : Ω) :
    acDerivativeDensity μ Ω u ν x =
      ((variationMeasure μ Ω u).rnDeriv ν x).toReal • polarDensity μ Ω u x := (rfl)

/-- The absolutely continuous derivative density is measurable. -/
@[fun_prop]
theorem measurable_acDerivativeDensity (ν : Measure Ω) :
    Measurable (acDerivativeDensity μ Ω u ν) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal.smul measurable_polarDensity

variable (hu : LocallyIntegrableOn u Ω μ)
  (hfin : ∀ K, IsCompact K → K ⊆ Ω →
    ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
  (ν : Measure Ω)

include hu hfin

/-- The norm of the absolutely continuous derivative density is exactly `d|Du|/dν`,
including where this Radon–Nikodym derivative vanishes. -/
theorem ae_enorm_acDerivativeDensity_eq_rnDeriv :
    (fun x => ‖acDerivativeDensity μ Ω u ν x‖ₑ) =ᵐ[ν]
      (variationMeasure μ Ω u).rnDeriv ν := by
  have := Ω.isOpen.locallyCompactSpace
  have hnorm := Measure.ae_rnDeriv_eq_zero_of_measure_eq_zero (ν := ν)
    (ae_iff.1 (ae_norm_polarDensity_eq_one hu hfin))
  filter_upwards [hnorm, Measure.rnDeriv_ne_top (variationMeasure μ Ω u) ν] with x hx htop
  rw [acDerivativeDensity_def, eNorm_smul, Real.eNorm_eq_ofReal
    ENNReal.toReal_nonneg, ENNReal.ofReal_toReal htop]
  by_cases hzero : (variationMeasure μ Ω u).rnDeriv ν x = 0
  · simp [hzero]
  · rw [← ofReal_norm, not_imp_comm.mp hx hzero, ENNReal.ofReal_one, mul_one]

/-- The variation measure splits into the norm of the absolutely continuous derivative
and the singular variation measure. The latter is mutually singular to `ν`. -/
theorem withDensity_enorm_acDerivativeDensity_add_singularPart [SigmaFinite ν] :
    ν.withDensity (fun x => ‖acDerivativeDensity μ Ω u ν x‖ₑ) +
      (variationMeasure μ Ω u).singularPart ν = variationMeasure μ Ω u := by
  have := Ω.isOpen.locallyCompactSpace
  rw [withDensity_congr_ae (ae_enorm_acDerivativeDensity_eq_rnDeriv hu hfin ν)]
  exact Measure.rnDeriv_add_singularPart _ _

/-- On every subset, variation is the integral of the norm of the absolutely continuous
derivative plus the singular variation, as an extended-valued identity. -/
theorem lintegral_enorm_acDerivativeDensity_add_singularPart [SigmaFinite ν] (s : Set Ω) :
    (∫⁻ x in s, ‖acDerivativeDensity μ Ω u ν x‖ₑ ∂ν) +
      (variationMeasure μ Ω u).singularPart ν s = variationMeasure μ Ω u s := by
  have h := congrArg (fun m : Measure Ω => m s)
    (withDensity_enorm_acDerivativeDensity_add_singularPart hu hfin ν)
  simpa only [_root_.add_apply, withDensity_apply'] using h

/-- The absolutely continuous derivative density is locally integrable even when the
whole derivative has infinite variation. -/
theorem locallyIntegrable_acDerivativeDensity :
    LocallyIntegrable (acDerivativeDensity μ Ω u ν) ν := by
  have := Ω.isOpen.locallyCompactSpace
  refine locallyIntegrable_iff.2 fun K hK =>
    ⟨(measurable_acDerivativeDensity ν).aestronglyMeasurable.restrict, ?_⟩
  apply hasFiniteIntegral_iff_eNorm.mpr
  rw [lintegral_congr_ae (ae_restrict_of_ae (ae_enorm_acDerivativeDensity_eq_rnDeriv hu hfin ν))]
  exact (Measure.setLIntegral_rnDeriv_le K).trans_lt hK.measure_lt_top

omit hfin in
/-- Finite total variation implies integrability of the absolutely continuous derivative
density. Global integrability of the original function is not required. -/
theorem integrable_acDerivativeDensity (hvar : totalVariationOn μ Ω u ≠ ∞) :
    Integrable (acDerivativeDensity μ Ω u ν) ν := by
  have := Ω.isOpen.locallyCompactSpace
  have hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞ :=
    fun _ _ hK => ⟨Ω, hK, hvar⟩
  refine ⟨(measurable_acDerivativeDensity ν).aestronglyMeasurable, ?_⟩
  apply hasFiniteIntegral_iff_eNorm.mpr
  rw [lintegral_congr_ae (ae_enorm_acDerivativeDensity_eq_rnDeriv hu hfin ν)]
  have hmass : variationMeasure μ Ω u univ < ∞ := by
    rw [variationMeasure_univ hu hfin]
    exact hvar.lt_top
  exact Measure.lintegral_rnDeriv_le.trans_lt hmass

/-- **Lebesgue decomposition of the BV derivative.** The distributional derivative is the sum
of the density `acDerivativeDensity μ Ω u ν` against `ν` and the polar field against the singular
part of `|Du|`. Both pairings are integrable because the test field has compact support. -/
theorem integral_divergenceCLM_mul_eq_neg_integral_inner_acDerivativeDensity_sub_singularPart
    [SigmaFinite ν] (φ : 𝓓(Ω, E)) :
    ∫ x, divergenceCLM φ x * u x ∂μ =
      -(∫ x, ⟪φ x, acDerivativeDensity μ Ω u ν x⟫ ∂ν) -
        ∫ x : Ω, ⟪φ x, polarDensity μ Ω u x⟫ ∂(variationMeasure μ Ω u).singularPart ν := by
  have := Ω.isOpen.locallyCompactSpace
  let lam := variationMeasure μ Ω u
  have hint := φ.integrable_inner_subtype
    (locallyIntegrable_polarDensity (μ := μ) (Ω := Ω) (u := u))
  have hac := hint.mono_measure (Measure.withDensity_rnDeriv_le lam ν)
  have hsing := hint.mono_measure (Measure.singularPart_le lam ν)
  have hsplit := congrArg
    (fun m : Measure Ω => ∫ x : Ω, ⟪φ x, polarDensity μ Ω u x⟫ ∂m)
    (Measure.rnDeriv_add_singularPart lam ν)
  rw [integral_add_measure hac hsing,
    integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top lam ν)] at hsplit
  rw [integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity hu hfin, ← hsplit]
  simp only [acDerivativeDensity_def, inner_smul_right, smul_eq_mul, neg_add, sub_eq_add_neg, lam]

/-- **Uniqueness of the absolutely continuous derivative density.** Any locally integrable
`g` representing `Du` together with a locally integrable density against a measure singular
to `ν` agrees with `acDerivativeDensity` at `ν`-almost every point. -/
theorem ae_eq_acDerivativeDensity [SigmaFinite ν] {g τ : Ω → E} {ξ : Measure Ω}
    (hg : LocallyIntegrable g ν) (hτ : LocallyIntegrable τ ξ) (hξ : ξ ⟂ₘ ν)
    (h : ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ =
      -(∫ x, ⟪φ x, g x⟫ ∂ν) - ∫ x : Ω, ⟪φ x, τ x⟫ ∂ξ) :
    g =ᵐ[ν] acDerivativeDensity μ Ω u ν := by
  have := Ω.isOpen.locallyCompactSpace
  let ω := (variationMeasure μ Ω u).singularPart ν
  have hσ : LocallyIntegrable (polarDensity μ Ω u) ω :=
    (locallyIntegrable_polarDensity (μ := μ) (Ω := Ω) (u := u)).mono_measure
      (Measure.singularPart_le _ _)
  -- The norms of the two singular densities give a locally finite dominating measure,
  -- even when the candidate singular reference measure itself is not σ-finite.
  let η := ξ.withDensity (fun x => ‖τ x‖ₑ) +
    ω.withDensity (fun x => ‖polarDensity μ Ω u x‖ₑ)
  have : IsFiniteMeasureOnCompacts η := ⟨fun K hK => by
    simp only [η, _root_.add_apply, withDensity_apply _ hK.measurableSet]
    exact ENNReal.add_lt_top.2
      ⟨hasFiniteIntegral_iff_eNorm.1 (hτ.integrableOn_isCompact hK).2,
        hasFiniteIntegral_iff_eNorm.1 (hσ.integrableOn_isCompact hK).2⟩⟩
  have hην : η ⟂ₘ ν :=
    (hξ.mono_ac (withDensity_absolutelyContinuous _ _) Measure.AbsolutelyContinuous.rfl).add_left
      ((Measure.mutuallySingular_singularPart _ _).mono_ac
        (withDensity_absolutelyContinuous _ _) Measure.AbsolutelyContinuous.rfl)
  let ρ := ν + η
  have hνρ : ν ≪ ρ := Measure.AbsolutelyContinuous.rfl.add_right _
  have hηρ : η ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  -- Transfer the difference of the absolutely continuous densities to the common measure.
  let f := fun x => (ν.rnDeriv ρ x).toReal • (g x - acDerivativeDensity μ Ω u ν x)
  have hg' := hg.sub (locallyIntegrable_acDerivativeDensity hu hfin ν)
  have := Ω.isOpen.locallyCompactSpace
  have hf : LocallyIntegrable f ρ := locallyIntegrable_toReal_rnDeriv_smul hνρ hg'
  have hle := ae_enorm_le_of_forall_enorm_integral_inner_le hf
    (Measure.measurable_rnDeriv η ρ)
    (fun K hK => ne_top_of_le_ne_top hK.measure_lt_top.ne (Measure.setLIntegral_rnDeriv_le K))
    fun U _ φ hφU hφ => by
      -- Bound each singular pairing by its norm measure on the support of the test field.
      have heq : ∫ x : Ω, ⟪φ x, f x⟫ ∂ρ =
          (∫ x : Ω, ⟪φ x, polarDensity μ Ω u x⟫ ∂ω) - ∫ x : Ω, ⟪φ x, τ x⟫ ∂ξ := by
        simp only [f, inner_smul_right, inner_sub_right]
        rw [integral_toReal_rnDeriv_mul hνρ,
          integral_sub (φ.integrable_inner_subtype hg)
            (φ.integrable_inner_subtype (locallyIntegrable_acDerivativeDensity hu hfin ν))]
        have h₁ := h φ
        have h₂ :=
          integral_divergenceCLM_mul_eq_neg_integral_inner_acDerivativeDensity_sub_singularPart
            hu hfin ν φ
        linarith
      rw [heq, Measure.setLIntegral_rnDeriv hηρ]
      exact eNorm_sub_le.trans (by
        simpa only [η, _root_.add_apply, add_comm] using add_le_add
          (TestFunction.enorm_integral_inner_le_withDensity U.isOpen.measurableSet hφU hφ ω
            (polarDensity μ Ω u))
          (TestFunction.enorm_integral_inner_le_withDensity U.isOpen.measurableSet hφU hφ ξ τ))
  -- The singular bound vanishes ν-a.e., while the density of ν in ρ is positive there.
  filter_upwards [hνρ.ae_le hle, Measure.rnDeriv_eq_zero_of_mutuallySingular hην hνρ,
    Measure.rnDeriv_pos hνρ, hνρ.ae_le (Measure.rnDeriv_ne_top ν ρ)] with x hx hz hp ht
  have hc : (ν.rnDeriv ρ x).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp.ne', ht⟩
  simpa [hz, f, smul_eq_zero, hc, sub_eq_zero] using hx

omit hu hfin in
/-- The absolutely continuous derivative density is unchanged almost everywhere if the
original function is changed on a null subset of its domain. -/
theorem acDerivativeDensity_congr_ae {v : E → ℝ} (h : u =ᵐ[μ.restrict Ω] v) :
    acDerivativeDensity μ Ω u ν =ᵐ[ν] acDerivativeDensity μ Ω v ν := by
  have hlam := variationMeasure_congr_ae h
  have hpolar := Measure.ae_rnDeriv_eq_zero_of_measure_eq_zero (ν := ν)
    (ae_iff.1 (polarDensity_congr_ae h))
  filter_upwards [hpolar] with x hx
  rw [acDerivativeDensity_def, acDerivativeDensity_def, ← hlam]
  by_cases hzero : (variationMeasure μ Ω u).rnDeriv ν x = 0
  · simp [hzero]
  · rw [not_imp_comm.mp hx hzero]

omit hu in
/-- **Derivative of a mollification via the BV Lebesgue decomposition.** Let `u` be locally
integrable on `E` with locally finite variation on `Ω`, and let `ρ : E → ℝ` be `C¹` with compact
support. At any `y` with `y - tsupport ρ ⊆ Ω`, the directional derivative of `ρ ⋆ u` along `v`
splits into the `ρ`-weighted integrals of `⟪v, acDerivativeDensity⟫` against `ν` and of
`⟪v, polarDensity⟫` against the singular variation measure. -/
theorem fderiv_convolution_lsmul_apply_eq [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    [SigmaFinite ν] (hu_loc : LocallyIntegrable u μ) {ρ : E → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hρc : HasCompactSupport ρ) {y : E} (hy : ∀ t ∈ tsupport ρ, y - t ∈ Ω) (v : E) :
    (fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) y) v =
      (∫ x : Ω, ρ (y - x) * ⟪v, acDerivativeDensity μ Ω u ν x⟫ ∂ν) +
        ∫ x : Ω, ρ (y - x) * ⟪v, polarDensity μ Ω u x⟫
          ∂(variationMeasure μ Ω u).singularPart ν := by
  have := Ω.isOpen.locallyCompactSpace
  have huΩ : LocallyIntegrableOn u Ω μ := hu_loc.locallyIntegrableOn Ω
  let L0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hce := (hρc.fderiv ℝ).convolutionExists_left
    (L0.precompL E :) (hρ.continuous_fderiv one_ne_zero) hu_loc y
  have hconv : (fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) y) v =
      ∫ z, fderiv ℝ ρ (y - z) v * u z ∂μ := by
    rw [(hρc.hasFDerivAt_convolution_left L0 hρ hu_loc y).fderiv,
      convolution_def, ContinuousLinearMap.integral_apply hce]
    simp only [L0, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [← integral_sub_left_eq_self _ μ y]
    simp_rw [sub_sub_self]
  -- Test the `C¹` polar decomposition against `z ↦ -ρ(y - z) • v` (divergence `Dρ(y - z) v`).
  set K : Set E := (fun t => y - t) '' tsupport ρ
  have hK : IsCompact K := hρc.isCompact.image (continuous_const.sub continuous_id)
  have hKΩ : K ⊆ Ω := by rintro _ ⟨t, ht, rfl⟩; exact hy t ht
  set Ψ : E → E := fun z => ρ (y - z) • v
  have hΨ0 (z : E) (hz : z ∉ K) : Ψ z = 0 := by
    have hzt : y - z ∉ tsupport ρ := fun h => hz ⟨y - z, h, sub_sub_cancel y z⟩
    simp [Ψ, image_eq_zero_of_notMem_tsupport hzt]
  have hΨc : HasCompactSupport Ψ := HasCompactSupport.intro hK hΨ0
  have hΨΩ : tsupport Ψ ⊆ Ω :=
    (closure_minimal (Function.support_subset_iff'.2 hΨ0) hK.isClosed).trans hKΩ
  have hΨ1 : ContDiff ℝ 1 Ψ := (hρ.comp (contDiff_const.sub contDiff_id)).smul contDiff_const
  have htr (z : E) : LinearMap.trace ℝ E (fderiv ℝ (-Ψ) z : E →ₗ[ℝ] E) =
      fderiv ℝ ρ (y - z) v := by
    set χ : E → ℝ := fun z => -ρ (y - z)
    have hχd : HasFDerivAt χ (fderiv ℝ ρ (y - z)) z := by
      have h1 : HasFDerivAt (fun z => y - z) (-ContinuousLinearMap.id ℝ E) z :=
        (hasFDerivAt_id z).const_sub y
      exact (((hρ.differentiable one_ne_zero) (y - z)).hasFDerivAt.comp z h1).neg.congr_fderiv
        (by ext w; simp)
    have hneg : (-Ψ) = fun z => χ z • v := by ext w; simp [Ψ, χ]
    rw [hneg, trace_fderiv_smul_const hχd.differentiableAt v, hχd.fderiv]
  have hibp : ∫ z, fderiv ℝ ρ (y - z) v * u z ∂μ =
      ∫ x : Ω, ⟪Ψ x, polarDensity μ Ω u x⟫ ∂variationMeasure μ Ω u := by
    have h0 := integral_trace_fderiv_mul_eq_neg_integral_inner_polarDensity (φ := -Ψ) huΩ hfin
      hΨ1.neg hΨc.neg (tsupport_neg Ψ ▸ hΨΩ)
    simp_rw [htr] at h0
    simp only [Pi.neg_apply, inner_neg_left, integral_neg, neg_neg] at h0
    exact h0
  -- Split `|Du|` into its `ν`-absolutely continuous part and its `ν`-singular part.
  let lam := variationMeasure μ Ω u
  have hint := integrable_inner_polarDensity (μ := μ) (Ω := Ω) (u := u) hΨ1.continuous hΨc hΨΩ
  have hac := hint.mono_measure (Measure.withDensity_rnDeriv_le lam ν)
  have hsing := hint.mono_measure (Measure.singularPart_le lam ν)
  have hsplit := congrArg
    (fun m : Measure Ω => ∫ x : Ω, ⟪Ψ x, polarDensity μ Ω u x⟫ ∂m)
    (Measure.rnDeriv_add_singularPart lam ν)
  rw [integral_add_measure hac hsing,
    integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top lam ν)] at hsplit
  rw [hconv, hibp, ← hsplit]
  simp only [Ψ, acDerivativeDensity_def, real_inner_smul_left, inner_smul_right, smul_eq_mul,
    mul_left_comm, lam]

omit hu in
/-- **Pointwise gradient bound for a nonnegative mollification.** For a nonnegative compactly
supported `C¹` kernel `ρ` and `y - tsupport ρ ⊆ Ω`, the norm of `fderiv (ρ ⋆ u) y` is bounded by
the `ρ`-weighted integral of `‖acDerivativeDensity‖` against `ν` plus the integral of `ρ (y - ·)`
against `|Du|.singularPart ν`. -/
theorem norm_fderiv_convolution_lsmul_le [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    [SigmaFinite ν] (hu_loc : LocallyIntegrable u μ) {ρ : E → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hρc : HasCompactSupport ρ) (hρ0 : ∀ t, 0 ≤ ρ t) {y : E} (hy : ∀ t ∈ tsupport ρ, y - t ∈ Ω) :
    ‖fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) y‖ ≤
      (∫ x : Ω, ρ (y - x) * ‖acDerivativeDensity μ Ω u ν x‖ ∂ν) +
        ∫ x : Ω, ρ (y - x) ∂(variationMeasure μ Ω u).singularPart ν := by
  have := Ω.isOpen.locallyCompactSpace
  have huΩ : LocallyIntegrableOn u Ω μ := hu_loc.locallyIntegrableOn Ω
  let ω := (variationMeasure μ Ω u).singularPart ν
  have : IsFiniteMeasureOnCompacts ω :=
    ⟨fun C hC => (Measure.singularPart_le _ _ C).trans_lt hC.measure_lt_top⟩
  set K : Set E := (fun t => y - t) '' tsupport ρ
  have hK : IsCompact K := hρc.isCompact.image (continuous_const.sub continuous_id)
  have hKΩ : K ⊆ Ω := by rintro _ ⟨t, ht, rfl⟩; exact hy t ht
  have hKsub : IsCompact (((↑) : Ω → E) ⁻¹' K) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK (by simpa using hKΩ)
  have hρsub : HasCompactSupport (fun x : Ω => ρ (y - x)) :=
    HasCompactSupport.intro hKsub fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx ⟨y - x, h, sub_sub_cancel y x⟩
  have hρcont : Continuous (fun x : Ω => ρ (y - x)) :=
    hρ.continuous.comp (continuous_const.sub continuous_subtype_val)
  have hint_vec : Integrable (fun x : Ω => ρ (y - x) • acDerivativeDensity μ Ω u ν x) ν :=
    (locallyIntegrable_acDerivativeDensity huΩ hfin ν).integrable_smul_left_of_hasCompactSupport
      hρcont hρsub
  have hint_ac : Integrable (fun x : Ω => ρ (y - x) * ‖acDerivativeDensity μ Ω u ν x‖) ν :=
    hint_vec.norm.congr (.of_forall fun x => by simp [norm_smul, Real.norm_of_nonneg (hρ0 _)])
  have hint_s : Integrable (fun x : Ω => ρ (y - x)) ω :=
    hρcont.integrable_of_hasCompactSupport hρsub
  refine ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (integral_nonneg fun x => mul_nonneg (hρ0 _) (norm_nonneg _))
      (integral_nonneg fun x => hρ0 _)) fun v => ?_
  rw [fderiv_convolution_lsmul_apply_eq hfin ν hu_loc hρ hρc hy v]
  have hb1 : ‖∫ x : Ω, ρ (y - x) * ⟪v, acDerivativeDensity μ Ω u ν x⟫ ∂ν‖ ≤
      (∫ x : Ω, ρ (y - x) * ‖acDerivativeDensity μ Ω u ν x‖ ∂ν) * ‖v‖ := by
    rw [← integral_mul_const]
    refine norm_integral_le_of_norm_le (hint_ac.mul_const ‖v‖) (.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hρ0 _), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((norm_inner_le_norm _ _).trans_eq (mul_comm _ _)) (hρ0 _)
  have hb2 : ‖∫ x : Ω, ρ (y - x) * ⟪v, polarDensity μ Ω u x⟫ ∂ω‖ ≤
      (∫ x : Ω, ρ (y - x) ∂ω) * ‖v‖ := by
    rw [← integral_mul_const]
    refine norm_integral_le_of_norm_le (hint_s.mul_const ‖v‖) ?_
    filter_upwards [ae_mono (Measure.singularPart_le _ _) (ae_norm_polarDensity_eq_one huΩ hfin)]
      with x hx
    rw [norm_mul, Real.norm_of_nonneg (hρ0 _)]
    exact mul_le_mul_of_nonneg_left
      ((norm_inner_le_norm _ _).trans (by rw [hx, mul_one])) (hρ0 _)
  calc ‖(∫ x : Ω, ρ (y - x) * ⟪v, acDerivativeDensity μ Ω u ν x⟫ ∂ν) +
        ∫ x : Ω, ρ (y - x) * ⟪v, polarDensity μ Ω u x⟫ ∂ω‖
      ≤ ‖∫ x : Ω, ρ (y - x) * ⟪v, acDerivativeDensity μ Ω u ν x⟫ ∂ν‖ +
        ‖∫ x : Ω, ρ (y - x) * ⟪v, polarDensity μ Ω u x⟫ ∂ω‖ := norm_add_le _ _
    _ ≤ (∫ x : Ω, ρ (y - x) * ‖acDerivativeDensity μ Ω u ν x‖ ∂ν) * ‖v‖ +
        (∫ x : Ω, ρ (y - x) ∂ω) * ‖v‖ := add_le_add hb1 hb2
    _ = ((∫ x : Ω, ρ (y - x) * ‖acDerivativeDensity μ Ω u ν x‖ ∂ν) +
        ∫ x : Ω, ρ (y - x) ∂ω) * ‖v‖ := (add_mul _ _ _).symm

omit hu hfin in
/-- **Whole-space gradient bound for a nonnegative mollification.** When `u` has locally finite
variation on `E`, `‖fderiv (ρ ⋆ u) y‖` is bounded by `(ρ ⋆ ‖g‖) y` plus the integral of
`ρ (y - ·)` against the singular variation measure, where `g` is the `μ`-absolutely continuous
derivative density of `u`. -/
theorem norm_fderiv_convolution_lsmul_top_le [SigmaFinite μ] [μ.IsAddLeftInvariant]
    [μ.IsNegInvariant] (hu_loc : LocallyIntegrable u μ)
    (hfin_top : ∀ K : Set E, IsCompact K → K ⊆ (⊤ : Opens E) →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    {ρ : E → ℝ} (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (y : E) :
    let ν : Measure (⊤ : Opens E) := μ.comap Subtype.val
    ‖fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) y‖ ≤
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
        fun z => ‖acDerivativeDensity μ ⊤ u ν ⟨z, Opens.mem_top z⟩‖) y +
        ∫ x : (⊤ : Opens E), ρ (y - x) ∂(variationMeasure μ ⊤ u).singularPart ν := by
  intro ν
  let e : E ≃ᵐ (⊤ : Opens E) :=
    { toFun := fun x => ⟨x, Opens.mem_top x⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      measurable_toFun := measurable_id.subtype_mk
      measurable_invFun := measurable_subtype_coe }
  have hν : ν = μ.map e := MeasurableEquiv.comap_symm e
  have : SigmaFinite ν := hν ▸ e.sigmaFinite_map
  have hm : MeasurableEmbedding (Subtype.val : (⊤ : Opens E) → E) := e.symm.measurableEmbedding
  have hmp : MeasurePreserving (Subtype.val : (⊤ : Opens E) → E) ν μ :=
    ⟨measurable_subtype_coe,
      by rw [hm.map_comap, Subtype.range_coe, Opens.coe_top, Measure.restrict_univ]⟩
  refine (norm_fderiv_convolution_lsmul_le (Ω := ⊤) hfin_top ν hu_loc hρ hρc hρ0
    fun _ _ => Opens.mem_top _).trans_eq ?_
  congr 1
  have hcomp := hmp.integral_comp hm
    (fun z => ρ (y - z) * ‖acDerivativeDensity μ ⊤ u ν ⟨z, Opens.mem_top z⟩‖)
  refine hcomp.trans ?_
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub_left_eq_self _ μ y]
  simp_rw [sub_sub_self]

end TauCeti
