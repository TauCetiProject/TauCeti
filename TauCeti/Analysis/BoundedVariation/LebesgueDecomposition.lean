/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.PolarDecomposition
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TauCeti.Analysis.Distribution.AELeOfIntegral
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.WithDensity

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

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1 (Lebesgue decomposition of the derivative).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace TestFunction Set
open scoped ENNReal Distributions RealInnerProductSpace

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
  rw [acDerivativeDensity_def, enorm_smul, Real.enorm_eq_ofReal
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
  apply hasFiniteIntegral_iff_enorm.mpr
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
  apply hasFiniteIntegral_iff_enorm.mpr
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
  have hint := φ.integrable_inner_subtype (locallyIntegrable_polarDensity hu hfin)
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
    (locallyIntegrable_polarDensity hu hfin).mono_measure (Measure.singularPart_le _ _)
  -- The norms of the two singular densities give a locally finite dominating measure,
  -- even when the candidate singular reference measure itself is not σ-finite.
  let η := ξ.withDensity (fun x => ‖τ x‖ₑ) +
    ω.withDensity (fun x => ‖polarDensity μ Ω u x‖ₑ)
  have : IsFiniteMeasureOnCompacts η := ⟨fun K hK => by
    simp only [η, _root_.add_apply, withDensity_apply _ hK.measurableSet]
    exact ENNReal.add_lt_top.2
      ⟨hasFiniteIntegral_iff_enorm.1 (hτ.integrableOn_isCompact hK).2,
        hasFiniteIntegral_iff_enorm.1 (hσ.integrableOn_isCompact hK).2⟩⟩
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
    fun U hU φ hφU hφ => by
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
      exact enorm_sub_le.trans (by
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

end TauCeti
