/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.PolarDecomposition
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TauCeti.Analysis.Distribution.TestFunction.Integral
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Lebesgue decomposition of the BV derivative

For a locally integrable function of locally finite variation, write `Du = σ |Du|` using
`polarDensity`. Relative to a σ-finite reference measure `ν` on the open domain, the absolutely
continuous part of `Du` has density `acDerivativeDensity μ Ω u ν = (d|Du|/dν) σ`. The remaining
part is `σ (|Du|.singularPart ν)`. We prove the distributional identity for their sum and the
exact splitting of variation, including local integrability of the density. Taking
`ν = μ.comap Subtype.val` gives the usual absolutely continuous/singular decomposition on the
domain. No global finiteness of `|Du|` or integrability of `u` is required.

The singular part uses Mathlib's `Measure.singularPart`, which is mutually singular to `ν`.
The polar field still has norm one almost everywhere for that measure, since it is dominated
by `|Du|`. Thus the splitting has no cancellation: the variation of the absolutely continuous
part is `‖acDerivativeDensity μ Ω u ν‖ ν` and the remaining variation is precisely
`|Du|.singularPart ν`. These statements describe the derivative through its action on test
fields; no globally finite vector measure is imposed on an unbounded domain.

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
theorem ae_enorm_acDerivativeDensity :
    (fun x => ‖acDerivativeDensity μ Ω u ν x‖ₑ) =ᵐ[ν]
      (variationMeasure μ Ω u).rnDeriv ν := by
  have := Ω.isOpen.locallyCompactSpace
  have hnorm := (ae_norm_polarDensity_eq_one hu hfin).filter_mono
    (Measure.absolutelyContinuous_of_le (Measure.withDensity_rnDeriv_le
      (variationMeasure μ Ω u) ν)).ae_le
  rw [ae_withDensity_iff (Measure.measurable_rnDeriv _ _)] at hnorm
  filter_upwards [hnorm, Measure.rnDeriv_ne_top (variationMeasure μ Ω u) ν] with x hx htop
  rw [acDerivativeDensity_def, enorm_smul, Real.enorm_eq_ofReal
    ENNReal.toReal_nonneg, ENNReal.ofReal_toReal htop]
  by_cases hzero : (variationMeasure μ Ω u).rnDeriv ν x = 0
  · simp [hzero]
  · rw [← ofReal_norm, hx hzero, ENNReal.ofReal_one, mul_one]

/-- The variation measure splits into the norm of the absolutely continuous derivative
and the singular variation measure. The latter is mutually singular to `ν`. -/
theorem withDensity_enorm_acDerivativeDensity_add_singularPart [SigmaFinite ν] :
    ν.withDensity (fun x => ‖acDerivativeDensity μ Ω u ν x‖ₑ) +
      (variationMeasure μ Ω u).singularPart ν = variationMeasure μ Ω u := by
  have := Ω.isOpen.locallyCompactSpace
  rw [withDensity_congr_ae (ae_enorm_acDerivativeDensity hu hfin ν)]
  exact Measure.rnDeriv_add_singularPart _ _

/-- On every subset, variation is the integral of the norm of the absolutely continuous
derivative plus the singular variation, as an extended-valued identity. -/
theorem lintegral_enorm_acDerivativeDensity_add_singularPart [SigmaFinite ν] (s : Set Ω) :
    (∫⁻ x in s, ‖acDerivativeDensity μ Ω u ν x‖ₑ ∂ν) +
      (variationMeasure μ Ω u).singularPart ν s = variationMeasure μ Ω u s := by
  have h := congrArg (fun m : Measure Ω => m s)
    (withDensity_enorm_acDerivativeDensity_add_singularPart hu hfin ν)
  simpa only [Measure.add_apply, withDensity_apply'] using h

/-- The absolutely continuous derivative density is locally integrable even when the
whole derivative has infinite variation. -/
theorem locallyIntegrable_acDerivativeDensity :
    LocallyIntegrable (acDerivativeDensity μ Ω u ν) ν := by
  have := Ω.isOpen.locallyCompactSpace
  refine locallyIntegrable_iff.2 fun K hK =>
    ⟨(measurable_acDerivativeDensity ν).aestronglyMeasurable.restrict, ?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  rw [lintegral_congr_ae (ae_restrict_of_ae (ae_enorm_acDerivativeDensity hu hfin ν))]
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
  rw [lintegral_congr_ae (ae_enorm_acDerivativeDensity hu hfin ν)]
  have hmass : variationMeasure μ Ω u univ < ∞ := by
    rw [variationMeasure_univ hu hfin]
    exact hvar.lt_top
  exact Measure.lintegral_rnDeriv_le.trans_lt hmass

/-- **Lebesgue decomposition of the BV derivative.** The distributional derivative is the sum
of the density `acDerivativeDensity μ Ω u ν` against `ν` and the polar field against the singular
part of `|Du|`. Both pairings are integrable because the test field has compact support. -/
theorem integral_divergenceCLM_mul_eq_neg_add_singularPart [SigmaFinite ν] (φ : 𝓓(Ω, E)) :
    ∫ x, divergenceCLM φ x * u x ∂μ =
      -(∫ x, ⟪φ x, acDerivativeDensity μ Ω u ν x⟫ ∂ν) -
        ∫ x : Ω, ⟪φ x, polarDensity μ Ω u x⟫ ∂(variationMeasure μ Ω u).singularPart ν := by
  have := Ω.isOpen.locallyCompactSpace
  let lam := variationMeasure μ Ω u
  have hint : Integrable (fun x : Ω => ⟪φ x, polarDensity μ Ω u x⟫) lam := by
    exact (φ.integrable_bilin_subtype (innerSL ℝ)
      (locallyIntegrable_polarDensity hu hfin)).congr
        (ae_of_all _ fun x => innerSL_apply_apply ℝ _ _)
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

omit hu hfin in
/-- The absolutely continuous derivative density is unchanged almost everywhere if the
original function is changed on a null subset of its domain. -/
theorem acDerivativeDensity_congr_ae {v : E → ℝ} (h : u =ᵐ[μ.restrict Ω] v) :
    acDerivativeDensity μ Ω u ν =ᵐ[ν] acDerivativeDensity μ Ω v ν := by
  have hlam := variationMeasure_congr_ae h
  have hpolar := (polarDensity_congr_ae h).filter_mono
    (Measure.absolutelyContinuous_of_le (Measure.withDensity_rnDeriv_le
      (variationMeasure μ Ω u) ν)).ae_le
  simp only [Filter.EventuallyEq, ae_withDensity_iff (Measure.measurable_rnDeriv _ _)] at hpolar
  filter_upwards [hpolar] with x hx
  rw [acDerivativeDensity_def, acDerivativeDensity_def, ← hlam]
  by_cases hzero : (variationMeasure μ Ω u).rnDeriv ν x = 0
  · simp [hzero]
  · rw [hx hzero]

end TauCeti
