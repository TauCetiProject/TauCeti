/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.PolarDecomposition
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Weak convergence of BV derivative measures

The derivative of a locally BV function is represented by its polar density against its
variation measure. Local `L¹` convergence, together with locally uniformly bounded variation
measures, implies convergence of these derivatives against every continuous vector field
compactly supported in the domain. Neither the domain nor the total variations need be bounded.
This is vague (local weak-*) convergence of the vector derivative measures, not convergence of
their total variations.

The proof first tests the distributional identity against smooth fields, then uses uniform
approximation with a fixed compact support to pass to continuous fields. The accompanying
integrability and distance estimates make the continuous-field pairings available without
assuming global finiteness of the derivative measures.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1 (weak-* convergence in BV).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace TestFunction Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace Distributions BoundedContinuousFunction

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E}

/-- Distributional convergence of locally BV functions with locally uniformly bounded variation
measures implies convergence of their derivative measures against continuous compactly supported
fields. The measures may have infinite mass on the whole domain. -/
theorem tendsto_integral_inner_polarDensity_of_tendsto_testFunction
    {ι : Type*} {l : Filter ι} {v : ι → E → ℝ} {u : E → ℝ}
    (hv : ∀ i, LocallyIntegrableOn (v i) Ω μ)
    (hvfin : ∀ i K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (v i) ≠ ∞)
    (hu : LocallyIntegrableOn u Ω μ)
    (hufin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    (hbound : ∀ K, IsCompact K → K ⊆ Ω → ∃ C : ℝ,
      ∀ᶠ i in l, (variationMeasure μ Ω (v i)).real (((↑) : Ω → E) ⁻¹' K) ≤ C)
    (hconv : ∀ ψ : 𝓓(Ω, ℝ),
      Tendsto (fun i => ∫ x, ψ x * v i x ∂μ) l (𝓝 (∫ x, ψ x * u x ∂μ)))
    {f : E → E} (hf : Continuous f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    Tendsto (fun i => ∫ x : Ω, ⟪f x, polarDensity μ Ω (v i) x⟫ ∂variationMeasure μ Ω (v i)) l
      (𝓝 (∫ x : Ω, ⟪f x, polarDensity μ Ω u x⟫ ∂variationMeasure μ Ω u)) := by
  obtain ⟨δ, hδ, hδΩ⟩ := hc.exists_cthickening_subset_open Ω.isOpen hs
  let K := cthickening δ (tsupport f)
  have hK : IsCompact K := hc.cthickening
  have hfK : tsupport f ⊆ K := self_subset_cthickening _
  obtain ⟨C, hC⟩ := hbound K hK hδΩ
  let M := max C 0 + (variationMeasure μ Ω u).real (((↑) : Ω → E) ⁻¹' K) + 1
  have hM : 0 < M := by positivity
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  let η := ε / (M + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨ψ, hψK, hψ⟩ := hf.exists_testFunction_dist_le hc (Subset.refl _) hδ hδΩ hη
  have hψconv : Tendsto
      (fun i => ∫ x : Ω, ⟪ψ x, polarDensity μ Ω (v i) x⟫ ∂variationMeasure μ Ω (v i)) l
      (𝓝 (∫ x : Ω, ⟪ψ x, polarDensity μ Ω u x⟫ ∂variationMeasure μ Ω u)) := by
    have h := (hconv (divergenceCLM ψ)).neg
    simp_rw [integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity
      (hv _) (hvfin _), integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity hu hufin,
      neg_neg] at h
    exact h
  filter_upwards [hC, (Metric.tendsto_nhds.1 hψconv) η hη] with i hi hdist
  have hleft := dist_integral_inner_polarDensity_le (hv i) (hvfin i) hf ψ.continuous
    hK hδΩ hfK hψK (fun x => (dist_comm _ _).trans_le (hψ x))
  have hright := dist_integral_inner_polarDensity_le hu hufin ψ.continuous hf
    hK hδΩ hψK hfK hψ
  refine (dist_triangle4 _
    (∫ x : Ω, ⟪ψ x, polarDensity μ Ω (v i) x⟫ ∂variationMeasure μ Ω (v i))
    (∫ x : Ω, ⟪ψ x, polarDensity μ Ω u x⟫ ∂variationMeasure μ Ω u) _).trans_lt ?_
  have hleft' := hleft.trans (mul_le_mul_of_nonneg_left (hi.trans (le_max_left C 0)) hη.le)
  have hsum : η * max C 0 + η +
      η * (variationMeasure μ Ω u).real (((↑) : Ω → E) ⁻¹' K) < ε := by
    have hηeq : η * (M + 1) = ε := div_mul_cancel₀ _ (ne_of_gt (by positivity : 0 < M + 1))
    dsimp [M] at hηeq
    nlinarith
  linarith

/-- Local `L¹` convergence of locally BV functions, with variation eventually bounded on an
open neighbourhood of every compact subset of the domain, implies local weak-* convergence of
the vector derivative measures. Local finiteness of the limit's variation follows from these
bounds; it is not an additional hypothesis. The conclusion uses continuous fields compactly
supported in the domain, not only smooth test fields. -/
theorem tendsto_integral_inner_polarDensity_of_tendsto_L1_loc
    {ι : Type*} {l : Filter ι} {v : ι → E → ℝ} {u : E → ℝ}
    (hv : ∀ i, LocallyIntegrableOn (v i) Ω μ)
    (hvfin : ∀ i K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (v i) ≠ ∞)
    (hu : LocallyIntegrableOn u Ω μ)
    (hbound : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E,
      K ⊆ (U : Set E) ∧ U ≤ Ω ∧ ∃ C : ℝ≥0,
        ∀ᶠ i in l, totalVariationOn μ U (v i) ≤ C)
    (hconv : ∀ K, IsCompact K → K ⊆ Ω →
      Tendsto (fun i => ∫⁻ x in K, ‖v i x - u x‖ₑ ∂μ) l (𝓝 0))
    {f : E → E} (hf : Continuous f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    Tendsto (fun i => ∫ x : Ω, ⟪f x, polarDensity μ Ω (v i) x⟫ ∂variationMeasure μ Ω (v i)) l
      (𝓝 (∫ x : Ω, ⟪f x, polarDensity μ Ω u x⟫ ∂variationMeasure μ Ω u)) := by
  obtain rfl | hl := l.eq_or_neBot
  · exact tendsto_bot
  have hufin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞ := by
    intro K hK hKΩ
    obtain ⟨U, hKU, hUΩ, C, hC⟩ := hbound K hK hKΩ
    refine ⟨U, hKU, ne_top_of_le_ne_top (b := (C : ℝ≥0∞)) ENNReal.coe_ne_top ?_⟩
    exact (totalVariationOn_le_liminf (.of_forall fun i => (hv i).mono_set hUΩ)
      (hu.mono_set hUΩ) (fun L hL hLU => hconv L hL (hLU.trans hUΩ))).trans
        (liminf_le_of_frequently_le' hC.frequently)
  have hmass : ∀ K, IsCompact K → K ⊆ Ω → ∃ C : ℝ,
      ∀ᶠ i in l, (variationMeasure μ Ω (v i)).real (((↑) : Ω → E) ⁻¹' K) ≤ C := by
    intro K hK hKΩ
    obtain ⟨U, hKU, hUΩ, C, hC⟩ := hbound K hK hKΩ
    refine ⟨C, hC.mono fun i hi => ?_⟩
    have hle : variationMeasure μ Ω (v i) (((↑) : Ω → E) ⁻¹' K) ≤ C := by
      exact (measure_mono (preimage_mono hKU)).trans
        ((variationMeasure_preimage_coe (hv i) (hvfin i) hUΩ).le.trans hi)
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top hle)
      ENNReal.coe_ne_top).2 hle
  refine tendsto_integral_inner_polarDensity_of_tendsto_testFunction hv hvfin hu hufin hmass
    (fun ψ => ?_) hf hc hs
  exact MeasureTheory.tendsto_integral_smul_of_tendsto_lintegral_enorm_sub
    (.of_forall fun x => (ψ : E →ᵇ ℝ).norm_coe_le_norm x)
    (.of_forall fun x hx => image_eq_zero_of_notMem_tsupport hx)
    (.of_forall fun i => integrable_smul_of_locallyIntegrableOn (hv i) ψ)
    (integrable_smul_of_locallyIntegrableOn hu ψ).aestronglyMeasurable
    (hconv _ ψ.hasCompactSupport ψ.tsupport_subset)

end TauCeti
