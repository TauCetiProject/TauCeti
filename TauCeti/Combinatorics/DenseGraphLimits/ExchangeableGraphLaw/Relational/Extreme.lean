/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Relational.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Extreme
public import TauCeti.Probability.Exchangeability.RelationalLaw.Convex
import TauCeti.MeasureTheory.Measure.Face

/-!
# Extremality of graph laws under relational encoding

Encoding simple graphs as relational configurations preserves and reflects extremality among
exchangeable probability measures. The target is the set of **all** exchangeable relational laws
of the language of graphs, not just those concentrated on symmetric irreflexive configurations.
Indeed, measures concentrated on simple graphs form a face of that larger set: both components of
any nontrivial convex decomposition of such a measure must also be concentrated on simple graphs.
The measurable graph encoding and its pullback then transport the decomposition in both directions.

Consequently an encoded exchangeable graph law is extreme exactly when its finite marginals are
dissociated. In particular, every graphon sampling law gives an extreme exchangeable relational
law, with no assumptions on its probability carrier.

## Main results

* `TauCeti.DenseGraphLimits.mem_extremePoints_iff_map_toRelationalConfiguration_mem_extremePoints`
  transports extremality between graph measures and relational measures.
* `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw.mem_extremePoints_toRelationalLaw_iff`
  characterizes extremality of the encoded law by dissociation of its finite marginals.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.

The affine transport argument follows the graph-to-array adapter
`mem_extremePoints_iff_arrayLaw_mem_extremePoints`; concentration is handled by
`TauCeti.MeasureTheory.isExtreme_setOf_measure_eq_zero`.
-/

public section

open MeasureTheory Set TauCeti.Probability TauCeti.RelationalConfiguration
open _root_.FirstOrder (Language)
open scoped ENNReal

namespace TauCeti.DenseGraphLimits

/-- Encoding a graph measure preserves and reflects exchangeability and total mass one. -/
theorem map_toRelationalConfiguration_mem_iff {μ : Measure (SimpleGraph ℕ)} :
    μ.map SimpleGraph.toRelationalConfiguration ∈
        exchangeableRelationalProbabilityMeasures Language.graph ↔
      μ ∈ exchangeableGraphProbabilityMeasures := by
  simp only [mem_exchangeableRelationalProbabilityMeasures_iff,
    mem_exchangeableGraphProbabilityMeasures_iff]
  constructor
  · rintro ⟨hexch, hp⟩
    have hp' : IsProbabilityMeasure μ := by
      constructor
      have h := hp.measure_univ
      rwa [Measure.map_apply SimpleGraph.measurable_toRelationalConfiguration
        MeasurableSet.univ, preimage_univ] at h
    refine ⟨fun σ => ?_, hp'⟩
    apply SimpleGraph.measurableEmbedding_toRelationalConfiguration.map_injective
    rw [Measure.map_map SimpleGraph.measurable_toRelationalConfiguration
      (SimpleGraph.measurable_comap _), SimpleGraph.toRelationalConfiguration_comp_comap,
      ← Measure.map_map (measurable_restrict _)
        SimpleGraph.measurable_toRelationalConfiguration, hexch σ]
  · rintro ⟨hexch, hp⟩
    simpa only [InfiniteExchangeableGraphLaw.toRelationalLaw_law] using
      mem_exchangeableRelationalProbabilityMeasures_iff.1
        (InfiniteExchangeableGraphLaw.toRelationalLaw ⟨μ, hp, hexch⟩).law_mem

/-- A graph measure is extreme among exchangeable graph probability measures exactly when its
encoding is extreme among all exchangeable relational probability measures of the graph language.
The simple-graph concentration constraint does not restrict the ambient extremality statement. -/
theorem mem_extremePoints_iff_map_toRelationalConfiguration_mem_extremePoints
    {μ : Measure (SimpleGraph ℕ)} :
    μ ∈ extremePoints ℝ≥0∞ exchangeableGraphProbabilityMeasures ↔
      μ.map SimpleGraph.toRelationalConfiguration ∈
        extremePoints ℝ≥0∞ (exchangeableRelationalProbabilityMeasures Language.graph) := by
  simp only [mem_extremePoints_iff_left]
  constructor
  · rintro ⟨hμ, h⟩
    refine ⟨map_toRelationalConfiguration_mem_iff.2 hμ, ?_⟩
    intro ρ₁ hρ₁ ρ₂ hρ₂ hsegment
    -- The encoded law lies in the face of measures concentrated on simple graphs, so both
    -- ends of its decomposition can be decoded as graph measures.
    have hface := TauCeti.MeasureTheory.isExtreme_setOf_measure_eq_zero
      (exchangeableRelationalProbabilityMeasures Language.graph)
      {c | IsSimpleGraph c}ᶜ
    have hmem : μ.map SimpleGraph.toRelationalConfiguration ∈
        {ρ ∈ exchangeableRelationalProbabilityMeasures Language.graph |
          ρ {c | IsSimpleGraph c}ᶜ = 0} :=
      ⟨map_toRelationalConfiguration_mem_iff.2 hμ,
        ae_iff.1 (SimpleGraph.ae_isSimpleGraph_map_toRelationalConfiguration μ)⟩
    have hs₁ : ∀ᵐ c ∂ρ₁, IsSimpleGraph c :=
      ae_iff.2 (hface.2 hρ₁ hρ₂ hmem hsegment).2
    have hs₂ : ∀ᵐ c ∂ρ₂, IsSimpleGraph c :=
      ae_iff.2 (hface.2 hρ₂ hρ₁ hmem (by rwa [openSegment_symm])).2
    have e₁ := SimpleGraph.map_comap_toRelationalConfiguration hs₁
    have e₂ := SimpleGraph.map_comap_toRelationalConfiguration hs₂
    have h₁ : ρ₁.comap SimpleGraph.toRelationalConfiguration ∈
        exchangeableGraphProbabilityMeasures := by
      rw [← map_toRelationalConfiguration_mem_iff, e₁]
      exact hρ₁
    have h₂ : ρ₂.comap SimpleGraph.toRelationalConfiguration ∈
        exchangeableGraphProbabilityMeasures := by
      rw [← map_toRelationalConfiguration_mem_iff, e₂]
      exact hρ₂
    obtain ⟨a, b, ha, hb, hab, hmix⟩ := hsegment
    have hmix' : a • ρ₁.comap SimpleGraph.toRelationalConfiguration +
        b • ρ₂.comap SimpleGraph.toRelationalConfiguration = μ := by
      simpa only [SimpleGraph.measurableEmbedding_toRelationalConfiguration.comap_add,
        Measure.comap_smul,
        SimpleGraph.measurableEmbedding_toRelationalConfiguration.comap_map] using
          congrArg (Measure.comap SimpleGraph.toRelationalConfiguration) hmix
    have heq := h _ h₁ _ h₂ ⟨a, b, ha, hb, hab, hmix'⟩
    rw [← e₁, heq]
  · rintro ⟨hμ, h⟩
    refine ⟨map_toRelationalConfiguration_mem_iff.1 hμ, ?_⟩
    rintro μ₁ hμ₁ μ₂ hμ₂ ⟨a, b, ha, hb, hab, hmix⟩
    apply SimpleGraph.measurableEmbedding_toRelationalConfiguration.map_injective
    apply h _ (map_toRelationalConfiguration_mem_iff.2 hμ₁) _
      (map_toRelationalConfiguration_mem_iff.2 hμ₂)
    refine ⟨a, b, ha, hb, hab, ?_⟩
    simpa only [Measure.map_add _ _ SimpleGraph.measurable_toRelationalConfiguration,
      Measure.map_smul _ SimpleGraph.measurable_toRelationalConfiguration.aemeasurable] using
        congrArg (Measure.map SimpleGraph.toRelationalConfiguration) hmix

/-- An encoded exchangeable graph law is extreme among all exchangeable relational probability
measures exactly when its finite graph law is dissociated. -/
theorem InfiniteExchangeableGraphLaw.mem_extremePoints_toRelationalLaw_iff
    (L : InfiniteExchangeableGraphLaw) :
    L.toRelationalLaw.law ∈
        extremePoints ℝ≥0∞ (exchangeableRelationalProbabilityMeasures Language.graph) ↔
      (exchangeableGraphLawEquivInfinite.symm L).IsDissociated := by
  rw [L.toRelationalLaw_law,
    ← mem_extremePoints_iff_map_toRelationalConfiguration_mem_extremePoints,
    mem_extremePoints_iff_isDissociated]

/-- Every graphon sampling law, encoded as a relational law, is extreme among all exchangeable
relational probability measures of the graph language. -/
theorem infiniteSampleLaw_map_toRelationalConfiguration_mem_extremePoints
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W : Graphon Ω μ) :
    (infiniteSampleLaw W).map SimpleGraph.toRelationalConfiguration ∈
      extremePoints ℝ≥0∞ (exchangeableRelationalProbabilityMeasures Language.graph) :=
  mem_extremePoints_iff_map_toRelationalConfiguration_mem_extremePoints.1
    (infiniteSampleLaw_mem_extremePoints W)

end TauCeti.DenseGraphLimits
