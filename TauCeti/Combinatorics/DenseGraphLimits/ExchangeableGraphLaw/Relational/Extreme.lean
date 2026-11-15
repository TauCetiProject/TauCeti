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
import TauCeti.Analysis.Convex.Extreme

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
* `InfiniteExchangeableGraphLaw.map_toRelationalConfiguration_mem_extremePoints_iff`
  characterizes extremality of the encoded law by dissociation of its finite marginals.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.

* `mem_extremePoints_iff_arrayLaw_mem_extremePoints`: the graph-to-array extremality adapter.
* `TauCeti.MeasureTheory.isExtreme_setOf_measure_eq_zero`: the face of measures concentrated
  on a set.
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
    have hp' : IsProbabilityMeasure μ :=
      (Measure.isProbabilityMeasure_map_iff
        SimpleGraph.measurable_toRelationalConfiguration.aemeasurable).1 hp
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
  have hf : ⇑(Measure.mapₗ SimpleGraph.toRelationalConfiguration) =
      Measure.map (SimpleGraph.toRelationalConfiguration (V := ℕ)) :=
    funext (Measure.mapₗ_apply_of_measurable SimpleGraph.measurable_toRelationalConfiguration)
  have h := TauCeti.mem_extremePoints_iff_linearMap_mem_extremePoints
    (C := exchangeableGraphProbabilityMeasures) μ
    (TauCeti.MeasureTheory.isExtreme_setOf_measure_eq_zero
      (exchangeableRelationalProbabilityMeasures Language.graph) {c | IsSimpleGraph c}ᶜ)
    (Measure.mapₗ SimpleGraph.toRelationalConfiguration)
  simp only [hf] at h
  apply h SimpleGraph.measurableEmbedding_toRelationalConfiguration.map_injective
    (fun _ => map_toRelationalConfiguration_mem_iff)
  · intro ν hν
    exact ⟨map_toRelationalConfiguration_mem_iff.2 hν,
      ae_iff.1 (SimpleGraph.ae_isSimpleGraph_map_toRelationalConfiguration ν)⟩
  · intro ρ hρ
    exact ⟨ρ.comap SimpleGraph.toRelationalConfiguration,
      SimpleGraph.map_comap_toRelationalConfiguration (ae_iff.2 hρ.2)⟩

/-- An encoded exchangeable graph law is extreme among all exchangeable relational probability
measures exactly when its finite graph law is dissociated. -/
@[simp]
theorem InfiniteExchangeableGraphLaw.map_toRelationalConfiguration_mem_extremePoints_iff
    (L : InfiniteExchangeableGraphLaw) :
    L.law.map SimpleGraph.toRelationalConfiguration ∈
        extremePoints ℝ≥0∞ (exchangeableRelationalProbabilityMeasures Language.graph) ↔
      (exchangeableGraphLawEquivInfinite.symm L).IsDissociated := by
  rw [← mem_extremePoints_iff_map_toRelationalConfiguration_mem_extremePoints,
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
