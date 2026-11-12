/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.DissociatedRepresentation
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Relational.Basic

/-!
# Dissociated exchangeable graph laws as dissociated relational laws

An exchangeable graph law is dissociated (`ExchangeableGraphLaw.IsDissociated`) when the random
graphs it induces on disjoint label windows are independent; an exchangeable relational law is
dissociated (`TauCeti.Probability.ExchangeableRelationalLaw.IsDissociated`) when the random
configurations it induces on disjoint vertex windows are. Encoding simple graphs as configurations
of the language of graphs commutes with restriction to a window, and the encoding is a measurable
embedding, so it neither creates nor destroys independence: a graph law is dissociated exactly when
its relational law is.

Combined with the extremality of graphon sampling laws among exchangeable graph laws
(`exists_graphon_of_isDissociated`), this identifies the dissociated exchangeable relational laws
of the language of graphs concentrated on simple graphs: they are exactly the relational laws of
graphon sampling laws.

## Main results

* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.isDissociated_toRelationalLaw_iff` — a graph law
  is dissociated exactly when its relational law is;
* `TauCeti.DenseGraphLimits.isDissociated_iff_exists_toRelationalLaw_sampleExchangeableLaw` — an
  exchangeable relational law of the language of graphs concentrated on simple graphs is
  dissociated exactly when it is the relational law of a graphon sampling law.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open MeasureTheory TauCeti.RelationalConfiguration TauCeti.Probability

open _root_.FirstOrder (Language)

namespace TauCeti

namespace DenseGraphLimits

namespace ExchangeableGraphLaw

/-- Reading the two windows of the encoded level-`(k + l)` marginal is encoding the two windows
of the graph marginal. -/
private theorem toRelationalLaw_law_map_restrict_pair (L : ExchangeableGraphLaw) (k l : ℕ) :
    (L.toRelationalLaw.law (k + l)).map
        (fun c => (c.restrict (Fin.castAdd l), c.restrict (Fin.natAdd k))) =
      ((L.law (k + l)).map fun G => (G.comap (Fin.castAdd l), G.comap (Fin.natAdd k))).map
        (Prod.map SimpleGraph.toRelationalConfiguration SimpleGraph.toRelationalConfiguration) := by
  have hpair : (fun c : RelationalConfiguration Language.graph (Fin (k + l)) =>
        (c.restrict (Fin.castAdd l), c.restrict (Fin.natAdd k))) ∘
          SimpleGraph.toRelationalConfiguration =
      Prod.map SimpleGraph.toRelationalConfiguration SimpleGraph.toRelationalConfiguration ∘
        fun G => (G.comap (Fin.castAdd l), G.comap (Fin.natAdd k)) := by
    funext G
    simp only [Function.comp_apply, Prod.map_apply, SimpleGraph.toRelationalConfiguration_comap]
  rw [toRelationalLaw_law, Measure.map_map ((measurable_restrict _).prodMk (measurable_restrict _))
      SimpleGraph.measurable_toRelationalConfiguration, hpair,
    Measure.map_map (SimpleGraph.measurable_toRelationalConfiguration.prodMap
      SimpleGraph.measurable_toRelationalConfiguration)
      ((SimpleGraph.measurable_comap _).prodMk (SimpleGraph.measurable_comap _))]

/-- **A graph law is dissociated exactly when its relational law is**: encoding graphs as
configurations of the language of graphs neither creates nor destroys independence of disjoint
windows. -/
@[simp]
theorem isDissociated_toRelationalLaw_iff (L : ExchangeableGraphLaw) :
    L.toRelationalLaw.IsDissociated ↔ L.IsDissociated := by
  rw [ExchangeableRelationalLaw.isDissociated_iff, isDissociated_iff]
  refine forall₂_congr fun k l => ?_
  -- Both sides of the relational identity are encodings of the two sides of the graph identity,
  -- and encoding pairs of graphs is a measurable embedding, so pushing forward along it is
  -- injective.
  rw [L.toRelationalLaw_law_map_restrict_pair k l, toRelationalLaw_law, toRelationalLaw_law,
    Measure.map_prod_map _ _ SimpleGraph.measurable_toRelationalConfiguration
      SimpleGraph.measurable_toRelationalConfiguration]
  exact (SimpleGraph.measurableEmbedding_toRelationalConfiguration.prodMap
    SimpleGraph.measurableEmbedding_toRelationalConfiguration).map_injective.eq_iff

end ExchangeableGraphLaw

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

variable (μ) in
/-- **Dissociated relational laws of graphs are graphon sampling laws.** An exchangeable relational
law of the language of graphs whose marginals are concentrated on simple graphs is dissociated
exactly when it is the relational law of the sampling law of a graphon, which may be taken on any
atomless standard Borel carrier `(Ω, μ)`, such as the unit interval. -/
theorem isDissociated_iff_exists_toRelationalLaw_sampleExchangeableLaw [StandardBorelSpace Ω]
    [NullSingletonClass μ] {ν : ExchangeableRelationalLaw Language.graph}
    (hν : ∀ n, ∀ᵐ c ∂ν.law n, IsSimpleGraph c) :
    ν.IsDissociated ↔ ∃ W : Graphon Ω μ, ν = (sampleExchangeableLaw W).toRelationalLaw := by
  -- Write `ν` as the relational law of a graph law and transport along the encoding.
  obtain ⟨L, hL⟩ := ExchangeableGraphLaw.relationalLawEquiv.surjective ⟨ν, hν⟩
  obtain rfl : L.toRelationalLaw = ν := by
    rw [← ExchangeableGraphLaw.coe_relationalLawEquiv, hL]
  rw [ExchangeableGraphLaw.isDissociated_toRelationalLaw_iff]
  refine ⟨fun h => (exists_graphon_of_isDissociated μ L h).imp fun _ hW => congrArg _ hW, ?_⟩
  rintro ⟨W, hW⟩
  rw [ExchangeableGraphLaw.toRelationalLaw_injective hW]
  exact isDissociated_sampleExchangeableLaw W

end DenseGraphLimits

end TauCeti
