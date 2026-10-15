/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite.Basic
public import TauCeti.Combinatorics.SimpleGraph.RelationalConfiguration
public import TauCeti.Probability.Exchangeability.RelationalLaw
-- Non-public: `measure_ext_of_map_restrict_val`, the window determination of laws on `ℕ`.
import TauCeti.MeasureTheory.Measure.RelationalConfiguration

/-!
# Exchangeable graph laws as exchangeable relational laws

Encoding a simple graph as a configuration of the language of graphs
(`SimpleGraph.toRelationalConfiguration`) turns an exchangeable graph law into an exchangeable
relational law, and an exchangeable law on infinite graphs into an invariant relational law on `ℕ`.
The generic correspondence between the two presentations of exchangeable relational laws
(`TauCeti.Probability.exchangeableRelationalLawEquivInfinite`) then agrees with the graph-specific
one (`exchangeableGraphLawEquivInfinite`): extending the encoded finite marginals gives the encoding
of the extended graph law.

Conversely, the encoding identifies exchangeable graph laws with the exchangeable relational laws
of the language of graphs whose marginals are concentrated on simple graphs, and likewise for laws
on infinite graphs: laws on simple graphs are recovered from their encodings by pulling back along
the encoding, a measurable embedding on countable vertex types.

## Main definitions

* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.toRelationalLaw` — the exchangeable relational law
  of an exchangeable graph law;
* `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw.toRelationalLaw` — the invariant
  relational law on `ℕ` of an exchangeable law on infinite graphs;
* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.relationalLawEquiv` and
  `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw.relationalLawEquiv` — these encodings are
  equivalences onto the relational laws concentrated on simple graphs.

## Main results

* `ExchangeableGraphLaw.exchangeableRelationalLawEquivInfinite_toRelationalLaw` (in
  `TauCeti.DenseGraphLimits`) — the generic correspondence agrees with
  `exchangeableGraphLawEquivInfinite`;
* `ae_isSimpleGraph_exchangeableRelationalLawEquivInfinite_law_iff` (in `TauCeti.DenseGraphLimits`)
  — the generic correspondence matches relational laws concentrated on simple graphs on both sides.
-/

public section

noncomputable section

open MeasureTheory TauCeti.RelationalConfiguration TauCeti.Probability

open _root_.FirstOrder (Language)

namespace TauCeti

namespace DenseGraphLimits

/-- Encoding commutes with restriction, as an identity of maps. -/
private theorem toRelationalConfiguration_comp_comap {V W : Type*} (f : V → W) :
    SimpleGraph.toRelationalConfiguration ∘ SimpleGraph.comap f =
      restrict f ∘ (SimpleGraph.toRelationalConfiguration : SimpleGraph W → _) :=
  funext fun G => SimpleGraph.toRelationalConfiguration_comap f G

/-- A law on configurations concentrated on simple graphs is the encoding of its pullback to
simple graphs. -/
private theorem map_comap_toRelationalConfiguration {V : Type*} [Countable V]
    {μ : Measure (RelationalConfiguration Language.graph V)} (hμ : ∀ᵐ c ∂μ, IsSimpleGraph c) :
    (μ.comap SimpleGraph.toRelationalConfiguration).map SimpleGraph.toRelationalConfiguration =
      μ := by
  rw [SimpleGraph.measurableEmbedding_toRelationalConfiguration.map_comap,
    SimpleGraph.range_toRelationalConfiguration]
  exact Measure.restrict_eq_self_of_ae_mem hμ

/-- The pullback to simple graphs of a probability law concentrated on simple graphs is a
probability law. -/
private theorem isProbabilityMeasure_comap_toRelationalConfiguration {V : Type*} [Countable V]
    {μ : Measure (RelationalConfiguration Language.graph V)} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ c ∂μ, IsSimpleGraph c) :
    IsProbabilityMeasure (μ.comap SimpleGraph.toRelationalConfiguration) :=
  SimpleGraph.measurableEmbedding_toRelationalConfiguration.isProbabilityMeasure_comap <| by
    rwa [SimpleGraph.range_toRelationalConfiguration]

/-- Restricting a law concentrated on simple graphs gives a law concentrated on simple graphs. -/
private theorem ae_isSimpleGraph_map_restrict {V W : Type*} [Countable V] (f : V → W)
    {μ : Measure (RelationalConfiguration Language.graph W)} (hμ : ∀ᵐ c ∂μ, IsSimpleGraph c) :
    ∀ᵐ c ∂μ.map (restrict f), IsSimpleGraph c := by
  rw [ae_map_iff (measurable_restrict f).aemeasurable measurableSet_setOf_isSimpleGraph]
  filter_upwards [hμ] with c hc using hc.restrict f

/-- For laws concentrated on simple graphs, pulling back to simple graphs commutes with
restriction. -/
private theorem map_comap_comap_toRelationalConfiguration {V W : Type*} [Countable V]
    [Countable W] (f : V → W) {μ : Measure (RelationalConfiguration Language.graph W)}
    (hμ : ∀ᵐ c ∂μ, IsSimpleGraph c) :
    (μ.comap SimpleGraph.toRelationalConfiguration).map (SimpleGraph.comap f) =
      (μ.map (restrict f)).comap SimpleGraph.toRelationalConfiguration := by
  refine SimpleGraph.measurableEmbedding_toRelationalConfiguration.map_injective ?_
  rw [Measure.map_map SimpleGraph.measurable_toRelationalConfiguration
      (SimpleGraph.measurable_comap _), toRelationalConfiguration_comp_comap,
    ← Measure.map_map (measurable_restrict _) SimpleGraph.measurable_toRelationalConfiguration,
    map_comap_toRelationalConfiguration hμ,
    map_comap_toRelationalConfiguration (ae_isSimpleGraph_map_restrict f hμ)]

/-- The encoding of a law on simple graphs is concentrated on simple graphs. -/
private theorem ae_isSimpleGraph_map_toRelationalConfiguration {V : Type*} [Countable V]
    (μ : Measure (SimpleGraph V)) :
    ∀ᵐ c ∂μ.map SimpleGraph.toRelationalConfiguration, IsSimpleGraph c :=
  SimpleGraph.measurableEmbedding_toRelationalConfiguration.ae_map_iff.2
    (ae_of_all _ SimpleGraph.isSimpleGraph_toRelationalConfiguration)

namespace ExchangeableGraphLaw

/-- The **exchangeable relational law of an exchangeable graph law**: its marginals, encoded as
configurations of the language of graphs. -/
def toRelationalLaw (L : ExchangeableGraphLaw) : ExchangeableRelationalLaw Language.graph where
  law n := (L.law n).map SimpleGraph.toRelationalConfiguration
  prob _ := inferInstance
  consistent f := by
    rw [Measure.map_map (measurable_restrict _) SimpleGraph.measurable_toRelationalConfiguration,
      ← toRelationalConfiguration_comp_comap,
      ← Measure.map_map SimpleGraph.measurable_toRelationalConfiguration
        (SimpleGraph.measurable_comap _), L.consistent]

@[simp]
theorem toRelationalLaw_law (L : ExchangeableGraphLaw) (n : ℕ) :
    L.toRelationalLaw.law n = (L.law n).map SimpleGraph.toRelationalConfiguration := (rfl)

/-- The marginals of the relational law of an exchangeable graph law are concentrated on simple
graphs. -/
theorem ae_isSimpleGraph_toRelationalLaw_law (L : ExchangeableGraphLaw) (n : ℕ) :
    ∀ᵐ c ∂L.toRelationalLaw.law n, IsSimpleGraph c :=
  ae_isSimpleGraph_map_toRelationalConfiguration _

/-- **Exchangeable graph laws are the exchangeable relational laws of the language of graphs whose
marginals are concentrated on simple graphs**, that is, on symmetric irreflexive configurations.
The inverse pulls each marginal back along the encoding. -/
def relationalLawEquiv : ExchangeableGraphLaw ≃
    {μ : ExchangeableRelationalLaw Language.graph // ∀ n, ∀ᵐ c ∂μ.law n, IsSimpleGraph c} where
  toFun L := ⟨L.toRelationalLaw, L.ae_isSimpleGraph_toRelationalLaw_law⟩
  invFun μ :=
    { law n := (μ.1.law n).comap SimpleGraph.toRelationalConfiguration
      prob n := isProbabilityMeasure_comap_toRelationalConfiguration (μ.2 n)
      consistent {_ l} f := by
        rw [map_comap_comap_toRelationalConfiguration _ (μ.2 l), μ.1.consistent] }
  left_inv L := ext fun n =>
    SimpleGraph.measurableEmbedding_toRelationalConfiguration.comap_map (L.law n)
  right_inv μ := Subtype.ext <| ExchangeableRelationalLaw.ext fun n =>
    map_comap_toRelationalConfiguration (μ.2 n)

@[simp]
theorem coe_relationalLawEquiv (L : ExchangeableGraphLaw) :
    (relationalLawEquiv L : ExchangeableRelationalLaw Language.graph) = L.toRelationalLaw := (rfl)

@[simp]
theorem relationalLawEquiv_symm_law
    (μ : {μ : ExchangeableRelationalLaw Language.graph // ∀ n, ∀ᵐ c ∂μ.law n, IsSimpleGraph c})
    (n : ℕ) :
    (relationalLawEquiv.symm μ).law n =
      (μ.1.law n).comap SimpleGraph.toRelationalConfiguration := (rfl)

/-- Distinct exchangeable graph laws have distinct relational laws. -/
theorem toRelationalLaw_injective : Function.Injective toRelationalLaw :=
  fun _ _ h => relationalLawEquiv.injective (Subtype.ext h)

end ExchangeableGraphLaw

namespace InfiniteExchangeableGraphLaw

/-- The **invariant relational law of an exchangeable law on infinite graphs**: its law, encoded as
configurations of the language of graphs. -/
def toRelationalLaw (L : InfiniteExchangeableGraphLaw) :
    InfiniteExchangeableRelationalLaw Language.graph where
  law := L.law.map SimpleGraph.toRelationalConfiguration
  prob := inferInstance
  exchangeable σ := by
    rw [Measure.map_map (measurable_restrict _) SimpleGraph.measurable_toRelationalConfiguration,
      ← toRelationalConfiguration_comp_comap,
      ← Measure.map_map SimpleGraph.measurable_toRelationalConfiguration
        (SimpleGraph.measurable_comap _), L.exchangeable]

@[simp]
theorem toRelationalLaw_law (L : InfiniteExchangeableGraphLaw) :
    L.toRelationalLaw.law = L.law.map SimpleGraph.toRelationalConfiguration := (rfl)

/-- The relational law of an exchangeable law on infinite graphs is concentrated on simple
graphs. -/
theorem ae_isSimpleGraph_toRelationalLaw_law (L : InfiniteExchangeableGraphLaw) :
    ∀ᵐ c ∂L.toRelationalLaw.law, IsSimpleGraph c :=
  ae_isSimpleGraph_map_toRelationalConfiguration _

/-- **Exchangeable laws on infinite graphs are the exchangeable relational laws of the language of
graphs on `ℕ` concentrated on simple graphs**, that is, on symmetric irreflexive configurations.
The inverse pulls the law back along the encoding. -/
def relationalLawEquiv : InfiniteExchangeableGraphLaw ≃
    {μ : InfiniteExchangeableRelationalLaw Language.graph // ∀ᵐ c ∂μ.law, IsSimpleGraph c} where
  toFun L := ⟨L.toRelationalLaw, L.ae_isSimpleGraph_toRelationalLaw_law⟩
  invFun μ :=
    { law := μ.1.law.comap SimpleGraph.toRelationalConfiguration
      prob := isProbabilityMeasure_comap_toRelationalConfiguration μ.2
      exchangeable σ := by
        rw [map_comap_comap_toRelationalConfiguration _ μ.2, μ.1.exchangeable] }
  left_inv L := ext <| SimpleGraph.measurableEmbedding_toRelationalConfiguration.comap_map L.law
  right_inv μ := Subtype.ext <| InfiniteExchangeableRelationalLaw.ext <|
    map_comap_toRelationalConfiguration μ.2

@[simp]
theorem coe_relationalLawEquiv (L : InfiniteExchangeableGraphLaw) :
    (relationalLawEquiv L : InfiniteExchangeableRelationalLaw Language.graph) =
      L.toRelationalLaw := (rfl)

@[simp]
theorem relationalLawEquiv_symm_law
    (μ : {μ : InfiniteExchangeableRelationalLaw Language.graph // ∀ᵐ c ∂μ.law, IsSimpleGraph c}) :
    (relationalLawEquiv.symm μ).law = μ.1.law.comap SimpleGraph.toRelationalConfiguration := (rfl)

/-- Distinct exchangeable laws on infinite graphs have distinct relational laws. -/
theorem toRelationalLaw_injective : Function.Injective toRelationalLaw :=
  fun _ _ h => relationalLawEquiv.injective (Subtype.ext h)

end InfiniteExchangeableGraphLaw

namespace ExchangeableGraphLaw

/-- **The generic correspondence agrees with the graph-specific one**: extending the relational
law of an exchangeable graph law gives the relational law of its extension to infinite graphs. -/
theorem exchangeableRelationalLawEquivInfinite_toRelationalLaw (L : ExchangeableGraphLaw) :
    exchangeableRelationalLawEquivInfinite Language.graph L.toRelationalLaw =
      (exchangeableGraphLawEquivInfinite L).toRelationalLaw := by
  refine InfiniteExchangeableRelationalLaw.ext (measure_ext_of_map_restrict_val fun n => ?_)
  -- Both laws have the encoded marginals as windows: the windows of an encoded infinite graph law
  -- are the encoded windows of the graph law.
  have hwin : restrict (Fin.val : Fin n → ℕ) ∘ SimpleGraph.toRelationalConfiguration =
      SimpleGraph.toRelationalConfiguration ∘ fun G : SimpleGraph ℕ => G.restrictFin n := by
    funext G
    simp only [Function.comp_apply, ← SimpleGraph.comap_val,
      SimpleGraph.toRelationalConfiguration_comap]
  rw [exchangeableRelationalLawEquivInfinite_law_map_restrict, toRelationalLaw_law,
    InfiniteExchangeableGraphLaw.toRelationalLaw_law,
    Measure.map_map (measurable_restrict _) SimpleGraph.measurable_toRelationalConfiguration, hwin,
    ← Measure.map_map SimpleGraph.measurable_toRelationalConfiguration
      (SimpleGraph.measurable_restrictFin n),
    exchangeableGraphLawEquivInfinite_law_map_restrictFin]

end ExchangeableGraphLaw

/-- **Consistent marginals concentrated on simple graphs extend to a law concentrated on simple
graphs**, and conversely: the extension of an exchangeable relational law of the language of graphs
is concentrated on simple graphs exactly when every marginal is. -/
theorem ae_isSimpleGraph_exchangeableRelationalLawEquivInfinite_law_iff
    (μ : ExchangeableRelationalLaw Language.graph) :
    (∀ᵐ c ∂(exchangeableRelationalLawEquivInfinite Language.graph μ).law, IsSimpleGraph c) ↔
      ∀ n, ∀ᵐ c ∂μ.law n, IsSimpleGraph c := by
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · rw [← exchangeableRelationalLawEquivInfinite_law_map_restrict]
    exact ae_isSimpleGraph_map_restrict _ h
  · -- Write `μ` as the relational law of a graph law and transport along the graph extension.
    obtain ⟨L, hL⟩ := ExchangeableGraphLaw.relationalLawEquiv.surjective ⟨μ, h⟩
    obtain rfl : L.toRelationalLaw = μ := congrArg Subtype.val hL
    rw [ExchangeableGraphLaw.exchangeableRelationalLawEquivInfinite_toRelationalLaw]
    exact InfiniteExchangeableGraphLaw.ae_isSimpleGraph_toRelationalLaw_law _

end DenseGraphLimits

end TauCeti
