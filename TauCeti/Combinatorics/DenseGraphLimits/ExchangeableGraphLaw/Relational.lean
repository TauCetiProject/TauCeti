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

## Main definitions

* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.toRelationalLaw` — the exchangeable relational law
  of an exchangeable graph law;
* `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw.toRelationalLaw` — the invariant
  relational law on `ℕ` of an exchangeable law on infinite graphs.

## Main results

* `ExchangeableGraphLaw.exchangeableRelationalLawEquivInfinite_toRelationalLaw` (in
  `TauCeti.DenseGraphLimits`) — the generic correspondence agrees with
  `exchangeableGraphLawEquivInfinite`.
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

end DenseGraphLimits

end TauCeti
