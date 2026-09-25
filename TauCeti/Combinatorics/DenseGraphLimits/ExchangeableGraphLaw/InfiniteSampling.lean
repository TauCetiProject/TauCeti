/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Sampling
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Infinite

/-!
# The infinite graphon sampler as an exchangeable law

There are two constructions of an infinite random graph associated to a graphon. The explicit
joint sampler `infiniteSampleLaw` draws all vertex positions and edge coins on one probability
space. Independently, the finite sampling laws form `sampleExchangeableLaw`, whose consistent
marginals have a unique extension to an infinite exchangeable law through
`exchangeableGraphLawEquivInfinite`.

This file identifies those constructions. They have the same restriction to every finite window,
so extensionality of measures on infinite graphs shows that their laws agree. In particular, the
explicit joint sampling law is invariant under every permutation of its vertex labels.

## Main results

* `TauCeti.DenseGraphLimits.infiniteSampleLaw_eq_extension` — the explicit joint sampler is the
  infinite extension of its finite sampling laws;
* `TauCeti.DenseGraphLimits.infiniteSampleLaw_map_comap` — the explicit joint sampler is invariant
  under relabelling by every permutation of `ℕ`.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0,
  `Graphon/InfiniteSampler.lean`. The identification here follows `map_sampleInfinite` and
  `map_sampleInfinite_eq_infiniteSampleLaw_mk`, adapted to the finite-window extensionality API
  for Tau Ceti's laws on `SimpleGraph ℕ`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The explicit infinite sampler realizes the abstract extension.** The joint sampling law of
a graphon equals the unique infinite exchangeable law whose finite marginals are the graphon's
finite sampling laws. -/
theorem infiniteSampleLaw_eq_extension (W : Graphon Ω μ) :
    infiniteSampleLaw W = (exchangeableGraphLawEquivInfinite (sampleExchangeableLaw W)).law := by
  apply measure_ext_of_map_restrictFin
  intro n
  rw [infiniteSampleLaw_map_restrictFin,
    exchangeableGraphLawEquivInfinite_law_map_restrictFin, sampleExchangeableLaw_law]

/-- The infinite joint sampling law of a graphon is invariant under relabelling along every
permutation of `ℕ`. -/
@[simp]
theorem infiniteSampleLaw_map_comap (W : Graphon Ω μ) (σ : Equiv.Perm ℕ) :
    (infiniteSampleLaw W).map (SimpleGraph.comap ⇑σ) = infiniteSampleLaw W := by
  rw [infiniteSampleLaw_eq_extension W,
    InfiniteExchangeableGraphLaw.exchangeable]

end DenseGraphLimits

end TauCeti
