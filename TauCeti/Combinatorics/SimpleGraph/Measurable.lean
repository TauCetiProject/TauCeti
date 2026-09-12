/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Constructions.SimpleGraph

/-!
# Measurability of simple graphs

Mathlib equips `SimpleGraph V` with the sigma-algebra induced by all adjacency coordinates. When
`V` is countable, an individual graph is measurable because its edge set is a measurable point in
the countable product space. This supplies the discrete integration API for finite random graphs.

This file also records the window of a graph on `ℕ` spanned by the first `n` labels, the map a
random graph on an infinite label set is read through to recover a finite sample, together with
its measurability.

## Main definitions

* `SimpleGraph.restrictFin` — the initial `n`-label window of a graph on `ℕ`.

## Main results

* `SimpleGraph.instMeasurableSingletonClass` — singletons of graphs on a countable vertex type are
  measurable.
* `SimpleGraph.measurable_restrictFin` — taking a window is measurable.

## Reference

* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/SamplingLaw.lean`. The
  instance is adapted from its measurable singleton instance; the proof here goes through
  Mathlib's `SimpleGraph.measurableEmbedding_edgeSet`.
-/

public section

namespace SimpleGraph

variable {V : Type*}

/-- The canonical measurable space on simple graphs over a countable vertex type has measurable
singletons. -/
instance instMeasurableSingletonClass [Countable V] :
    MeasurableSingletonClass (SimpleGraph V) where
  measurableSet_singleton G := by
    rw [← measurableEmbedding_edgeSet.measurableSet_image, Set.image_singleton]
    exact MeasurableSet.singleton _

/-- The window of a graph on `ℕ` spanned by the first `n` labels. -/
def restrictFin (G : SimpleGraph ℕ) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.comap (fun i => (i : ℕ)) G

@[simp]
theorem restrictFin_adj {n : ℕ} (G : SimpleGraph ℕ) (a b : Fin n) :
    (G.restrictFin n).Adj a b ↔ G.Adj a b := Iff.rfl

/-- Taking a window is measurable. -/
theorem measurable_restrictFin (n : ℕ) :
    Measurable fun G : SimpleGraph ℕ => G.restrictFin n := by
  rw [SimpleGraph.measurable_iff_adj]
  intro a b
  exact (measurable_pi_apply (b : ℕ)).comp
    ((measurable_pi_apply (a : ℕ)).comp SimpleGraph.measurable_adj)

end SimpleGraph
