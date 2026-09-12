/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.SimpleGraph
public import TauCeti.Combinatorics.SimpleGraph.Maps

/-!
# Measurability of individual simple graphs and of relabelling

Mathlib equips `SimpleGraph V` with the sigma-algebra induced by all adjacency coordinates. When
`V` is countable, an individual graph is measurable because its edge set is a measurable point in
the countable product space. This supplies the discrete integration API for finite random graphs.

Each adjacency coordinate of a graph pulled back along a map of vertex types is a single
adjacency coordinate of the source graph, so the pullback is measurable with no hypothesis on
either vertex type. This is what lets a random graph be restricted to a window of labels: the
window `SimpleGraph.restrictFin` is the special case along `Fin.val`.

## Main results

* `SimpleGraph.instMeasurableSingletonClass` — singletons of graphs on a countable vertex type are
  measurable;
* `SimpleGraph.measurable_comap` — pulling back along a map of vertex types is measurable;
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

variable {W : Type*}

/-- Pulling a simple graph back along a map of vertex types is measurable: each adjacency
coordinate of the pullback is an adjacency coordinate of the source. -/
@[fun_prop]
theorem measurable_comap (f : V → W) :
    Measurable (SimpleGraph.comap f : SimpleGraph W → SimpleGraph V) :=
  measurable_iff_adj.2 fun u v => measurable_iff_adj.1 measurable_id (f u) (f v)

/-- Taking a window is measurable. -/
@[fun_prop]
theorem measurable_restrictFin (n : ℕ) :
    Measurable fun G : SimpleGraph ℕ => G.restrictFin n :=
  -- `restrictFin` does not unfold outside the module that defines it, so `measurable_comap` is
  -- not applicable directly; `restrictFin_adj` supplies the same adjacency equation.
  measurable_iff_adj.2 fun u v => by
    simp only [restrictFin_adj]
    exact measurable_iff_adj.1 measurable_id (u : ℕ) v

end SimpleGraph
