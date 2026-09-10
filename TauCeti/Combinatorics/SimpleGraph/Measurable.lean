/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Constructions.SimpleGraph

/-!
# Measurability of individual simple graphs

Mathlib equips `SimpleGraph V` with the sigma-algebra induced by all adjacency coordinates. When
`V` is countable, an individual graph is measurable because its edge set is a measurable point in
the countable product space. This supplies the discrete integration API for finite random graphs.

## Main result

* `SimpleGraph.instMeasurableSingletonClass` — singletons of graphs on a countable vertex type are
  measurable.

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

end SimpleGraph
