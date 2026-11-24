/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Polish

/-!
# Open embeddings into completely metrizable and Polish spaces

An open embedding `f : X → Y` identifies `X` homeomorphically with the open range `Set.range f`, so
complete metrizability and Polishness pull back along `f` via Mathlib's
`IsOpen.isCompletelyMetrizableSpace` and `IsOpen.polishSpace`.

## Main results

* `Topology.IsOpenEmbedding.isCompletelyMetrizableSpace`: open embeddings pull back complete
  metrizability.
* `Topology.IsOpenEmbedding.polishSpace`: open embeddings pull back Polishness.
-/

public section

open Set Topology TopologicalSpace

namespace Topology.IsOpenEmbedding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- An open embedding into a completely metrizable space makes the domain completely metrizable. -/
theorem isCompletelyMetrizableSpace [IsCompletelyMetrizableSpace Y] (hf : IsOpenEmbedding f) :
    IsCompletelyMetrizableSpace X := by
  have : IsCompletelyMetrizableSpace (range f) := hf.isOpen_range.isCompletelyMetrizableSpace
  exact hf.isEmbedding.toHomeomorph.isClosedEmbedding.IsCompletelyMetrizableSpace

/-- An open embedding into a Polish space makes the domain Polish. -/
theorem polishSpace [PolishSpace Y] (hf : IsOpenEmbedding f) : PolishSpace X := by
  have : PolishSpace (range f) := hf.isOpen_range.polishSpace
  exact hf.isEmbedding.toHomeomorph.isClosedEmbedding.polishSpace

end Topology.IsOpenEmbedding
