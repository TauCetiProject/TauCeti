/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Basic

/-!
# Closed embeddings out of an empty space

Every map out of an empty space is a closed embedding. Mathlib proves the open version
(`Topology.IsOpenEmbedding.of_isEmpty`); this file supplies the closed one.
-/

public section

namespace Topology.IsClosedEmbedding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every map out of an empty space is a closed embedding. -/
theorem of_isEmpty [IsEmpty X] (f : X → Y) : IsClosedEmbedding f :=
  ⟨.of_subsingleton f, by simp [Set.range_eq_empty]⟩

end Topology.IsClosedEmbedding
