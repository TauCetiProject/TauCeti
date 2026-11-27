/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Basic

/-!
# Lemmas for topological embeddings

This file provides general lemmas about topological embeddings (`Topology.IsEmbedding`), including
`Topology.IsEmbedding.closure_image_subset_range_of_comp`: if `j : X → Y` is an embedding and the
closure of `(j ∘ i) '' s` lies in `Set.range (j ∘ i)`, then the closure of `i '' s` lies in
`Set.range i`.
-/

public section

open Set

namespace Topology.IsEmbedding

/-- If `j : X → Y` is a topological embedding and the closure of `(j ∘ i) '' s` lies in
`Set.range (j ∘ i)`, then the closure of `i '' s` lies in `Set.range i`. -/
theorem closure_image_subset_range_of_comp {W X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {i : W → X} {j : X → Y} (hj : IsEmbedding j) {s : Set W}
    (hs : closure ((j ∘ i) '' s) ⊆ Set.range (j ∘ i)) :
    closure (i '' s) ⊆ Set.range i := by
  rw [hj.closure_eq_preimage_closure_image]
  intro v hv
  have hv' : j v ∈ closure ((j ∘ i) '' s) := by
    simpa only [Set.mem_preimage, Set.image_image, Function.comp_apply] using hv
  obtain ⟨w, hw⟩ := hs hv'
  exact ⟨w, hj.injective hw⟩

end Topology.IsEmbedding
