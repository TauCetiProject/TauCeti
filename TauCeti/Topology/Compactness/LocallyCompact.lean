/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Local compactness from an open cover

Local compactness follows from an open cover whose members are locally compact.
-/

public section

open Set Topology

namespace TauCeti

/-- A space covered by locally compact open subspaces is locally compact. -/
theorem locallyCompactSpace_of_isOpen_cover {X ι : Type*} [TopologicalSpace X]
    {U : ι → Set X} (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    [∀ i, LocallyCompactSpace (U i)] : LocallyCompactSpace X := by
  refine ⟨fun x W hW ↦ ?_⟩
  obtain ⟨i, hi⟩ := iUnion_eq_univ_iff.mp hcover x
  let f : U i → X := Subtype.val
  have hf : IsOpenEmbedding f := (hU i).isOpenEmbedding_subtypeVal
  obtain ⟨K, hKx, hKW, hKc⟩ := local_compact_nhds
    (hf.continuous.continuousAt.preimage_mem_nhds hW : f ⁻¹' W ∈ 𝓝 ⟨x, hi⟩)
  refine ⟨f '' K, hf.isOpenMap.image_mem_nhds hKx, ?_, hKc.image hf.continuous⟩
  exact image_subset_iff.mpr hKW

end TauCeti
