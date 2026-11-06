/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Separation.Regular

/-!
# Local compactness from an open cover, and lifting compact sets along open maps

Local compactness follows from an open cover whose members are locally compact.

Along an open surjection out of a weakly locally compact space, every compact subset of the
codomain lies in the image of a compact set. This is how a compactness statement about a quotient,
such as a group modulo a kernel, is pulled back to the group.

A continuous injection out of a locally compact space into a Hausdorff space is a
topological embedding on an open neighbourhood of any compact set
(`Continuous.exists_opens_isEmbedding_restrict`).
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

/-- Along an open surjection out of a weakly locally compact space, every compact subset of the
codomain is contained in the image of a compact set. -/
theorem IsOpenMap.exists_isCompact_subset_image {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [WeaklyLocallyCompactSpace X] {f : X → Y} (hf : IsOpenMap f)
    (hsurj : Function.Surjective f) {K : Set Y} (hK : IsCompact K) :
    ∃ L : Set X, IsCompact L ∧ K ⊆ f '' L := by
  choose g hg using hsurj
  choose s hc hmem using fun x : X ↦ exists_compact_mem_nhds x
  obtain ⟨I, -, hIK⟩ := hK.elim_nhds_subcover (fun y ↦ f '' s (g y)) fun y _ ↦ by
    simpa only [hg] using hf.image_mem_nhds (hmem (g y))
  refine ⟨⋃ y ∈ I, s (g y), I.isCompact_biUnion fun _ _ ↦ hc _, ?_⟩
  rwa [image_iUnion₂]

/-- A continuous injection from a locally compact space into a Hausdorff space restricts
to a topological embedding on some open neighbourhood of any compact set. -/
theorem Continuous.exists_opens_isEmbedding_restrict {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [LocallyCompactSpace X] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hinj : Function.Injective f) {K : Set X} (hK : IsCompact K) :
    ∃ W : TopologicalSpace.Opens X, K ⊆ W ∧ IsEmbedding fun q : W => f q := by
  have := T2Space.of_injective_continuous hinj hf
  obtain ⟨W, hW, hKW, -, hcW⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ _)
  have : CompactSpace (closure W) := isCompact_iff_compactSpace.mp hcW
  have h : IsEmbedding fun q : closure W => f q :=
    ((hf.comp continuous_subtype_val).isClosedEmbedding
      (hinj.comp Subtype.val_injective)).isEmbedding
  exact ⟨⟨W, hW⟩, hKW, h.comp (IsEmbedding.inclusion (subset_closure : W ⊆ closure W))⟩
