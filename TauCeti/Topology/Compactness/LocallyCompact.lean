/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Separation.Hausdorff

/-!
# Local compactness from local data, and lifting compact sets along open maps

A space in which every point has a locally compact neighbourhood is locally compact
(`TauCeti.locallyCompactSpace_of_forall_exists_mem_nhds`).

Along an open map out of a weakly locally compact space, every compact subset of the range lies in
the image of a compact set (`IsOpenMap.exists_isCompact_subset_image`). This is how a compactness
statement about a quotient, such as a group modulo a kernel, is pulled back to the group.

A continuous injection out of a weakly locally compact space into a Hausdorff space is a
topological embedding on an open neighbourhood of any compact set
(`Continuous.exists_opens_isEmbedding_restrict`).
-/

public section

open Set Topology

namespace TauCeti

/-- A space in which every point has a locally compact neighbourhood is locally compact. -/
theorem locallyCompactSpace_of_forall_exists_mem_nhds {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, LocallyCompactSpace U) : LocallyCompactSpace X := by
  refine ⟨fun x W hW ↦ ?_⟩
  obtain ⟨U, hU, _⟩ := h x
  have hmap := IsInducing.subtypeVal.map_nhds_of_mem (⟨x, mem_of_mem_nhds hU⟩ : U)
    (by simpa using hU)
  rw [← hmap] at hW ⊢
  obtain ⟨K, hKx, hKW, hKc⟩ := local_compact_nhds hW
  exact ⟨(↑) '' K, Filter.image_mem_map hKx, image_subset_iff.mpr hKW,
    hKc.image continuous_subtype_val⟩

end TauCeti

/-- Along an open map out of a weakly locally compact space, every compact subset of the range is
contained in the image of a compact set. -/
theorem IsOpenMap.exists_isCompact_subset_image {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [WeaklyLocallyCompactSpace X] {f : X → Y} (hf : IsOpenMap f)
    {K : Set Y} (hK : IsCompact K) (hKf : K ⊆ range f) :
    ∃ L : Set X, IsCompact L ∧ K ⊆ f '' L := by
  choose s hc hmem using fun x : X ↦ exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x ↦ f '' interior (s x))
    (fun x ↦ hf _ isOpen_interior) fun _ hy ↦ by
      obtain ⟨x, rfl⟩ := hKf hy
      exact mem_iUnion.2 ⟨x, mem_image_of_mem f (mem_interior_iff_mem_nhds.2 (hmem x))⟩
  refine ⟨⋃ x ∈ t, s x, t.isCompact_biUnion fun x _ ↦ hc x, ht.trans ?_⟩
  rw [image_iUnion₂]
  exact iUnion₂_mono fun x _ ↦ image_mono interior_subset

/-- A continuous injection from a weakly locally compact space into a Hausdorff space restricts
to a topological embedding on some open neighbourhood of any compact set. -/
theorem Continuous.exists_opens_isEmbedding_restrict {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [WeaklyLocallyCompactSpace X] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hinj : Function.Injective f) {K : Set X} (hK : IsCompact K) :
    ∃ W : TopologicalSpace.Opens X, K ⊆ W ∧ IsEmbedding fun q : W => f q := by
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have h : IsEmbedding fun q : L => f q :=
    ((hf.comp continuous_subtype_val).isClosedEmbedding
      (hinj.comp Subtype.val_injective)).isEmbedding
  exact ⟨⟨interior L, isOpen_interior⟩, hKL, h.comp (IsEmbedding.inclusion interior_subset)⟩
