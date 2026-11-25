/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Compact sets read through an open partial homeomorphism

For an open partial homeomorphism `e : X → Y`, a compact subset `K` of the target and a closed
set `s` of `X`, the points of `K` sent by `e.symm` into `s` form a compact set
(`OpenPartialHomeomorph.isCompact_inter_preimage_symm`). No separation axiom is needed: the set is
the image under `e` of the compact set `e.symm '' K ∩ s`. For instance, the points of the support
of a test function on a chart target that lie, read on the manifold, in the support of a function
on the manifold form a compact set.
-/

public section

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The points of a compact subset `K` of the target of `e` sent by `e.symm` into a closed set `s`
form a compact set: it is the image under `e` of the compact set `e.symm '' K ∩ s`. -/
theorem isCompact_inter_preimage_symm (e : OpenPartialHomeomorph X Y) {K : Set Y}
    (hK : IsCompact K) (hKt : K ⊆ e.target) {s : Set X} (hs : IsClosed s) :
    IsCompact (K ∩ e.symm ⁻¹' s) := by
  have heq : K ∩ e.symm ⁻¹' s = e '' (e.symm '' K ∩ s) := by
    ext y
    refine ⟨fun ⟨hyK, hys⟩ ↦ ⟨e.symm y, ⟨mem_image_of_mem _ hyK, hys⟩, e.right_inv (hKt hyK)⟩, ?_⟩
    rintro ⟨_, ⟨⟨z, hzK, rfl⟩, hzs⟩, rfl⟩
    rw [e.right_inv (hKt hzK)]
    exact ⟨hzK, hzs⟩
  rw [heq]
  exact ((hK.image_of_continuousOn (e.continuousOn_symm.mono hKt)).inter_right hs)
    |>.image_of_continuousOn <| e.continuousOn.mono <| inter_subset_left.trans <|
      image_subset_iff.2 fun _ hy ↦ e.map_target (hKt hy)

end OpenPartialHomeomorph
