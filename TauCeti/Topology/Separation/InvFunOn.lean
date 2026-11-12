/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuity of inverses of maps out of compact sets

A continuous injection from a compact space to a Hausdorff space is a closed embedding. This file
records the version of that fact needed for the characteristic maps of cells: let `f` be continuous
on a compact set `K`, with values in a Hausdorff space, injective on a subset `U ⊆ K`, and assume no
point of `K \ U` has the same image as a point of `U`. Then the inverse `Function.invFunOn f U` is
continuous on `f '' U` (`ContinuousOn.continuousOn_invFunOn_image_of_isCompact`). For a cell, `K`
is the closed unit ball, `U` the open unit ball, and the boundary sphere is mapped outside the open
cell.

The proof is the closed map argument: the preimage under the inverse of a closed set `C` is the
trace on `f '' U` of the compact, hence closed, set `f '' (C ∩ K)`.
-/

public section

open Function Set

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- **Inverses of maps out of compact sets are continuous.** If `f` is continuous on a compact set
`K` with values in a Hausdorff space, injective on `U ⊆ K`, and no point of `K \ U` has the same
image as a point of `U`, then the inverse `invFunOn f U` of `f` on `U` is continuous on `f '' U`.
-/
theorem ContinuousOn.continuousOn_invFunOn_image_of_isCompact [Nonempty α] [T2Space β]
    {f : α → β} {K U : Set α} (hf : ContinuousOn f K) (hK : IsCompact K) (hUK : U ⊆ K)
    (hinj : InjOn f U) (hdisj : Disjoint (f '' (K \ U)) (f '' U)) :
    ContinuousOn (invFunOn f U) (f '' U) := by
  refine continuousOn_iff_isClosed.2 fun C hC ↦
    ⟨f '' (C ∩ K), ((hK.inter_left hC).image_of_continuousOn (hf.mono inter_subset_right)).isClosed,
      ?_⟩
  ext y
  simp only [mem_inter_iff, mem_preimage]
  refine ⟨fun ⟨hyC, hy⟩ ↦ ⟨?_, hy⟩, fun ⟨⟨k, ⟨hkC, hkK⟩, hky⟩, hy⟩ ↦ ⟨?_, hy⟩⟩
  · exact ⟨invFunOn f U y, ⟨hyC, hUK (invFunOn_mem hy)⟩, invFunOn_eq hy⟩
  · -- A point of `K` with image in `f '' U` lies in `U`, so it is the chosen preimage.
    have hkU : k ∈ U := by
      by_contra hkU
      exact disjoint_left.1 hdisj ⟨k, ⟨hkK, hkU⟩, hky⟩ hy
    rwa [← hky, hinj.leftInvOn_invFunOn hkU]

end
