/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Preferred trivializations near points and over compact subsets

Near a point `v₀` of the total space of a fibre bundle, every point lies over the base set of the
preferred trivialization at the base point `v₀.proj`, so it can be read in that trivialization.
A compact subset of the total space lies over finitely many preferred trivializing base sets.

## Main results

* `Bundle.TotalSpace.eventually_proj_mem_baseSet_trivializationAt`: near `v₀`, points lie over
  the base set of the trivialization at `v₀.proj`.
* `IsCompact.exists_finset_subset_preimage_biUnion_baseSet`: a compact subset of the total
  space lies over a finite union of preferred trivializing base sets.
-/

public section

open Bundle Filter Set
open scoped Topology

namespace Bundle.TotalSpace

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

/-- Near a point `v₀` of the total space, every point lies over the base set of the
trivialization at `v₀.proj`. -/
theorem eventually_proj_mem_baseSet_trivializationAt (v₀ : TotalSpace F E) :
    ∀ᶠ v in 𝓝 v₀, v.proj ∈ (trivializationAt F E v₀.proj).baseSet :=
  (FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds
    ((trivializationAt F E v₀.proj).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' v₀.proj))

end Bundle.TotalSpace

/-- A compact subset of a fibre bundle's total space lies over a finite union of the
chosen trivializing base sets. -/
theorem IsCompact.exists_finset_subset_preimage_biUnion_baseSet
    {B : Type*} [TopologicalSpace B] {F : Type*} [TopologicalSpace F]
    {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    {K : Set (TotalSpace F E)} (hK : IsCompact K) :
    ∃ s : Finset B, K ⊆ π F E ⁻¹' ⋃ b ∈ s, (trivializationAt F E b).baseSet := by
  obtain ⟨s, hs⟩ := (hK.image (FiberBundle.continuous_proj F E)).elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩)
  exact ⟨s, fun p hp ↦ hs (mem_image_of_mem _ hp)⟩
