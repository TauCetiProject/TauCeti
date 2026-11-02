/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Topology

/-!
# Interiors of convex sets

A convex set symmetric about the origin has `0` in its interior as soon as its interior is
nonempty. This lets volume arguments obtain the neighbourhood of the origin needed to use the
gauge of a symmetric convex set.

The interior of a sum of two convex sets with nonempty interiors is the sum of their
interiors. In particular, this describes the interior of the sum of two interval supports.
-/

public section

open Set
open scoped Pointwise

/-- The interior of a sum of convex sets with nonempty interiors is the sum of their
interiors. -/
theorem Convex.interior_add {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {s t : Set E} (hs : Convex 𝕜 s)
    (ht : Convex 𝕜 t) (hsne : (interior s).Nonempty) (htne : (interior t).Nonempty) :
    interior (s + t) = interior s + interior t := by
  have hopen : IsOpen (interior s + interior t) := isOpen_interior.add_left
  have hne : (interior (interior s + interior t)).Nonempty := by
    rw [hopen.interior_eq]
    exact add_nonempty.mpr ⟨hsne, htne⟩
  have hs' : s ⊆ closure (interior s) := by
    rw [hs.closure_interior_eq_closure_of_nonempty_interior hsne]
    exact subset_closure
  have ht' : t ⊆ closure (interior t) := by
    rw [ht.closure_interior_eq_closure_of_nonempty_interior htne]
    exact subset_closure
  have hsub : s + t ⊆ closure (interior s + interior t) := by
    rw [← add_image_prod, ← add_image_prod]
    exact (image_mono (Set.prod_mono hs' ht')).trans (by
      rw [← closure_prod_eq]
      exact image_closure_subset_closure_image (continuous_fst.add continuous_snd))
  refine subset_antisymm ?_ subset_interior_add
  calc
    interior (s + t) ⊆ interior (closure (interior s + interior t)) := interior_mono hsub
    _ = interior s + interior t := by
      rw [(hs.interior.add ht.interior).interior_closure_eq_interior_of_nonempty_interior hne,
        hopen.interior_eq]

/-- A convex set symmetric about the origin with nonempty interior has the origin in its
interior. -/
theorem Convex.zero_mem_interior_of_symmetric {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] {s : Set E} (hs : Convex 𝕜 s)
    (hsymm : ∀ x ∈ s, -x ∈ s) (hi : (interior s).Nonempty) :
    (0 : E) ∈ interior s := by
  obtain ⟨x, hx⟩ := hi
  have hx' : -x ∈ interior s := (Homeomorph.neg E).isOpenMap.mapsTo_interior hsymm hx
  simpa using hs.interior hx hx' (by norm_num : (0 : 𝕜) ≤ 1 / 2)
    (by norm_num : (0 : 𝕜) ≤ 1 / 2) (by norm_num)
