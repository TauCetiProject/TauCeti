/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# Preconnected sets covered by disjoint open sets

A preconnected set covered by a family of pairwise disjoint open sets lies in each member of the
family that it meets. This is the form in which connectedness is used to show that a region
contained in a union of disjoint open cells lies in a single cell.
-/

public section

open Function Set

variable {α ι : Type*} [TopologicalSpace α]

/-- A preconnected set covered by pairwise disjoint open sets `u i` lies in each `u i` that it
meets. -/
theorem IsPreconnected.subset_of_subset_iUnion {s : Set α} {u : ι → Set α}
    (hs : IsPreconnected s) (hu : ∀ i, IsOpen (u i)) (hdisj : Pairwise (Disjoint on u))
    (hsu : s ⊆ ⋃ i, u i) {i : ι} (hsi : (s ∩ u i).Nonempty) : s ⊆ u i := by
  classical
  refine hs.subset_left_of_subset_union (v := ⋃ (j) (_ : j ≠ i), u j) (hu i)
    (isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ hu j)
    (disjoint_iUnion₂_right.2 fun j hj ↦ hdisj (Ne.symm hj)) (fun x hx ↦ ?_) hsi
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hsu hx)
  by_cases hji : j = i
  · exact Or.inl (hji ▸ hj)
  · exact Or.inr (mem_iUnion₂.2 ⟨j, hji, hj⟩)
