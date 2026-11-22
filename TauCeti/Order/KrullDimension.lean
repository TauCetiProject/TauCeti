/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.KrullDimension

/-!
# Krull dimension of a union of upper sets

A strict chain in a union of two upper sets lies entirely in the set that contains its first
element, so the Krull dimension of the union is the larger of the two Krull dimensions
(`Order.krullDim_union_of_isUpperSet`). In a prime spectrum the closed sets are upper sets for
the inclusion order, so this computes the dimension of a union of two closed subsets, for instance
the support of `M ⧸ r s M` as the union of the supports of `M ⧸ r M` and `M ⧸ s M`.
-/

public section

namespace Order

variable {α : Type*} [Preorder α]

/-- The Krull dimension of a union of two upper sets is the larger of their Krull dimensions. -/
theorem krullDim_union_of_isUpperSet {s t : Set α} (hs : IsUpperSet s) (ht : IsUpperSet t) :
    krullDim ↥(s ∪ t) = max (krullDim ↥s) (krullDim ↥t) := by
  refine le_antisymm ?_ (max_le
    (krullDim_le_of_strictMono (Set.inclusion Set.subset_union_left) fun _ _ h ↦ h)
    (krullDim_le_of_strictMono (Set.inclusion Set.subset_union_right) fun _ _ h ↦ h))
  refine iSup_le fun p ↦ ?_
  -- The whole chain lies in whichever of `s` and `t` contains its first element.
  have hmem {u : Set α} (hu : IsUpperSet u) (h : (p.head : α) ∈ u) (i : Fin (p.length + 1)) :
      (p i : α) ∈ u :=
    hu (p.monotone (Fin.zero_le i)) h
  rcases p.head.property with h | h
  · exact le_max_of_le_left (LTSeries.length_le_krullDim
      ⟨p.length, fun i ↦ ⟨p i, hmem hs h i⟩, fun i ↦ p.step i⟩)
  · exact le_max_of_le_right (LTSeries.length_le_krullDim
      ⟨p.length, fun i ↦ ⟨p i, hmem ht h i⟩, fun i ↦ p.step i⟩)

end Order
