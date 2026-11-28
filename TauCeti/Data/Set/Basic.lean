/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Basic
import Mathlib.Order.BooleanAlgebra.Set

/-!
# Basic set identities

This file collects elementary set identities for intersections, unions, and set differences.

## Main results

* `Set.inter_eq_singleton_of_subset`: shrinking one side of an intersection contained in a
  singleton while retaining the shared point gives equality with that singleton.
* `Set.union_sdiff_sdiff_inter`: removing `f \ (s ∩ f)` from `s ∪ f` recovers `s`.
* `Set.inter_eq_of_inter_eq_union`: shrinking the right factor of an intersection `a ∩ b = j ∪ g`
  to a subset `b' ⊆ b` containing `j` with `g ∩ b' ⊆ j` leaves `a ∩ b' = j`.
-/

public section

namespace Set

variable {α : Type*}

/-- Shrink the second side of an intersection `a ∩ s ⊆ {x}` to `b ⊆ s` while retaining the shared
point `x`. -/
theorem inter_eq_singleton_of_subset {a b s : Set α} {x : α}
    (has : a ∩ s ⊆ {x}) (hbs : b ⊆ s) (hxa : x ∈ a) (hxb : x ∈ b) :
    a ∩ b = {x} :=
  Subset.antisymm ((inter_subset_inter_right a hbs).trans has)
    (singleton_subset_iff.mpr ⟨hxa, hxb⟩)

/-- Removing `f \ (s ∩ f)` from `s ∪ f` recovers `s`. -/
theorem union_sdiff_sdiff_inter (s f : Set α) :
    (s ∪ f) \ (f \ (s ∩ f)) = s := by
  rw [sdiff_sdiff_eq_sdiff_union (inter_subset_left.trans subset_union_left),
    union_sdiff_right, sdiff_union_inter]

/-- If `a ∩ b = j ∪ g`, `b' ⊆ b` contains `j`, and `g ∩ b' ⊆ j`, then `a ∩ b' = j`. -/
theorem inter_eq_of_inter_eq_union {a b b' g j : Set α}
    (hab : a ∩ b = j ∪ g) (hb' : b' ⊆ b) (hjb' : j ⊆ b') (hg : g ∩ b' ⊆ j) :
    a ∩ b' = j := by
  refine Subset.antisymm (fun z ⟨hza, hzb'⟩ => ?_)
    (subset_inter ((hab ▸ subset_union_left).trans inter_subset_left) hjb')
  have hz : z ∈ a ∩ b := ⟨hza, hb' hzb'⟩
  rw [hab] at hz
  rcases hz with hzj | hzg
  · exact hzj
  · exact hg ⟨hzg, hzb'⟩

end Set
