/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Image

/-!
# Representatives of pairs under an involution

A finite set avoiding the fixed points of an involution admits one representative from each
pair it meets. The representatives can be taken from the original set, even when that set is
not closed under the involution.
-/

public section

namespace Finset

/-- Select a subset `t` of `s` meeting each involution pair met by `s` exactly once. In particular,
a point of `s` whose partner is outside `s` must itself be selected. -/
theorem exists_subset_disjoint_image_of_involutive {α : Type*} [DecidableEq α]
    (s : Finset α) {f : α → α} (hf : Function.Involutive f) (hne : ∀ x ∈ s, f x ≠ x) :
    ∃ t ⊆ s, Disjoint t (t.image f) ∧ s ⊆ t ∪ t.image f := by
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | insert a s _ ih =>
    obtain ⟨t, hts, hdisj, hcov⟩ := ih fun x hx ↦ hne x (mem_insert_of_mem hx)
    by_cases hfa : f a ∈ t
    · refine ⟨t, hts.trans (subset_insert _ _), hdisj, ?_⟩
      simpa only [insert_subset_iff, mem_union] using
        And.intro (Or.inr (hf a ▸ mem_image_of_mem f hfa)) hcov
    · refine ⟨insert a t, insert_subset_iff.mpr ⟨mem_insert_self _ _,
        hts.trans (subset_insert _ _)⟩, ?_, ?_⟩
      · rw [image_insert, disjoint_left]
        intro x hx hx'
        rcases mem_insert.mp hx with hxa | hx
        · subst x
          rcases mem_insert.mp hx' with h | h
          · exact hne a (mem_insert_self _ _) h.symm
          · obtain ⟨y, hy, hy'⟩ := mem_image.mp h
            exact hfa (by simpa only [← hy', hf y] using hy)
        · rcases mem_insert.mp hx' with rfl | hx'
          · exact hfa hx
          · exact disjoint_left.mp hdisj hx hx'
      · rw [insert_subset_iff]
        refine ⟨mem_union_left _ (mem_insert_self _ _), hcov.trans ?_⟩
        exact union_subset_union (subset_insert _ _) (image_subset_image (subset_insert _ _))

end Finset
