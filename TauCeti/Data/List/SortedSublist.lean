/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Sort

/-!
# Increasing sublists under appending a letter

The recurrence below splits a bounded weakly increasing sublist according to whether it uses
the final letter. It is the word-side recurrence in Schensted's longest subsequence theorem.
-/

public section

namespace List

variable {α : Type*} [Preorder α]

/-- A bounded weakly increasing sublist of length `n + 1` after appending `x` either already
occurs in the original list, or is obtained by appending `x` to an increasing sublist of length
`n` bounded by `x`. -/
theorem exists_sortedLE_sublist_append_singleton_iff (w : List α) (x a : α) (n : ℕ) :
    (∃ s, s <+ w ++ [x] ∧ s.SortedLE ∧ s.length = n + 1 ∧ ∀ y ∈ s, y ≤ a) ↔
      (∃ s, s <+ w ∧ s.SortedLE ∧ s.length = n + 1 ∧ ∀ y ∈ s, y ≤ a) ∨
        (x ≤ a ∧ ∃ s, s <+ w ∧ s.SortedLE ∧ s.length = n ∧ ∀ y ∈ s, y ≤ x) := by
  constructor
  · rintro ⟨s, hs, hsort, hlen, hbound⟩
    obtain ⟨t, u, rfl, ht, hu⟩ := sublist_append_iff.mp hs
    rcases sublist_singleton.mp hu with rfl | rfl
    · exact Or.inl ⟨t, ht, by simpa using hsort, by simpa using hlen, by simpa using hbound⟩
    · exact Or.inr ⟨hbound x (by simp), t, ht, by grind, by simpa using hlen, by grind⟩
  · rintro (⟨s, hs, hsort, hlen, hbound⟩ | ⟨hxa, s, hs, hsort, hlen, hbound⟩)
    · exact ⟨s, sublist_append_of_sublist_left hs, hsort, hlen, hbound⟩
    · exact ⟨s ++ [x], hs.append_right [x], by grind, by simp [hlen], by grind⟩

end List
