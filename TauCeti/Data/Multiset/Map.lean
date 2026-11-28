/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.MapFold

/-!
# Submultisets of an image

A submultiset of the image `s.map f` of a multiset is itself the image of a submultiset of `s`
(`Multiset.le_map_iff`). This is the multiset form of `List.sublist_map_iff`: occurrences of
`s.map f` are selected by selecting the occurrences of `s` they come from, even when several of
them have the same image.
-/

public section

namespace Multiset

variable {α β : Type*}

/-- A submultiset of `s.map f` is the image of a submultiset of `s`. -/
theorem le_map_iff {f : α → β} {s : Multiset α} {t : Multiset β} :
    t ≤ s.map f ↔ ∃ u ≤ s, t = u.map f := by
  classical
  refine ⟨fun ht => ?_, fun ⟨u, hu, ht⟩ => ht ▸ map_le_map hu⟩
  induction s using Multiset.induction_on generalizing t with
  | empty =>
    rw [Multiset.map_zero] at ht
    exact ⟨0, le_rfl, by rw [Multiset.map_zero, ← Multiset.le_zero]; exact ht⟩
  | cons a s ih =>
    rw [map_cons] at ht
    by_cases ha : f a ∈ t
    · obtain ⟨t, rfl⟩ := exists_cons_of_mem ha
      obtain ⟨u, hu, rfl⟩ := ih ((cons_le_cons_iff _).1 ht)
      exact ⟨a ::ₘ u, (cons_le_cons_iff _).2 hu, by simp⟩
    · obtain ⟨u, hu, rfl⟩ := ih ((le_cons_of_notMem ha).1 ht)
      exact ⟨u, hu.trans (le_cons_self _ _), rfl⟩

end Multiset
