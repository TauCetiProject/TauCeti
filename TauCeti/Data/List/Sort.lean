/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain

/-!
# Weakly increasing lists under appending an entry, and insertion sort

A weakly increasing list stays weakly increasing after appending an entry exactly when its last
entry, if any, is at most the new one.

For a linear order, inserting two distinct entries into a list in either order gives the same list
(`List.orderedInsert_comm`), and two lists which are permutations of each other have the same
insertion sort (`List.Perm.insertionSort_eq`).
-/

public section

namespace List

variable {α : Type*} [Preorder α]

/-- A list followed by one more entry is weakly increasing exactly when the list is, and its last
entry, if any, is at most the new entry. -/
theorem sortedLE_append_singleton {l : List α} {a : α} :
    (l ++ [a]).SortedLE ↔ l.SortedLE ∧ ∀ b ∈ l.getLast?, b ≤ a := by
  rw [sortedLE_iff_isChain, sortedLE_iff_isChain, isChain_append]
  cases l.getLast? <;> simp

section LinearOrder

variable {β : Type*} [LinearOrder β]

/-- Inserting two distinct entries into a list in either order gives the same list. -/
theorem orderedInsert_comm {a b : β} (hab : a ≠ b) (s : List β) :
    (s.orderedInsert (· ≤ ·) b).orderedInsert (· ≤ ·) a =
      (s.orderedInsert (· ≤ ·) a).orderedInsert (· ≤ ·) b := by
  induction s with
  | nil => rcases lt_or_gt_of_ne hab with h | h <;> simp [h.le, not_le.2 h]
  | cons c s ih =>
    by_cases ha : a ≤ c <;> by_cases hb : b ≤ c
    · rcases lt_or_gt_of_ne hab with h | h <;> simp [ha, hb, h.le, not_le.2 h]
    · have hba : ¬ b ≤ a := fun h ↦ hb (h.trans ha)
      simp [ha, hb, hba]
    · have hab' : ¬ a ≤ b := fun h ↦ ha (h.trans hb)
      simp [ha, hb, hab']
    · simp [ha, hb, ih]

/-- Two lists which are permutations of each other have the same insertion sort. -/
theorem Perm.insertionSort_eq {l l' : List β} (h : l.Perm l') :
    l.insertionSort (· ≤ ·) = l'.insertionSort (· ≤ ·) :=
  Perm.eq_of_sortedLE sortedLE_insertionSort sortedLE_insertionSort
    ((perm_insertionSort _ l).trans (h.trans (perm_insertionSort _ l').symm))

end LinearOrder

end List
