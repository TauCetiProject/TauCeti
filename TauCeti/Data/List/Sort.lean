/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Sort
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.List.Chain

/-!
# Weakly increasing lists under appending an entry, and insertion sort

A weakly increasing list stays weakly increasing after appending an entry exactly when its last
entry, if any, is at most the new one.

For a linear order, inserting two entries into a list in either order gives the same list
(`List.orderedInsert_comm`), and two lists which are permutations of each other have the same
insertion sort (`List.Perm.insertionSort_eq`).

## Consecutive entries of a sorted list

In a strictly increasing list the next entry is the least entry above the current one
(`List.SortedLT.isLeast_inter_Ioi_getElem_succ`), and in a weakly increasing list the last
entry is the greatest (`List.SortedLE.isGreatest_getElem_of_not_succ_lt`).
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

/-- Inserting two entries into a list in either order gives the same list. -/
theorem orderedInsert_comm (a b : β) (s : List β) :
    (s.orderedInsert (· ≤ ·) b).orderedInsert (· ≤ ·) a =
      (s.orderedInsert (· ≤ ·) a).orderedInsert (· ≤ ·) b := by
  rcases eq_or_ne a b with rfl | hab
  · rfl
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

section Entries

variable {l : List α}

/-- In a strictly increasing list, the entry after `l[i]` is the least entry above `l[i]`. -/
theorem SortedLT.isLeast_inter_Ioi_getElem_succ (hl : l.SortedLT) {i : ℕ}
    (h : i + 1 < l.length) : IsLeast ({x | x ∈ l} ∩ Set.Ioi l[i]) l[i + 1] := by
  refine ⟨⟨getElem_mem _, Set.mem_Ioi.2 (hl.getElem_lt_getElem_of_lt (Nat.lt_succ_self i))⟩,
    fun x ⟨hx, hix⟩ => ?_⟩
  obtain ⟨k, hk, rfl⟩ := mem_iff_getElem.1 hx
  refine hl.sortedLE.getElem_le_getElem_of_le (Nat.succ_le_of_lt (lt_of_not_ge fun hki => ?_))
  exact lt_irrefl _ ((Set.mem_Ioi.1 hix).trans_le (hl.sortedLE.getElem_le_getElem_of_le hki))

/-- In a weakly increasing list, the last entry is the greatest entry. -/
theorem SortedLE.isGreatest_getElem_of_not_succ_lt (hl : l.SortedLE) {i : ℕ} (hi : i < l.length)
    (h : ¬i + 1 < l.length) : IsGreatest {x | x ∈ l} l[i] := by
  refine ⟨getElem_mem _, fun x hx => ?_⟩
  obtain ⟨k, hk, rfl⟩ := mem_iff_getElem.1 hx
  exact hl.getElem_le_getElem_of_le (by omega)

end Entries

end List
