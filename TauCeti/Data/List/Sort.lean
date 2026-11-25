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
# Weakly increasing lists under appending an entry

A weakly increasing list stays weakly increasing after appending an entry exactly when its last
entry, if any, is at most the new one.

## Consecutive entries of a strictly increasing list

In a strictly increasing list the next entry is the least entry above the current one
(`List.SortedLT.isLeast_inter_Ioi_getElem_succ`) and the last entry is the greatest
(`List.SortedLT.isGreatest_getElem_of_not_succ_lt`).
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

section Entries

variable {α : Type*} [LinearOrder α] {l : List α}

/-- In a strictly increasing list, the entry after `l[i]` is the least entry above `l[i]`. -/
theorem SortedLT.isLeast_inter_Ioi_getElem_succ (hl : l.SortedLT) {i : ℕ}
    (h : i + 1 < l.length) : IsLeast ({x | x ∈ l} ∩ Set.Ioi l[i]) l[i + 1] := by
  refine ⟨⟨getElem_mem _, Set.mem_Ioi.2 (hl.getElem_lt_getElem_iff.2 (by omega))⟩,
    fun x ⟨hx, hix⟩ => ?_⟩
  obtain ⟨k, hk, rfl⟩ := mem_iff_getElem.1 hx
  exact hl.getElem_le_getElem_iff.2 (by have := hl.getElem_lt_getElem_iff.1 hix; omega)

/-- In a strictly increasing list, the last entry is the greatest entry. -/
theorem SortedLT.isGreatest_getElem_of_not_succ_lt (hl : l.SortedLT) {i : ℕ} (hi : i < l.length)
    (h : ¬i + 1 < l.length) : IsGreatest {x | x ∈ l} l[i] := by
  refine ⟨getElem_mem _, fun x hx => ?_⟩
  obtain ⟨k, hk, rfl⟩ := mem_iff_getElem.1 hx
  exact hl.getElem_le_getElem_iff.2 (by omega)

end Entries

end List
