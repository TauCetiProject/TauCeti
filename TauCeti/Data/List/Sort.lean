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

The entries of the differences of consecutive entries, closed up by an extra entry `b`, are
described by `List.getElem_zipWith_sub_tail_append_singleton`. In a strictly increasing list the
next entry is the least entry above the current one
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

/-- The entry at `i` of the differences of consecutive entries of `l`, closed up by `b`, is the
difference from `l[i]` to the next entry of `l`, or to `b` at the last index. -/
theorem getElem_zipWith_sub_tail_append_singleton {G : Type*} [Sub G] {b : G} {l : List G}
    {i : ℕ} (hi : i < (zipWith (· - ·) (l.tail ++ [b]) l).length) :
    (zipWith (· - ·) (l.tail ++ [b]) l)[i] =
      (if h : i + 1 < l.length then l[i + 1] else b) - l[i]'(by simp at hi; omega) := by
  rw [getElem_zipWith]
  split_ifs with h
  · rw [getElem_append_left (by simp; omega), getElem_tail]
  · rw [getElem_append_right (by simp; omega)]
    simp

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
