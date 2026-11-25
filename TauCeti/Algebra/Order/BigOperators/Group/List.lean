/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.List.Sort
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
# Gaps between prefix products

In a canonically ordered monoid, prefix products `(L.take k).prod` grow with `k`
(`List.monotone_prod_take`). If every entry of `L` is at least `c`, then a later prefix product
exceeds an earlier one by a factor of at least `c`, as long as the earlier prefix stops before
the end of the list: `List.prod_take_mul_le_prod_take`, and additively
`List.sum_take_add_le_sum_take`.

## Gaps between consecutive entries

In an ordered group, the quotients of consecutive entries of a strictly increasing list `l`,
closed up by a strict upper bound `b` of `l`, are all greater than `1`:
`List.one_lt_of_mem_zipWith_div_tail_append_singleton`, and additively the differences of
consecutive entries are positive, `List.pos_of_mem_zipWith_sub_tail_append_singleton`. Their
entries are described by `List.getElem_zipWith_sub_tail_append_singleton`. In a strictly
increasing list the next entry is the least entry above the current one
(`List.SortedLT.isLeast_inter_Ioi_getElem_succ`) and the last entry is the greatest
(`List.SortedLT.isGreatest_getElem_of_not_succ_lt`).
-/

public section

namespace List

section Take

variable {M : Type*} [Monoid M] [Preorder M] [MulLeftMono M] [CanonicallyOrderedMul M]

/-- If every entry of `L` is at least `c`, then for `j < k` with `j < L.length` the prefix
product `(L.take k).prod` is at least `(L.take j).prod * c`. -/
@[to_additive /-- If every entry of `L` is at least `c`, then for `j < k` with `j < L.length`
the prefix sum `(L.take k).sum` is at least `(L.take j).sum + c`. -/]
theorem prod_take_mul_le_prod_take {L : List M} {c : M} (h : ∀ a ∈ L, c ≤ a) {j k : ℕ}
    (hjk : j < k) (hj : j < L.length) : (L.take j).prod * c ≤ (L.take k).prod :=
  calc (L.take j).prod * c ≤ (L.take j).prod * L[j] := by
        gcongr
        exact h _ (getElem_mem hj)
    _ = (L.take (j + 1)).prod := (prod_take_succ L j hj).symm
    _ ≤ (L.take k).prod := monotone_prod_take L hjk

end Take

section Consecutive

variable {G : Type*} [Group G] [Preorder G] [MulRightStrictMono G]

/-- The quotients of consecutive entries of a strictly increasing list `l`, closed up by a strict
upper bound `b` of `l`, are greater than `1`. -/
@[to_additive /-- The differences of consecutive entries of a strictly increasing list `l`, closed
up by a strict upper bound `b` of `l`, are positive. -/]
theorem one_lt_of_mem_zipWith_div_tail_append_singleton {b : G} {l : List G} (hl : l.SortedLT)
    (hb : ∀ x ∈ l, x < b) {g : G} (hg : g ∈ zipWith (· / ·) (l.tail ++ [b]) l) : 1 < g := by
  rw [sortedLT_iff_pairwise] at hl
  induction l with
  | nil => simp at hg
  | cons a l ih =>
    cases l with
    | nil =>
      obtain rfl : g = b / a := by simpa using hg
      exact one_lt_div'.2 (hb a mem_cons_self)
    | cons c l =>
      rw [tail_cons, cons_append, zipWith_cons_cons, mem_cons] at hg
      rcases hg with rfl | hg
      · exact one_lt_div'.2 (rel_of_pairwise_cons hl mem_cons_self)
      · exact ih hl.of_cons (fun x hx => hb x (mem_cons_of_mem _ hx)) (by simpa using hg)

end Consecutive

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
