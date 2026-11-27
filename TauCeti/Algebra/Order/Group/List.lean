/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Data.List.Sort

/-!
# Gaps between consecutive entries of a list

In an ordered group, the quotients of consecutive entries of a strictly increasing list `l`,
closed up by a strict upper bound `b` of `l`, are all greater than `1`:
`List.one_lt_of_mem_zipWith_div_tail_append_singleton`, and additively the differences of
consecutive entries are positive, `List.pos_of_mem_zipWith_sub_tail_append_singleton`.
-/

public section

namespace List

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

end List
