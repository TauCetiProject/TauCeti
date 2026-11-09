/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Card

/-!
# Counting letters in prefixes of `List.ofFn`

The number of occurrences of a letter `s` among the first `j` letters of the word
`f 0, …, f (k - 1)` is the number of positions `a < j` with `f a = s`
(`List.count_take_ofFn`). This is the occurrence-count form of `List.sum_take_ofFn`.
-/

public section

open Finset

namespace List

/-- The number of occurrences of `s` among the first `j` letters of `List.ofFn f` is the number of
positions before `j` at which `f` takes the value `s`. -/
theorem count_take_ofFn {α : Type*} [DecidableEq α] {k : ℕ} (f : Fin k → α) (s : α) (j : ℕ) :
    ((ofFn f).take j).count s = #{a : Fin k | (a : ℕ) < j ∧ f a = s} := by
  induction j with
  | zero => simp
  | succ j ih =>
    -- Split off the position `j` from the positions before `j + 1`.
    simp_rw [Nat.lt_succ_iff_lt_or_eq, or_and_right, filter_or]
    rw [card_union_of_disjoint (disjoint_filter.mpr fun a _ h h' => by omega), ← ih,
      take_add_one, count_append, List.getElem?_ofFn]
    congr 1
    by_cases hj : j < k
    · have hfilt : ({a : Fin k | (a : ℕ) = j ∧ f a = s} : Finset (Fin k)) =
          ({⟨j, hj⟩} : Finset (Fin k)).filter (f · = s) := by
        ext a
        simp [Fin.ext_iff]
      rw [hfilt, Finset.filter_singleton]
      split_ifs with hs <;> simp [hs]
    · rw [card_eq_zero.mpr (filter_eq_empty_iff.mpr fun a _ ⟨h, _⟩ => hj (h ▸ a.isLt))]
      simp [hj]

end List
