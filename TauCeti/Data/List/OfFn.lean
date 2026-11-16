/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Lemmas on `List.ofFn`

* `List.count_take_ofFn`: the number of occurrences of a letter `s` among the first `j` letters of
  the word `f 0, …, f (k - 1)` is the number of positions `a < j` with `f a = s`. This is the
  occurrence-count form of `List.sum_take_ofFn`.
* `List.ofFn_insertNth_perm`: inserting `a` at any position `p` of `f : Fin j → α` via
  `Fin.insertNth` yields a permutation of `a :: List.ofFn f`.
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

/-- Inserting `a` at any position `p` of `f : Fin j → α` via `Fin.insertNth` yields a permutation
of `a :: List.ofFn f`. -/
theorem ofFn_insertNth_perm {α : Type*} :
    ∀ {j : ℕ} (p : Fin (j + 1)) (a : α) (f : Fin j → α),
      (ofFn (p.insertNth a f)).Perm (a :: ofFn f)
  | 0, p, _, _ => p.cases (by simp) fun i => i.elim0
  | _ + 1, p, a, f =>
      p.cases (by simp) fun q => by
        conv_lhs => rw [← Fin.cons_self_tail f, Fin.insertNth_succ_cons, ofFn_succ]
        conv_rhs => rw [← Fin.cons_self_tail f, ofFn_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact ((ofFn_insertNth_perm q a (Fin.tail f)).cons (f 0)).trans (Perm.swap a (f 0) _)

end List
