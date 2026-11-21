/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TakeDrop
public import Mathlib.Order.Defs.PartialOrder

/-!
# Prefixes and suffixes of lists

For `m ≤ n`, the suffix `l.drop m` splits at the position `n` of `l` into the window
`(l.take n).drop m` of the entries `m, …, n - 1` and the suffix `l.drop n`. This is
`List.drop_take_append_drop` with the window written as a suffix of a prefix.

For every bound `N` on lists in a preorder and every length `n` there is a list of length `n`
dominating `N` along its prefixes: each entry is at least `N` of the list of the earlier entries
(`List.exists_length_eq_forall_le_getElem`).
-/

public section

namespace List

variable {α : Type*}

/-- For `m ≤ n`, the suffix `l.drop m` is the window `(l.take n).drop m` followed by the suffix
`l.drop n`. -/
theorem drop_take_append_drop_of_le (l : List α) {m n : ℕ} (h : m ≤ n) :
    (l.take n).drop m ++ l.drop n = l.drop m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [drop_take]

/-- For every bound `N` on lists in a preorder and every length `n` there is a list of length `n`
in which each entry is at least `N` of the list of the earlier entries. -/
theorem exists_length_eq_forall_le_getElem [Preorder α] (N : List α → α) (n : ℕ) :
    ∃ p : List α, p.length = n ∧ ∀ i (hi : i < p.length), N (p.take i) ≤ p[i] := by
  induction n with
  | zero => exact ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨p, hp, hN⟩ := ih
    refine ⟨p ++ [N p], by simp [hp], fun i hi => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 (by simpa using hi)) with hi' | rfl
    · simpa [take_append_of_le_length (Nat.le_of_lt hi'), getElem_append_left hi'] using hN i hi'
    · simp

end List
