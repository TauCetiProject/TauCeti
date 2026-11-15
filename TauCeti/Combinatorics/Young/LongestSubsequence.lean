/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.RobinsonSchensted
public import TauCeti.Data.List.SortedSublist

import Mathlib.Data.List.MinMax

/-!
# Schensted's longest increasing subsequence theorem

The first row of the insertion tableau has the length of a longest weakly increasing
subsequence of the input word. For words without repeated letters, this is also the length
of a longest strictly increasing subsequence, in particular for permutations.

The proof follows the minimal-tail recurrence for first-row insertion: appending `x` can
extend exactly the increasing subsequences whose final letters are at most `x`. It uses
`TauCeti.rowBump` and `TauCeti.robinsonSchensted` from the existing row-insertion development.

The more precise bounded version counts first-row entries at most a given letter. It
characterizes which lengths occur among weakly increasing subsequences bounded by that letter.

## References

* C. Schensted, *Longest increasing and decreasing subsequences*,
  Canadian Journal of Mathematics 13 (1961), 179–191.
-/

public section

namespace TauCeti

open List

variable {α : Type*} [LinearOrder α]

private theorem countP_le_rowBump_iff (x a : α) {row : List α} (hrow : row.SortedLE)
    (n : ℕ) :
    n ≤ ((rowBump x row).1.countP (fun y => y ≤ a)) ↔
      n ≤ row.countP (fun y => y ≤ a) ∨
        (x ≤ a ∧ n ≤ row.countP (fun y => y ≤ x) + 1) := by
  induction row generalizing n with
  | nil =>
    by_cases hxa : x ≤ a
    · simp [hxa]
      omega
    · simp [hxa]
  | cons y row ih =>
    obtain ⟨hhead, htail⟩ := sortedLE_cons.mp hrow
    by_cases hxy : x < y
    · have hxzero : row.countP (fun z => z ≤ x) = 0 := by
        apply countP_eq_zero.mpr
        intro z hz
        simpa using not_le.mpr (hxy.trans_le (hhead z hz))
      rw [rowBump_cons_of_lt row hxy]
      by_cases hya : y ≤ a
      · have hxa := hxy.le.trans hya
        simp only [countP_cons]
        simp [hya, hxa, hxzero, not_le.mpr hxy]
        omega
      · have hazero : row.countP (fun z => z ≤ a) = 0 := by
          apply countP_eq_zero.mpr
          intro z hz
          simpa using not_le.mpr ((lt_of_not_ge hya).trans_le (hhead z hz))
        by_cases hxa : x ≤ a
        · simp [hxzero, hazero, hya, hxa, not_le.mpr hxy]
          omega
        · simp [hxzero, hazero, hya, hxa, not_le.mpr hxy]
    · rw [rowBump_cons_of_le row (not_lt.mp hxy)]
      have hi := ih htail
      by_cases hya : y ≤ a
      · cases n with
        | zero => simp
        | succ n => simpa [hya, not_lt.mp hxy, Nat.succ_le_succ_iff] using hi n
      · have hxa : ¬ x ≤ a := fun h => hya ((not_lt.mp hxy).trans h)
        simpa [hya, hxa] using hi n

/-- There is a weakly increasing subsequence of length `n`, with all letters at most `a`,
exactly when the first row of the insertion tableau has at least `n` entries at most `a`. -/
theorem exists_sortedLE_sublist_length_bounded_iff_le_countP_headD_robinsonSchensted_fst
    (w : List α) (n : ℕ) (a : α) :
    (∃ s, s <+ w ∧ s.SortedLE ∧ s.length = n ∧ ∀ y ∈ s, y ≤ a) ↔
      n ≤ ((robinsonSchensted w).1.headD []).countP (fun y => y ≤ a) := by
  induction w using reverseRecOn generalizing n a with
  | nil => simp [sortedLE_nil, eq_comm]
  | append_singleton w x ih =>
    cases n with
    | zero => simp [sortedLE_nil]
    | succ n =>
      have ht := isTableauRows_robinsonSchensted_fst w
      have hrow : ((robinsonSchensted w).1.headD []).SortedLE := by
        cases h : (robinsonSchensted w).1 with
        | nil => exact sortedLE_nil
        | cons row rows => exact (isTableauRows_cons.mp (h ▸ ht)).2.1
      rw [exists_sortedLE_sublist_append_singleton_iff, ih, ih,
        robinsonSchensted_append_singleton, headD_rowInsert,
        countP_le_rowBump_iff x a hrow]
      simp only [Nat.add_le_add_iff_right]

/-- Schensted's theorem for words: there is a weakly increasing subsequence of length `n`
exactly when `n` is at most the length of the first row of the insertion tableau. Thus this
length is attained by an increasing subsequence, and bounds the length of every such subsequence. -/
theorem exists_sortedLE_sublist_length_iff_le_length_headD_robinsonSchensted_fst
    (w : List α) (n : ℕ) :
    (∃ s, s <+ w ∧ s.SortedLE ∧ s.length = n) ↔
      n ≤ ((robinsonSchensted w).1.headD []).length := by
  cases n with
  | zero => simp [sortedLE_nil]
  | succ n =>
    constructor
    · rintro ⟨s, hs, hsort, hlen⟩
      have hpos : 0 < s.length := by omega
      have hcount :=
        (exists_sortedLE_sublist_length_bounded_iff_le_countP_headD_robinsonSchensted_fst
          w (n + 1) (s.maximum_of_length_pos hpos)).mp
          ⟨s, hs, hsort, hlen, fun _ hy => le_maximum_of_length_pos_of_mem hy hpos⟩
      exact hcount.trans countP_le_length
    · intro hlen
      have hpos : 0 < ((robinsonSchensted w).1.headD []).length := by omega
      let a := ((robinsonSchensted w).1.headD []).maximum_of_length_pos hpos
      have hcount : ((robinsonSchensted w).1.headD []).countP (fun y => y ≤ a) =
          ((robinsonSchensted w).1.headD []).length := by
        apply countP_eq_length.mpr
        intro y hy
        simpa only [decide_eq_true_eq] using le_maximum_of_length_pos_of_mem hy hpos
      obtain ⟨s, hs, hsort, hslen, _⟩ :=
        (exists_sortedLE_sublist_length_bounded_iff_le_countP_headD_robinsonSchensted_fst
          w (n + 1) a).mpr (hcount ▸ hlen)
      exact ⟨s, hs, hsort, hslen⟩

/-- Schensted's theorem for words without repeated letters, including permutation words:
there is a strictly increasing subsequence of length `n` exactly when `n` is at most the
length of the first row of the insertion tableau. -/
theorem exists_sortedLT_sublist_length_iff_le_length_headD_robinsonSchensted_fst
    (w : List α) (hw : w.Nodup) (n : ℕ) :
    (∃ s, s <+ w ∧ s.SortedLT ∧ s.length = n) ↔
      n ≤ ((robinsonSchensted w).1.headD []).length := by
  rw [← exists_sortedLE_sublist_length_iff_le_length_headD_robinsonSchensted_fst]
  constructor
  · rintro ⟨s, hs, hsort, hlen⟩
    exact ⟨s, hs, hsort.sortedLE, hlen⟩
  · rintro ⟨s, hs, hsort, hlen⟩
    exact ⟨s, hs, hsort.sortedLT_of_nodup (hw.sublist hs), hlen⟩

end TauCeti
