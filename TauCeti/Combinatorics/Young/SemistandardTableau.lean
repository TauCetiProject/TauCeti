/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Young.SemistandardTableau

/-!
# Order properties of semistandard Young tableaux

Mathlib's `SemistandardYoungTableau` records that entries increase weakly along each row and
strictly down each column, each within a single row or column. This file derives the order facts
that combine these conditions across several rows and columns: an entry is bounded by any entry
weakly below and to the right of it, and, since the entries start at `0` and increase strictly down
each column, the entry in row `i` is at least `i`.

The material is kept in its own module, upstream of the content and Kostka-number theory, so that
these basic order facts about tableaux do not oblige a consumer to import that theory.

## Main declarations

* `SemistandardYoungTableau.entry_le_of_le`: entries increase weakly to the right and downwards.
* `SemistandardYoungTableau.le_entry`: the entry in row `i` is at least `i`.
-/

public section

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- The entries of a semistandard Young tableau increase weakly to the right and downwards. -/
theorem entry_le_of_le (T : SemistandardYoungTableau μ) {i₁ i₂ j₁ j₂ : ℕ} (hi : i₁ ≤ i₂)
    (hj : j₁ ≤ j₂) (hc : ((i₂, j₂) : ℕ × ℕ) ∈ μ) : T i₁ j₁ ≤ T i₂ j₂ :=
  (T.row_weak_of_le hj (μ.up_left_mem hi le_rfl hc)).trans (T.col_weak hi hc)

/-- The entries of a semistandard Young tableau increase strictly down a column, so the entry in
row `i` is at least `i`. -/
theorem le_entry (T : SemistandardYoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) : i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    exact Nat.succ_le_of_lt <|
      (ih (μ.up_left_mem m.le_succ le_rfl h)).trans_lt (T.col_strict m.lt_succ_self h)

end SemistandardYoungTableau
