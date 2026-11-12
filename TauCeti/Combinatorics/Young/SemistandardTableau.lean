/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Young.SemistandardTableau
public import TauCeti.Combinatorics.Young.Diagram

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

/-- Column strictness, for a cell given by a bound on its column. -/
theorem col_strict_of_lt_rowLen (T : SemistandardYoungTableau μ) {r r' c : ℕ}
    (h : r' < r) (hc : c < μ.rowLen r) : T r' c < T r c :=
  T.col_strict h (YoungDiagram.mem_iff_lt_rowLen.mpr hc)

/-- The entries of a semistandard Young tableau increase strictly down a column, so the entry in
row `i` is at least `i`. -/
theorem le_entry (T : SemistandardYoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) : i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    exact Nat.succ_le_of_lt <|
      (ih (μ.up_left_mem m.le_succ le_rfl h)).trans_lt (T.col_strict m.lt_succ_self h)

open Finset in
/-- If some cell in a column at least `j` holds the letter `a`, there is a lowest row `k`
holding such a cell, and no row below `k` holds one. -/
theorem exists_lowestRow_of_exists {T : SemistandardYoungTableau μ} {j a : ℕ}
    (hex : ∃ k c, c < μ.rowLen k ∧ j ≤ c ∧ T k c = a) :
    ∃ k c, c < μ.rowLen k ∧ j ≤ c ∧ T k c = a ∧
      ∀ r, k < r → #{c ∈ range (μ.rowLen r) | j ≤ c ∧ T r c = a} = 0 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.findGreatest
      (fun k => ∃ c, c < μ.rowLen k ∧ j ≤ c ∧ T k c = a) (μ.colLen 0) := ⟨_, rfl⟩
  obtain ⟨k₀, c₀, hc₀, hjc₀, hT₀⟩ := hex
  have hk₀ : k₀ ≤ μ.colLen 0 :=
    (YoungDiagram.lt_colLen_zero_of_mem (YoungDiagram.mem_iff_lt_rowLen.mpr hc₀)).le
  have hspec := Nat.findGreatest_spec
    (P := fun k => ∃ c, c < μ.rowLen k ∧ j ≤ c ∧ T k c = a) hk₀ ⟨c₀, hc₀, hjc₀, hT₀⟩
  rw [← hk] at hspec
  obtain ⟨c, hc, hjc, hTc⟩ := hspec
  refine ⟨k, c, hc, hjc, hTc, fun r hr => ?_⟩
  refine card_eq_zero.mpr (filter_eq_empty_iff.mpr fun c' hc' ⟨hjc', hTc'⟩ => ?_)
  have hc' := mem_range.mp hc'
  exact Nat.findGreatest_is_greatest
    (P := fun k => ∃ c, c < μ.rowLen k ∧ j ≤ c ∧ T k c = a) (hk ▸ hr)
    (YoungDiagram.lt_colLen_zero_of_mem (YoungDiagram.mem_iff_lt_rowLen.mpr hc')).le
    ⟨c', hc', hjc', hTc'⟩

end SemistandardYoungTableau
