/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Kostka
import TauCeti.Combinatorics.Young.Diagram
import TauCeti.Combinatorics.Young.SemistandardTableau

/-!
# Deleting full columns of a semistandard tableau

Let `μ` and `ν` be Young diagrams with at most `N` rows such that `ν.rowLen i = μ.rowLen i + d`
for every `i < N`: `ν` is `μ` with `d` columns of the full height `N` prepended. In a semistandard
tableau of shape `ν` with entries smaller than `N`, these columns are forced to hold
`0, 1, …, N - 1` from top to bottom, since the entries increase strictly down a column. Deleting
them is therefore a bijection `TauCeti.BoundedSSYT.fullColumnsEquiv` onto the semistandard
tableaux of shape `μ` with entries smaller than `N`; its inverse writes `0, 1, …, N - 1` into the
`d` new columns.

## Main results

* `YoungDiagram.colLen_eq_of_rowLen_eq_add` and `YoungDiagram.colLen_add_of_rowLen_eq_add`: the
  columns of `ν` are `d` columns of height `N` followed by the columns of `μ`.
* `TauCeti.BoundedSSYT.val_eq_of_mem_of_lt`: the entries of a full column are forced.
* `TauCeti.BoundedSSYT.fullColumnsEquiv`: deleting the `d` full columns.
-/

public section

namespace YoungDiagram

variable {N d : ℕ} {μ ν : YoungDiagram}

/-- Shifting a cell of `μ` by the `d` prepended columns gives a cell of `ν`, and conversely. -/
private theorem add_mem_iff_of_rowLen_eq_add (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N)
    (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) {i j : ℕ} : (i, j + d) ∈ ν ↔ (i, j) ∈ μ := by
  rcases lt_or_ge i N with hi | hi
  · rw [mem_iff_lt_rowLen, mem_iff_lt_rowLen, h i hi]
    omega
  · exact iff_of_false (fun hc => absurd ((lt_colLen_zero_of_mem hc).trans_le hν) (not_lt.mpr hi))
      fun hc => absurd ((lt_colLen_zero_of_mem hc).trans_le hμ) (not_lt.mpr hi)

/-- The first `d` columns of `ν` have the full height `N`. -/
private theorem mem_of_rowLen_eq_add (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) {i j : ℕ}
    (hi : i < N) (hj : j < d) : (i, j) ∈ ν := by
  rw [mem_iff_lt_rowLen, h i hi]
  omega

/-- If `ν` is `μ` with `d` columns of the full height `N` prepended, these columns have height
`N`. -/
theorem colLen_eq_of_rowLen_eq_add (hν : ν.colLen 0 ≤ N)
    (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) {j : ℕ} (hj : j < d) : ν.colLen j = N :=
  eq_of_forall_lt_iff fun i => by
    rw [← mem_iff_lt_colLen]
    exact ⟨fun hc => (lt_colLen_zero_of_mem hc).trans_le hν, fun hi => mem_of_rowLen_eq_add h hi hj⟩

/-- If `ν` is `μ` with `d` columns of the full height `N` prepended (both with at most `N` rows),
the column `j + d` of `ν` is the column `j` of `μ`. -/
theorem colLen_add_of_rowLen_eq_add (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N)
    (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) (j : ℕ) : ν.colLen (j + d) = μ.colLen j :=
  eq_of_forall_lt_iff fun i => by
    rw [← mem_iff_lt_colLen, ← mem_iff_lt_colLen]
    exact add_mem_iff_of_rowLen_eq_add hμ hν h

end YoungDiagram

namespace TauCeti

namespace BoundedSSYT

open YoungDiagram

variable {N d : ℕ} {μ ν : YoungDiagram}

/-- **The entries of a full column are forced.** In a semistandard tableau with entries smaller
than `N` whose column `j` has the full height `N`, the entry in the row `i < N` of that column is
`i`. -/
theorem val_eq_of_mem_of_lt (T : BoundedSSYT N ν) {i j : ℕ} (hc : (N - 1, j) ∈ ν) (hi : i < N) :
    T.val i j = i := by
  have h₁ := T.val.le_entry (ν.up_left_mem (by omega : i ≤ N - 1) le_rfl hc)
  have h₂ := T.val.entry_add_sub_le_entry (by omega : i ≤ N - 1) hc
  have h₃ := T.entry_lt hc
  omega

/-- The tableau of shape `μ` obtained by deleting the first `d` columns. -/
private def dropTableau (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N)
    (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) (T : BoundedSSYT N ν) :
    SemistandardYoungTableau μ where
  entry i j := T.val i (j + d)
  row_weak' hj hc := T.val.row_weak (by omega) ((add_mem_iff_of_rowLen_eq_add hμ hν h).mpr hc)
  col_strict' hi hc := T.val.col_strict hi ((add_mem_iff_of_rowLen_eq_add hμ hν h).mpr hc)
  zeros' hc := T.val.zeros (mt (add_mem_iff_of_rowLen_eq_add hμ hν h).mp hc)

private theorem dropTableau_apply (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N)
    (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) (T : BoundedSSYT N ν) (i j : ℕ) :
    dropTableau hμ hν h T i j = T.val i (j + d) :=
  (rfl)

/-- The cell `(i, j)` of `ν` outside the first `d` columns comes from the cell `(i, j - d)` of
`μ`. -/
private theorem sub_mem_iff (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N)
    (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) {i j : ℕ} (hj : ¬j < d) :
    (i, j - d) ∈ μ ↔ (i, j) ∈ ν := by
  rw [← add_mem_iff_of_rowLen_eq_add hμ hν h, Nat.sub_add_cancel (not_lt.mp hj)]

/-- The tableau of shape `ν` obtained by writing `0, 1, …, N - 1` into `d` new first columns. -/
private def addTableau (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N)
    (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) (U : BoundedSSYT N μ) :
    SemistandardYoungTableau ν where
  entry i j := if j < d then (if i < N then i else 0) else U.val i (j - d)
  row_weak' {i j₁ j₂} hj hc := by
    have hi := (lt_colLen_zero_of_mem hc).trans_le hν
    by_cases hj₂ : j₂ < d
    · simp [show j₁ < d by omega, hj₂]
    have hc' := (sub_mem_iff hμ hν h hj₂).mpr hc
    by_cases hj₁ : j₁ < d
    · simpa [hj₁, hj₂, hi] using U.val.le_entry hc'
    · simpa [hj₁, hj₂] using U.val.row_weak_of_le (by omega) hc'
  col_strict' {i₁ i₂ j} hi hc := by
    have hi₂ := (lt_colLen_zero_of_mem hc).trans_le hν
    by_cases hj : j < d
    · simp [hj, hi₂, hi.trans hi₂, hi]
    simpa [hj] using U.val.col_strict hi ((sub_mem_iff hμ hν h hj).mpr hc)
  zeros' {i j} hc := by
    by_cases hj : j < d
    · simp only [hj, ite_true]
      exact ite_eq_right fun hi => hc (mem_of_rowLen_eq_add h hi hj)
    simp [hj, U.val.zeros (mt (sub_mem_iff hμ hν h hj).mp hc)]

private theorem addTableau_apply (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N)
    (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) (U : BoundedSSYT N μ) (i j : ℕ) :
    addTableau hμ hν h U i j = if j < d then (if i < N then i else 0) else U.val i (j - d) :=
  (rfl)

/-- **Deleting full columns.** If `ν` is `μ` with `d` columns of the full height `N` prepended
(both with at most `N` rows), deleting these columns is a bijection from the semistandard tableaux
of shape `ν` with entries smaller than `N` to those of shape `μ`. The inverse writes
`0, 1, …, N - 1` into each of the `d` full columns. -/
def fullColumnsEquiv (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N)
    (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) : BoundedSSYT N ν ≃ BoundedSSYT N μ where
  toFun T := ⟨dropTableau hμ hν h T, fun i j hc => by
    rw [dropTableau_apply]
    exact T.entry_lt ((add_mem_iff_of_rowLen_eq_add hμ hν h).mpr hc)⟩
  invFun U := ⟨addTableau hμ hν h U, fun i j hc => by
    rw [addTableau_apply]
    by_cases hj : j < d
    · simp [hj, (lt_colLen_zero_of_mem hc).trans_le hν]
    simpa [hj] using U.entry_lt ((sub_mem_iff hμ hν h hj).mpr hc)⟩
  left_inv T := by
    refine Subtype.ext (SemistandardYoungTableau.ext fun i j => ?_)
    rw [addTableau_apply]
    by_cases hj : j < d
    · by_cases hi : i < N
      · rw [ite_eq_left hj, ite_eq_left hi,
          val_eq_of_mem_of_lt T (mem_of_rowLen_eq_add h (by omega) hj) hi]
      · rw [ite_eq_left hj, ite_eq_right hi,
          T.val.zeros fun hc => hi ((lt_colLen_zero_of_mem hc).trans_le hν)]
    · rw [ite_eq_right hj, dropTableau_apply, Nat.sub_add_cancel (not_lt.mp hj)]
  right_inv U := by
    refine Subtype.ext (SemistandardYoungTableau.ext fun i j => ?_)
    rw [dropTableau_apply, addTableau_apply, ite_eq_right (by omega), Nat.add_sub_cancel]

/-- Deleting the full columns reads the tableau from the column `d` on. -/
@[simp]
theorem fullColumnsEquiv_apply_val (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N)
    (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) (T : BoundedSSYT N ν) (i j : ℕ) :
    (fullColumnsEquiv hμ hν h T).val i j = T.val i (j + d) :=
  (rfl)

/-- Prepending the full columns writes `0, 1, …, N - 1` into each of them. -/
@[simp]
theorem fullColumnsEquiv_symm_apply_val (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N)
    (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) (U : BoundedSSYT N μ) (i j : ℕ) :
    ((fullColumnsEquiv hμ hν h).symm U).val i j =
      if j < d then (if i < N then i else 0) else U.val i (j - d) :=
  (rfl)

end BoundedSSYT

end TauCeti
