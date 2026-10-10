/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Schensted.Basic

/-!
# The row-insertion bumping lemma

If `x ≤ y`, inserting `x` and then `y` into a semistandard tableau places the second new
cell weakly above and strictly to the right of the first. If `y < x`, the second cell is
strictly below and weakly to the left. Thus the order of two incoming letters is detected
by either the rows or the columns of their new cells.

The column of the cell added by inserting `x` into `rows` is the original length of row
`rowInsertIndex x rows`. These comparisons ensure that a weakly increasing block of letters
adds cells in distinct columns. This is the horizontal-strip property needed for the
semistandard recording tableau in the matrix Robinson--Schensted--Knuth correspondence.

The row comparisons require less: weakly increasing rows suffice for the weak comparison,
and the strict comparison holds even without any tableau hypothesis.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Section 4.1.
* B. E. Sagan, *The Symmetric Group*, second edition, Springer GTM 203 (2001), Section 3.2.
-/

public section

namespace TauCeti

open List

variable {α : Type*} [LinearOrder α]

/-- Inserting weakly increasing letters successively ends weakly higher the second time.
Only weak increase within each row is needed. -/
theorem rowInsertIndex_le_of_le {rows : List (List α)}
    (hrows : ∀ row ∈ rows, row.SortedLE) {x y : α} (hxy : x ≤ y) :
    rowInsertIndex y (rowInsert x rows) ≤ rowInsertIndex x rows := by
  induction rows generalizing x y with
  | nil =>
    simp [rowInsertIndex_cons_of_eq_none []
      ((rowBump_snd_eq_none_iff y [x]).mpr (by simpa using hxy))]
  | cons row rows ih =>
    cases hx : (rowBump x row).2 with
    | none =>
      have hle := (rowBump_snd_eq_none_iff x row).mp hx
      have hy : (rowBump y (rowBump x row).1).2 = none := by
        rw [rowBump_of_forall_le x row hle]
        apply (rowBump_snd_eq_none_iff _ _).mpr
        intro z hz
        rcases mem_append.mp hz with hz | hz
        · exact (hle z hz).trans hxy
        · exact (mem_singleton.mp hz) ▸ hxy
      simp [rowInsert_cons_of_eq_none rows hx,
        rowInsertIndex_cons_of_eq_none rows hx,
        rowInsertIndex_cons_of_eq_none rows hy]
    | some a =>
      rw [rowInsert_cons_of_eq_some rows hx, rowInsertIndex_cons_of_eq_some rows hx]
      cases hy : (rowBump y (rowBump x row).1).2 with
      | none => simp [rowInsertIndex_cons_of_eq_none _ hy]
      | some b =>
        rw [rowInsertIndex_cons_of_eq_some _ hy]
        exact Nat.add_le_add_right (ih (fun r hr => hrows r (mem_cons_of_mem _ hr))
          (rowBump_bumped_le_of_le (hrows row mem_cons_self) hxy hx hy)) 1

/-- Inserting a strictly smaller letter successively ends strictly lower the second time.
This holds for arbitrary lists of rows. -/
theorem rowInsertIndex_lt_of_lt {rows : List (List α)} {x y : α} (hyx : y < x) :
    rowInsertIndex x rows < rowInsertIndex y (rowInsert x rows) := by
  induction rows generalizing x y with
  | nil =>
    rw [rowInsert_nil, rowInsertIndex_nil,
      rowInsertIndex_cons_of_eq_some (y := x) [] (by simp [rowBump_cons_of_lt [] hyx])]
    simp
  | cons row rows ih =>
    obtain ⟨b, hy, hbx⟩ := exists_rowBump_snd_eq_some_le_of_lt hyx row
    cases hx : (rowBump x row).2 with
    | none =>
      simp [rowInsert_cons_of_eq_none rows hx,
        rowInsertIndex_cons_of_eq_none rows hx,
        rowInsertIndex_cons_of_eq_some rows hy]
    | some a =>
      rw [rowInsert_cons_of_eq_some rows hx, rowInsertIndex_cons_of_eq_some rows hx,
        rowInsertIndex_cons_of_eq_some _ hy]
      exact Nat.add_lt_add_right (ih (hbx.trans_lt (lt_of_rowBump_snd_eq_some hx))) 1

/-- For weakly increasing rows, the second insertion ends weakly higher exactly when the
second incoming letter is at least the first. Supply `hrows` explicitly when using this
characterization with `simp`: its discharger does not solve the universally quantified
row-sortedness premise. -/
theorem rowInsertIndex_le_iff {rows : List (List α)}
    (hrows : ∀ row ∈ rows, row.SortedLE) (x y : α) :
    rowInsertIndex y (rowInsert x rows) ≤ rowInsertIndex x rows ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hxy
    exact (not_lt_of_ge h) (rowInsertIndex_lt_of_lt (not_le.mp hxy))
  · exact rowInsertIndex_le_of_le hrows

/-- The second cell lies strictly to the right when the incoming letters weakly increase.
The column indices are the row lengths before the respective insertions. -/
theorem rowInsert_column_lt_of_le {rows : List (List α)} (hrows : rows.IsTableauRows)
    {x y : α} (hxy : x ≤ y) :
    (rows.getD (rowInsertIndex x rows) []).length <
      ((rowInsert x rows).getD (rowInsertIndex y (rowInsert x rows)) []).length := by
  have hrow := rowInsertIndex_le_of_le hrows.sortedLE hxy
  have hanti : Antitone fun i => ((rowInsert x rows).getD i []).length :=
    antitone_nat_of_succ_le (hrows.rowInsert x).length_getD_succ_le
  have hlen := hanti hrow
  dsimp only at hlen
  rw [length_getD_rowInsert, ite_eq_left rfl] at hlen
  omega

/-- The second cell lies weakly to the left when the second incoming letter is smaller.
The column indices are the row lengths before the respective insertions. -/
theorem rowInsert_column_le_of_lt {rows : List (List α)} (hrows : rows.IsTableauRows)
    {x y : α} (hyx : y < x) :
    ((rowInsert x rows).getD (rowInsertIndex y (rowInsert x rows)) []).length ≤
      (rows.getD (rowInsertIndex x rows) []).length := by
  have hrow := rowInsertIndex_lt_of_lt (rows := rows) hyx
  rw [length_getD_rowInsert, ite_eq_right (Ne.symm (Nat.ne_of_lt hrow)), Nat.add_zero]
  have hanti : Antitone fun i => (rows.getD i []).length :=
    antitone_nat_of_succ_le hrows.length_getD_succ_le
  exact hanti hrow.le

/-- The second new cell lies strictly to the right exactly when the second incoming letter
is at least the first. This includes equal letters, which produce distinct columns. -/
@[simp]
theorem rowInsert_column_lt_iff {rows : List (List α)} (hrows : rows.IsTableauRows)
    (x y : α) :
    (rows[rowInsertIndex x rows]?.getD []).length <
      ((rowInsert x rows)[rowInsertIndex y (rowInsert x rows)]?.getD []).length ↔ x ≤ y := by
  simp only [← getD_eq_getElem?_getD]
  constructor
  · intro h
    by_contra hxy
    exact (not_lt_of_ge (rowInsert_column_le_of_lt hrows (not_le.mp hxy))) h
  · exact rowInsert_column_lt_of_le hrows

end TauCeti
