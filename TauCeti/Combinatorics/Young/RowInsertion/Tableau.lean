/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Chain
public import TauCeti.Combinatorics.Young.RowInsertion.Basic

/-!
# Row insertion into a semistandard tableau

`TauCeti.rowBump` performs the local step of row insertion: it replaces the first entry of a row
strictly greater than the inserted letter and hands that entry on. This file iterates the step
down a whole tableau, which is what the Robinson--Schensted--Knuth correspondence runs on.

A tableau is carried here by its list of rows, and its shape is read off as the list of row
lengths. A list of rows is the only workable carrier for insertion: the operation changes the
shape, so no single `SemistandardYoungTableau μ` can hold both its input and its output.
Semistandardness is therefore a predicate on the list of rows, `TauCeti.IsSemistandardRows`:
every row increases weakly, and consecutive rows are related by `TauCeti.IsColumnStrict`, which
asks that the lower row be no longer than the upper one and strictly larger entry by entry. That
second condition already forces the row lengths to decrease weakly, so the shape of a
semistandard list of rows is a Young diagram
(`TauCeti.IsSemistandardRows.sortedGE_map_length`).

The main theorem is that insertion preserves semistandardness
(`TauCeti.IsSemistandardRows.tableauInsert`). Its proof runs on two facts about a single
bumping step, both proved by induction along the two rows and neither needing the rows sorted.
The first, `TauCeti.IsColumnStrict.rowBump_left`, is that bumping the upper row keeps the lower
one strictly below it: the step only ever lowers an entry or appends past the end. The second,
`TauCeti.IsColumnStrict.rowBump`, is the two-row heart of the matter: if the step in the upper
row hands on the letter `y`, then inserting `y` into the lower row keeps that row strictly below
the new upper row. Both inequalities needed there come from `x < y`, the letter handed on being
strictly larger than the letter inserted.

Insertion adds exactly one cell: the letters of the result are those of the tableau together with
the inserted letter (`TauCeti.flatten_tableauInsert_perm`), the number of cells grows by one, and
the number of rows grows by at most one.

## Main definitions

* `TauCeti.IsColumnStrict`: the lower of two rows is no longer than the upper one and is strictly
  larger in every column they share.
* `TauCeti.IsSemistandardRows`: rows increase weakly and successive rows are column strict.
* `TauCeti.tableauInsert`: insert a letter into a tableau presented as its list of rows, bumping
  down the rows until a letter comes to rest.

## Main results

* `TauCeti.IsColumnStrict.rowBump_left` and `TauCeti.IsColumnStrict.rowBump`: the two one-step
  facts about column strictness along a bump.
* `TauCeti.IsSemistandardRows.tableauInsert`: **row insertion preserves semistandardness.**
* `TauCeti.flatten_tableauInsert_perm` and `TauCeti.length_flatten_tableauInsert`: insertion
  conserves the letters and adds exactly one cell.
* `TauCeti.nodup_flatten_tableauInsert`: inserting a fresh letter into a tableau with distinct
  entries leaves the entries distinct, so standard tableaux stay standard.
* `TauCeti.le_length_tableauInsert` and `TauCeti.length_tableauInsert_le`: the number of rows
  grows by at most one.
* `TauCeti.IsSemistandardRows.sortedGE_map_length`: the shape of a semistandard list of rows is
  weakly decreasing.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), §1.1, for row insertion into a
  tableau and the bumping route.
* B. E. Sagan, *The Symmetric Group*, 2nd ed., Springer (2001), §3.1.
-/

public section

namespace TauCeti

variable {α : Type*} [LinearOrder α]

/-! ### Column strictness between two rows -/

/-- `IsColumnStrict r s` says that the row `s` sits strictly below the row `r` in a tableau: it is
no longer than `r`, and in each column they share its entry is strictly larger. -/
def IsColumnStrict (r s : List α) : Prop :=
  List.Forall₂ (· < ·) (r.take s.length) s

/-- Column strictness unfolded: the lower row is matched entry by entry against the prefix of the
upper row of its own length. -/
theorem isColumnStrict_iff {r s : List α} :
    IsColumnStrict r s ↔ List.Forall₂ (· < ·) (r.take s.length) s :=
  Iff.rfl

/-- Nothing sits below an empty row except an empty row. -/
@[simp]
theorem isColumnStrict_nil_left_iff {s : List α} :
    IsColumnStrict ([] : List α) s ↔ s = [] := by
  simp [isColumnStrict_iff]

/-- An empty row sits below every row. -/
@[simp]
theorem isColumnStrict_nil_right (r : List α) : IsColumnStrict r ([] : List α) := by
  simp [isColumnStrict_iff]

/-- Column strictness, one column at a time. -/
@[simp]
theorem isColumnStrict_cons_cons {a b : α} {r s : List α} :
    IsColumnStrict (a :: r) (b :: s) ↔ a < b ∧ IsColumnStrict r s := by
  simp [isColumnStrict_iff]

/-- A row below another is no longer than it. -/
theorem IsColumnStrict.length_le {r s : List α} (h : IsColumnStrict r s) :
    s.length ≤ r.length := by
  have h' := (isColumnStrict_iff.mp h).length_eq
  rw [List.length_take] at h'
  omega

/-! ### Semistandard lists of rows -/

/-- A list of rows is semistandard when each row increases weakly and each row sits strictly
below the one before it. -/
structure IsSemistandardRows (rows : List (List α)) : Prop where
  /-- Entries increase weakly along each row. -/
  sortedLE : ∀ r ∈ rows, r.SortedLE
  /-- Successive rows are column strict. -/
  isChain : List.IsChain IsColumnStrict rows

@[simp]
theorem isSemistandardRows_nil : IsSemistandardRows ([] : List (List α)) :=
  ⟨by simp, List.isChain_nil⟩

theorem isSemistandardRows_singleton {r : List α} (hr : r.SortedLE) :
    IsSemistandardRows [r] :=
  ⟨by simpa using hr, List.isChain_singleton r⟩

/-- Dropping the first row of a semistandard list of rows leaves a semistandard list of rows. -/
theorem IsSemistandardRows.of_cons {r : List α} {rows : List (List α)}
    (h : IsSemistandardRows (r :: rows)) : IsSemistandardRows rows := by
  refine ⟨fun t ht => h.sortedLE t (by simp [ht]), ?_⟩
  cases rows with
  | nil => exact List.isChain_nil
  | cons s rows => exact (List.isChain_cons_cons.mp h.isChain).2

/-- The shape of a semistandard list of rows is weakly decreasing, so it is a Young diagram. -/
theorem IsSemistandardRows.sortedGE_map_length {rows : List (List α)}
    (h : IsSemistandardRows rows) : (rows.map List.length).SortedGE := by
  rw [List.sortedGE_iff_isChain]
  exact List.isChain_map_of_isChain List.length (fun _ _ hrs => hrs.length_le) h.isChain

/-- In a semistandard list of rows with no repeated entry, every row increases strictly. -/
theorem IsSemistandardRows.sortedLT_of_nodup_flatten {rows : List (List α)}
    (h : IsSemistandardRows rows) (hnd : rows.flatten.Nodup) {r : List α} (hr : r ∈ rows) :
    r.SortedLT :=
  (h.sortedLE r hr).sortedLT_of_nodup ((List.nodup_flatten.mp hnd).1 r hr)

/-! ### Column strictness along a bump -/

/-- Bumping the upper row keeps the row below it strictly below: the step either lowers an entry
of the upper row or appends past the end of the lower one. -/
theorem IsColumnStrict.rowBump_left {r s : List α} (h : IsColumnStrict r s) (x : α) :
    IsColumnStrict (rowBump x r).1 s := by
  induction r generalizing s with
  | nil =>
    rw [isColumnStrict_nil_left_iff] at h
    subst h
    simp
  | cons a r ih =>
    cases s with
    | nil => simp
    | cons b s =>
      rw [isColumnStrict_cons_cons] at h
      by_cases hxa : x < a
      · rw [rowBump_cons_of_lt r hxa, isColumnStrict_cons_cons]
        exact ⟨hxa.trans h.1, h.2⟩
      · rw [rowBump_cons_of_le r (not_lt.mp hxa), isColumnStrict_cons_cons]
        exact ⟨h.1, ih h.2⟩

/-- The two-row step of row insertion. If bumping the letter `x` into the upper row hands on the
letter `y`, then bumping `y` into the row below keeps that row strictly below the new upper row.

Both inequalities the proof needs come from `x < y`: the letter handed on is strictly larger than
the letter inserted, so it is strictly larger than every entry the insertion walked past. -/
theorem IsColumnStrict.rowBump {x y : α} {r s : List α} (h : IsColumnStrict r s)
    (hy : (rowBump x r).2 = some y) :
    IsColumnStrict (rowBump x r).1 (rowBump y s).1 := by
  induction r generalizing s with
  | nil => simp at hy
  | cons a r ih =>
    by_cases hxa : x < a
    · rw [rowBump_cons_of_lt r hxa] at hy ⊢
      obtain rfl : a = y := Option.some.inj hy
      cases s with
      | nil => simpa using hxa
      | cons b s =>
        rw [isColumnStrict_cons_cons] at h
        rw [rowBump_cons_of_lt s h.1, isColumnStrict_cons_cons]
        exact ⟨hxa, h.2⟩
    · rw [rowBump_cons_of_le r (not_lt.mp hxa)] at hy ⊢
      have hay : a < y := lt_of_le_of_lt (not_lt.mp hxa) (lt_of_rowBump_snd_eq_some hy)
      cases s with
      | nil => simpa using hay
      | cons b s =>
        rw [isColumnStrict_cons_cons] at h
        by_cases hyb : y < b
        · rw [rowBump_cons_of_lt s hyb, isColumnStrict_cons_cons]
          exact ⟨hay, h.2.rowBump_left x⟩
        · rw [rowBump_cons_of_le s (not_lt.mp hyb), isColumnStrict_cons_cons]
          exact ⟨h.1, ih h.2 hy⟩

/-! ### Insertion into a tableau -/

/-- Insert a letter into a tableau presented as its list of rows: bump it into the first row, and
carry the letter the bump hands on into the rows below, until one comes to rest at the end of a
row or a new row is started. -/
def tableauInsert (x : α) : List (List α) → List (List α)
  | [] => [[x]]
  | r :: rows => (rowBump x r).1 :: (rowBump x r).2.elim rows fun y => tableauInsert y rows

@[simp]
theorem tableauInsert_nil (x : α) : tableauInsert x ([] : List (List α)) = [[x]] := (rfl)

theorem tableauInsert_cons (x : α) (r : List α) (rows : List (List α)) :
    tableauInsert x (r :: rows) =
      (rowBump x r).1 :: (rowBump x r).2.elim rows fun y => tableauInsert y rows := (rfl)

/-- A letter that comes to rest in the first row leaves the rows below untouched. -/
theorem tableauInsert_cons_of_eq_none {x : α} {r : List α} (rows : List (List α))
    (h : (rowBump x r).2 = none) :
    tableauInsert x (r :: rows) = (rowBump x r).1 :: rows := by
  rw [tableauInsert_cons, h]
  rfl

/-- A letter bumped out of the first row is inserted into the rows below. -/
theorem tableauInsert_cons_of_eq_some {x y : α} {r : List α} (rows : List (List α))
    (h : (rowBump x r).2 = some y) :
    tableauInsert x (r :: rows) = (rowBump x r).1 :: tableauInsert y rows := by
  rw [tableauInsert_cons, h]
  rfl

@[simp]
theorem tableauInsert_ne_nil (x : α) (rows : List (List α)) : tableauInsert x rows ≠ [] := by
  cases rows with
  | nil => simp
  | cons r rows => rw [tableauInsert_cons]; simp

/-- **Row insertion preserves semistandardness.** -/
theorem IsSemistandardRows.tableauInsert {rows : List (List α)} (h : IsSemistandardRows rows)
    (x : α) : IsSemistandardRows (tableauInsert x rows) := by
  induction rows generalizing x with
  | nil =>
    have hx : [x].SortedLE := List.sortedLE_iff_pairwise.mpr (by simp)
    simpa using isSemistandardRows_singleton hx
  | cons r rows ih =>
    have hhead : (rowBump x r).1.SortedLE := sortedLE_rowBump x (h.sortedLE r (by simp))
    cases hy : (rowBump x r).2 with
    | none =>
      rw [tableauInsert_cons_of_eq_none rows hy]
      refine ⟨fun t ht => ?_, ?_⟩
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact hhead
        · exact h.sortedLE t (by simp [ht])
      · cases rows with
        | nil => exact List.isChain_singleton _
        | cons s rows =>
          exact List.isChain_cons_cons.mpr
            ⟨(List.isChain_cons_cons.mp h.isChain).1.rowBump_left x,
              h.of_cons.isChain⟩
    | some y =>
      have htail := ih h.of_cons y
      rw [tableauInsert_cons_of_eq_some rows hy]
      refine ⟨fun t ht => ?_, ?_⟩
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact hhead
        · exact htail.sortedLE t ht
      · cases rows with
        | nil =>
          refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩
          simpa using (isColumnStrict_nil_right r).rowBump hy
        | cons s rows =>
          rw [tableauInsert_cons] at htail ⊢
          exact List.isChain_cons_cons.mpr
            ⟨(List.isChain_cons_cons.mp h.isChain).1.rowBump hy, htail.isChain⟩

/-! ### Letters, cells and rows -/

/-- Row insertion conserves the letters: the entries of the new tableau are those of the old one
together with the inserted letter. -/
theorem flatten_tableauInsert_perm (x : α) (rows : List (List α)) :
    (tableauInsert x rows).flatten.Perm (x :: rows.flatten) := by
  induction rows generalizing x with
  | nil => simp
  | cons r rows ih =>
    cases hy : (rowBump x r).2 with
    | none =>
      rw [tableauInsert_cons_of_eq_none rows hy, List.flatten_cons, List.flatten_cons]
      have hperm : (rowBump x r).1.Perm (x :: r) := by
        simpa [hy] using rowBump_perm x r
      exact hperm.append_right rows.flatten
    | some y =>
      rw [tableauInsert_cons_of_eq_some rows hy, List.flatten_cons, List.flatten_cons]
      have hperm : ((rowBump x r).1 ++ [y]).Perm (x :: r) := by
        simpa [hy] using rowBump_perm x r
      refine ((ih y).append_left (rowBump x r).1).trans ?_
      have hsplit : (rowBump x r).1 ++ y :: rows.flatten
          = ((rowBump x r).1 ++ [y]) ++ rows.flatten := by simp
      rw [hsplit]
      exact hperm.append_right rows.flatten

/-- Row insertion adds exactly one cell. -/
theorem length_flatten_tableauInsert (x : α) (rows : List (List α)) :
    (tableauInsert x rows).flatten.length = rows.flatten.length + 1 := by
  simpa using (flatten_tableauInsert_perm x rows).length_eq

/-- The entries of the new tableau are the inserted letter together with the old entries. -/
theorem mem_flatten_tableauInsert_iff {a x : α} {rows : List (List α)} :
    a ∈ (tableauInsert x rows).flatten ↔ a = x ∨ a ∈ rows.flatten := by
  simpa using (flatten_tableauInsert_perm x rows).mem_iff (a := a)

/-- Inserting a letter that does not already occur into a tableau whose entries are distinct
leaves the entries distinct. This is what keeps a standard tableau standard along the bumping
route. -/
theorem nodup_flatten_tableauInsert {x : α} {rows : List (List α)}
    (hnd : rows.flatten.Nodup) (hx : x ∉ rows.flatten) :
    (tableauInsert x rows).flatten.Nodup :=
  ((flatten_tableauInsert_perm x rows).nodup_iff).mpr (List.nodup_cons.mpr ⟨hx, hnd⟩)

/-- Row insertion never removes a row. -/
theorem le_length_tableauInsert (x : α) (rows : List (List α)) :
    rows.length ≤ (tableauInsert x rows).length := by
  induction rows generalizing x with
  | nil => simp
  | cons r rows ih =>
    cases hy : (rowBump x r).2 with
    | none => rw [tableauInsert_cons_of_eq_none rows hy]; simp
    | some y =>
      rw [tableauInsert_cons_of_eq_some rows hy, List.length_cons, List.length_cons]
      exact Nat.succ_le_succ (ih y)

/-- Row insertion adds at most one row. -/
theorem length_tableauInsert_le (x : α) (rows : List (List α)) :
    (tableauInsert x rows).length ≤ rows.length + 1 := by
  induction rows generalizing x with
  | nil => simp
  | cons r rows ih =>
    cases hy : (rowBump x r).2 with
    | none => rw [tableauInsert_cons_of_eq_none rows hy]; simp
    | some y =>
      rw [tableauInsert_cons_of_eq_some rows hy, List.length_cons, List.length_cons]
      exact Nat.succ_le_succ (ih y)

/-- Inserting `2` into the tableau with rows `1 2 4` and `3 5` bumps `4` out of the first row,
which in turn bumps `5` out of the second row, and `5` starts a third row. -/
example : tableauInsert 2 [[1, 2, 4], [3, 5]] = [[1, 2, 2], [3, 4], [5]] := by
  simp [tableauInsert_cons]

end TauCeti
