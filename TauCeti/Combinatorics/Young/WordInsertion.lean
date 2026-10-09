/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Schensted

/-!
# Schensted insertion of a word

`TauCeti.rowInsert` inserts one letter into a tableau. Iterating it over the letters of a word,
from left to right, is `TauCeti.insertWord`: the insertion tableau `P(w)` of the word `w`, the
first half of the Robinson--Schensted--Knuth correspondence. Each letter adds exactly one cell,
in the row returned by `TauCeti.rowInsertIndex`, and the list of those rows, in insertion order,
is `TauCeti.insertRecord`: the recording data `Q(w)`, kept here as the list of rows rather than
as a tableau.

The two together lose nothing. `TauCeti.reverseInsertWord` walks the recorded rows backwards,
undoing one insertion at a time by `TauCeti.reverseRowInsert`, and recovers both the tableau
inserted into and the whole word (`TauCeti.reverseInsertWord_insertWord`); in particular word
insertion from a fixed tableau is injective
(`TauCeti.insertWord_insertRecord_injective`). Insertion also conserves the letters
(`TauCeti.flatten_insertWord_perm`), so a word of distinct letters disjoint from the starting
tableau inserts to a tableau with distinct entries, the standardness ingredient of the
correspondence.

## Main definitions

* `TauCeti.insertWord`: Schensted insertion of a word into a tableau.
* `TauCeti.insertRecord`: the rows of the cells the letters of a word add, in insertion order.
* `TauCeti.reverseInsertWord`: reverse insertion along a list of recorded rows.

## Main results

* `TauCeti.insertWord_append`, `TauCeti.insertRecord_append`: both operations compose over a
  concatenation of words.
* `List.IsTableauRows.insertWord`: inserting a word into a tableau gives a tableau.
* `TauCeti.flatten_insertWord_perm`: insertion conserves the letters.
* `TauCeti.length_insertRecord`: one recorded row per letter.
* `TauCeti.reverseInsertWord_insertWord`: reverse insertion recovers the tableau and the word.
* `TauCeti.insertWord_insertRecord_injective`: a word is determined by its insertion tableau and
  its recorded rows.

## Implementation notes

The recording data is a list of row indices, not a tableau: the row indices are what insertion
produces and what reverse insertion consumes, and reading them as a standard tableau is a
separate step, available only for a word of distinct letters. Which pairs of a tableau and a list
of rows arise from a word is not characterized here, so the bijection with pairs of standard
tableaux of a common shape is not proved here either.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Section 1.1.
* B. E. Sagan, *The Symmetric Group*, 2nd ed., Springer GTM 203 (2001), Section 3.1.
-/

public section

namespace TauCeti

open List

variable {α : Type*} [LinearOrder α]

/-! ### Inserting a word -/

/-- **Schensted insertion of a word** into a tableau given by its rows: insert the letters of the
word one at a time, from left to right, by `TauCeti.rowInsert`. -/
def insertWord : List (List α) → List α → List (List α)
  | rows, [] => rows
  | rows, x :: w => insertWord (rowInsert x rows) w

/-- The rows in which the letters of a word add their cells under `TauCeti.insertWord`, listed
in insertion order. -/
def insertRecord : List (List α) → List α → List ℕ
  | _, [] => []
  | rows, x :: w => rowInsertIndex x rows :: insertRecord (rowInsert x rows) w

/-- Inserting the empty word changes nothing. -/
@[simp]
theorem insertWord_nil (rows : List (List α)) : insertWord rows [] = rows := (rfl)

/-- Inserting a word inserts its first letter, then the rest. -/
@[simp]
theorem insertWord_cons (rows : List (List α)) (x : α) (w : List α) :
    insertWord rows (x :: w) = insertWord (rowInsert x rows) w := (rfl)

/-- The empty word records no rows. -/
@[simp]
theorem insertRecord_nil (rows : List (List α)) : insertRecord rows ([] : List α) = [] := (rfl)

/-- The first letter of a word records its own row, then the rest record theirs. -/
@[simp]
theorem insertRecord_cons (rows : List (List α)) (x : α) (w : List α) :
    insertRecord rows (x :: w) =
      rowInsertIndex x rows :: insertRecord (rowInsert x rows) w := (rfl)

/-- **Word insertion composes**: inserting a concatenation is inserting the first word, then the
second into the result. -/
@[simp]
theorem insertWord_append (rows : List (List α)) (u v : List α) :
    insertWord rows (u ++ v) = insertWord (insertWord rows u) v := by
  induction u generalizing rows with
  | nil => simp
  | cons x u ih => simp [ih]

/-- **The recording data composes**: a concatenation records the rows of the first word, followed
by those the second word records when inserted into the tableau the first produced. -/
@[simp]
theorem insertRecord_append (rows : List (List α)) (u v : List α) :
    insertRecord rows (u ++ v) = insertRecord rows u ++ insertRecord (insertWord rows u) v := by
  induction u generalizing rows with
  | nil => simp
  | cons x u ih => simp [ih]

/-- Inserting a word and then one more letter is inserting the longer word. -/
theorem insertWord_concat (rows : List (List α)) (w : List α) (x : α) :
    insertWord rows (w ++ [x]) = rowInsert x (insertWord rows w) := by
  simp

/-- The rows recorded by a word followed by one more letter are those of the word, followed by
the row of the last letter's cell. -/
theorem insertRecord_concat (rows : List (List α)) (w : List α) (x : α) :
    insertRecord rows (w ++ [x]) =
      insertRecord rows w ++ [rowInsertIndex x (insertWord rows w)] := by
  simp

/-- One row is recorded per letter of the word. -/
@[simp]
theorem length_insertRecord (rows : List (List α)) (w : List α) :
    (insertRecord rows w).length = w.length := by
  induction w generalizing rows with
  | nil => simp
  | cons x w ih => simp [ih]

/-- **Word insertion preserves tableaux.** -/
theorem _root_.List.IsTableauRows.insertWord {rows : List (List α)} (h : rows.IsTableauRows)
    (w : List α) : (insertWord rows w).IsTableauRows := by
  induction w generalizing rows with
  | nil => simpa using h
  | cons x w ih => simpa using ih (h.rowInsert x)

/-- **Word insertion conserves the letters**: the cells of the resulting tableau carry the
letters of the word together with those of the tableau inserted into. -/
theorem flatten_insertWord_perm (rows : List (List α)) (w : List α) :
    (insertWord rows w).flatten.Perm (w ++ rows.flatten) := by
  induction w generalizing rows with
  | nil => simp
  | cons x w ih =>
    rw [insertWord_cons, cons_append]
    exact (ih (rowInsert x rows)).trans
      (((flatten_rowInsert_perm x rows).append_left w).trans perm_middle)

/-- **Each letter adds one cell**: the number of cells grows by the length of the word. -/
theorem length_flatten_insertWord (rows : List (List α)) (w : List α) :
    (insertWord rows w).flatten.length = w.length + rows.flatten.length := by
  simpa using (flatten_insertWord_perm rows w).length_eq

/-- **Word insertion preserves distinct entries**: inserting a word whose letters are distinct
and do not already occur gives a tableau whose entries are distinct. -/
theorem nodup_flatten_insertWord (rows : List (List α)) {w : List α}
    (h : (w ++ rows.flatten).Nodup) : (insertWord rows w).flatten.Nodup :=
  (flatten_insertWord_perm rows w).nodup_iff.mpr h

/-- Each letter adds at most one row. -/
theorem length_insertWord_le (rows : List (List α)) (w : List α) :
    (insertWord rows w).length ≤ rows.length + w.length := by
  induction w generalizing rows with
  | nil => simp
  | cons x w ih =>
    rw [insertWord_cons, length_cons]
    refine (ih (rowInsert x rows)).trans ?_
    have hle := rowInsertIndex_le_length x rows
    have hlen := length_rowInsert x rows
    omega

/-! ### Recovering the word -/

/-- **Reverse Schensted insertion of a word**: undo a run of insertions whose cells were added in
the rows `rs`, listed in *reverse* insertion order, by iterating `TauCeti.reverseRowInsert`. The
letters removed are returned in insertion order, so this inverts `TauCeti.insertWord` paired with
`TauCeti.insertRecord`. -/
def reverseInsertWord : List (List α) → List ℕ → List (List α) × List α
  | rows, [] => (rows, [])
  | rows, k :: rs =>
    ((reverseInsertWord (reverseRowInsert k rows).1 rs).1,
      (reverseInsertWord (reverseRowInsert k rows).1 rs).2 ++ (reverseRowInsert k rows).2.toList)

/-- Undoing no insertion changes nothing. -/
@[simp]
theorem reverseInsertWord_nil (rows : List (List α)) :
    reverseInsertWord rows ([] : List ℕ) = (rows, []) := (rfl)

/-- Undoing a run of insertions undoes the most recent one first; the letter it removes is the
last letter of the recovered word. -/
theorem reverseInsertWord_cons (rows : List (List α)) (k : ℕ) (rs : List ℕ) :
    reverseInsertWord rows (k :: rs) =
      ((reverseInsertWord (reverseRowInsert k rows).1 rs).1,
        (reverseInsertWord (reverseRowInsert k rows).1 rs).2 ++
          (reverseRowInsert k rows).2.toList) := (rfl)

/-- **Reverse insertion recovers the word.** Walking the recorded rows of a word backwards and
undoing one insertion at a time returns the tableau inserted into and the word itself. -/
theorem reverseInsertWord_insertWord {rows : List (List α)} (h : rows.IsTableauRows)
    (w : List α) :
    reverseInsertWord (insertWord rows w) (insertRecord rows w).reverse = (rows, w) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u x ih =>
    have hu := h.insertWord u
    rw [insertWord_concat, insertRecord_concat, reverse_append, reverse_singleton,
      singleton_append, reverseInsertWord_cons,
      reverseRowInsert_rowInsert x hu.nil_notMem hu.sortedLE]
    simp [ih]

/-- **A word is determined by its insertion tableau and its recorded rows**: the map taking a
word to the pair of its insertion tableau and its recording data is injective. The insertion
tableau on its own is not enough; the recorded rows are what reverse insertion follows. -/
theorem insertWord_insertRecord_injective {rows : List (List α)} (h : rows.IsTableauRows) :
    Function.Injective fun w : List α => (insertWord rows w, insertRecord rows w) := by
  intro w w' hw
  simp only [Prod.mk.injEq] at hw
  have hrec := reverseInsertWord_insertWord h w
  rw [hw.1, hw.2, reverseInsertWord_insertWord h w'] at hrec
  exact (congrArg Prod.snd hrec).symm

/-! ### A worked example -/

/-- Inserting `2, 1, 3` into the empty tableau: `2` starts the first row, `1` bumps it down into
a second row, and `3` is appended to the first row. So the insertion tableau has rows `[1, 3]`
and `[2]`, and the three cells are added in rows `0`, `1`, `0`. -/
example :
    insertWord ([] : List (List ℕ)) [2, 1, 3] = [[1, 3], [2]] ∧
      insertRecord ([] : List (List ℕ)) [2, 1, 3] = [0, 1, 0] := by
  have h₁ : rowInsert (1 : ℕ) [[2]] = [[1], [2]] := by
    rw [rowInsert_cons_of_eq_some (x := 1) (y := 2) (row := [2]) (rows := []) (by simp)]
    simp
  have h₂ : rowInsertIndex (1 : ℕ) [[2]] = 1 := by
    rw [rowInsertIndex_cons_of_eq_some (x := 1) (y := 2) (row := [2]) (rows := []) (by simp)]
    simp
  have h₃ : rowInsert (3 : ℕ) [[1], [2]] = [[1, 3], [2]] := by
    rw [rowInsert_cons_of_eq_none (x := 3) (row := [1]) (rows := [[2]]) (by simp)]
    simp
  have h₄ : rowInsertIndex (3 : ℕ) [[1], [2]] = 0 :=
    rowInsertIndex_cons_of_eq_none (x := 3) (row := [1]) (rows := [[2]]) (by simp)
  exact ⟨by simp [h₁, h₃], by simp [h₁, h₂, h₃, h₄]⟩

end TauCeti
