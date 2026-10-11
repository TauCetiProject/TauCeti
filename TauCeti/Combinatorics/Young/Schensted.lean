/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.RowInsertion
public import Mathlib.Data.List.Chain

/-!
# Schensted row insertion into a tableau

A semistandard tableau is recorded here by its list of rows, from top to bottom: every row is
nonempty and weakly increasing, and each row sits on top of the next one, being at least as long
and strictly smaller in every column (`List.IsTableauRows`).

Row insertion `TauCeti.rowInsert x T` inserts the letter `x` into the first row by
`TauCeti.rowBump`; the letter bumped out of that row is inserted into the second row, and so on,
until a letter is appended at the end of a row (possibly a new row at the bottom). This is
Schensted's insertion `T ← x`, the step iterated by the Robinson--Schensted--Knuth
correspondence. Its basic properties are:

* the result is again a tableau (`List.IsTableauRows.rowInsert`);
* it has the letters of `T` together with `x` (`TauCeti.flatten_rowInsert_perm`);
* its shape is that of `T` with one cell added, at the end of the row
  `TauCeti.rowInsertIndex x T` (`TauCeti.length_getD_rowInsert`), and that cell is a corner
  (`TauCeti.length_getD_succ_rowInsertIndex_lt`).

Reverse insertion `TauCeti.reverseRowInsert k T` removes the last entry of row `k` and moves it
up by `TauCeti.reverseRowBump`, row by row, ejecting a letter from the first row. It undoes
insertion (`TauCeti.reverseRowInsert_rowInsert`), and conversely, from a corner of a tableau it
produces a tableau and a letter whose insertion recovers the original tableau with the new cell
at that corner (`TauCeti.rowInsert_reverseRowInsert`, `List.IsTableauRows.reverseRowInsert`).
So insertion is a bijection between pairs of a tableau and a letter, and tableaux with a chosen
corner (`TauCeti.rowInsertEquiv`). Iterating it over the letters of a word, and recording the
new cells, is the Robinson--Schensted--Knuth correspondence.

## Main definitions

* `List.IsRowAbove`: one row can sit directly on top of another in a semistandard tableau.
* `List.IsTableauRows`: the rows of a semistandard tableau.
* `TauCeti.rowInsert`: Schensted row insertion of a letter into a tableau.
* `TauCeti.rowInsertIndex`: the row in which row insertion adds its new cell.
* `TauCeti.reverseRowInsert`: reverse row insertion from the end of a given row.
* `TauCeti.rowInsertEquiv`: row insertion as a bijection onto tableaux with a chosen corner.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Sections 1.1 and 4.1.
* B. E. Sagan, *The Symmetric Group*, 2nd ed., Springer GTM 203 (2001), Section 3.1.
-/

public section

namespace List

variable {α : Type*}

/-- The row `upper` can sit directly on top of the row `lower` in a semistandard tableau:
`lower` is no longer than `upper`, and each entry of `lower` is strictly greater than the entry
of `upper` above it. -/
structure IsRowAbove [LT α] (upper lower : List α) : Prop where
  /-- The lower row is no longer than the upper row. -/
  length_le : lower.length ≤ upper.length
  /-- Each entry of the lower row is strictly greater than the entry above it. -/
  getElem_lt : ∀ (j : ℕ) (hu : j < upper.length) (hl : j < lower.length), upper[j] < lower[j]

/-- Any row can sit on top of the empty row. -/
@[simp]
theorem isRowAbove_nil [LT α] (upper : List α) : upper.IsRowAbove [] :=
  ⟨by simp, fun _ _ hl => absurd hl (Nat.not_lt_zero _)⟩

/-- Lengthening the upper row keeps it on top of the lower row. -/
theorem IsRowAbove.append_right [LT α] {upper lower : List α} (h : upper.IsRowAbove lower)
    (extra : List α) : (upper ++ extra).IsRowAbove lower := by
  refine ⟨by simpa using h.length_le.trans (Nat.le_add_right _ _), fun j hu hl => ?_⟩
  rw [getElem_append_left (hl.trans_le h.length_le)]
  exact h.getElem_lt j _ hl

/-- If one row sits above a second, and the second above a third, the first sits above the
third. -/
theorem IsRowAbove.trans [LT α] [IsTrans α (· < ·)] {upper middle lower : List α}
    (h₁ : upper.IsRowAbove middle) (h₂ : middle.IsRowAbove lower) : upper.IsRowAbove lower :=
  ⟨h₂.length_le.trans h₁.length_le, fun j hu hl => IsTrans.trans _ _ _
    (h₁.getElem_lt j hu (hl.trans_le h₂.length_le)) (h₂.getElem_lt j _ hl)⟩

instance [LT α] [IsTrans α (· < ·)] : IsTrans (List α) IsRowAbove :=
  ⟨fun _ _ _ => IsRowAbove.trans⟩

/-- The rows, listed from top to bottom, of a semistandard tableau: every row is nonempty and
weakly increasing, and every row sits on top of the next one in the sense of `List.IsRowAbove`.
So the row lengths weakly decrease and the columns strictly increase. -/
structure IsTableauRows [Preorder α] (rows : List (List α)) : Prop where
  /-- No row is empty. -/
  nil_notMem : [] ∉ rows
  /-- Every row is weakly increasing. -/
  sortedLE : ∀ row ∈ rows, row.SortedLE
  /-- Every row sits on top of the next one. -/
  isChain : rows.IsChain IsRowAbove

variable [Preorder α]

/-- The empty tableau. -/
@[simp]
theorem isTableauRows_nil : IsTableauRows ([] : List (List α)) :=
  ⟨by simp, by simp, .nil⟩

/-- A tableau is a nonempty weakly increasing first row on top of a tableau. -/
theorem isTableauRows_cons {row : List α} {rows : List (List α)} :
    IsTableauRows (row :: rows) ↔ row ≠ [] ∧ row.SortedLE ∧ row.IsRowAbove (rows.headD []) ∧
      IsTableauRows rows := by
  constructor
  · rintro ⟨hne, hs, hc⟩
    rw [isChain_cons] at hc
    refine ⟨fun h => hne (h ▸ mem_cons_self), hs _ mem_cons_self, ?_,
      ⟨fun h => hne (mem_cons_of_mem _ h), fun r hr => hs r (mem_cons_of_mem _ hr), hc.2⟩⟩
    cases rows with
    | nil => exact isRowAbove_nil row
    | cons lower rows => exact hc.1 lower rfl
  · rintro ⟨hne, hs, habove, hrows⟩
    refine ⟨?_, ?_, isChain_cons.mpr ⟨?_, hrows.isChain⟩⟩
    · intro h
      rcases mem_cons.mp h with h | h
      · exact hne h.symm
      · exact hrows.nil_notMem h
    · simpa using ⟨hs, hrows.sortedLE⟩
    · cases rows with
      | nil => simp
      | cons lower rows => simpa using habove

/-- Deleting the first row of a tableau leaves a tableau. -/
theorem IsTableauRows.tail {row : List α} {rows : List (List α)}
    (h : IsTableauRows (row :: rows)) : IsTableauRows rows :=
  (isTableauRows_cons.mp h).2.2.2

/-- The row lengths of a tableau weakly decrease. Rows beyond the last one are read as empty. -/
theorem IsTableauRows.length_getD_succ_le {rows : List (List α)} (h : IsTableauRows rows)
    (i : ℕ) : (rows.getD (i + 1) []).length ≤ (rows.getD i []).length := by
  induction rows generalizing i with
  | nil => simp
  | cons row rows ih =>
    obtain ⟨-, -, habove, hrows⟩ := isTableauRows_cons.mp h
    cases i with
    | zero =>
      cases rows with
      | nil => simp
      | cons lower rows => simpa using habove.length_le
    | succ i => simpa using ih hrows i

end List

namespace TauCeti

open List

variable {α : Type*} [LinearOrder α]

/-! ### Row insertion -/

/-- **Schensted row insertion** `T ← x` of a letter `x` into a tableau given by its rows `T`:
insert `x` into the first row by `TauCeti.rowBump`, insert the bumped letter into the next row,
and so on, until a letter is appended at the end of a row, possibly a new last row. -/
def rowInsert (x : α) : List (List α) → List (List α)
  | [] => [[x]]
  | row :: rows => (rowBump x row).1 :: (rowBump x row).2.elim rows (rowInsert · rows)

/-- The index of the row in which `TauCeti.rowInsert x T` adds its new cell. -/
def rowInsertIndex (x : α) : List (List α) → ℕ
  | [] => 0
  | row :: rows => (rowBump x row).2.elim 0 (rowInsertIndex · rows + 1)

/-- Inserting into the empty tableau gives a one-cell tableau. -/
@[simp]
theorem rowInsert_nil (x : α) : rowInsert x [] = [[x]] := (rfl)

/-- Inserting into the empty tableau adds its cell in the first row. -/
@[simp]
theorem rowInsertIndex_nil (x : α) : rowInsertIndex x [] = 0 := (rfl)

/-- If nothing is bumped from the first row, insertion stops there. -/
theorem rowInsert_cons_of_eq_none {x : α} {row : List α} (rows : List (List α))
    (h : (rowBump x row).2 = none) : rowInsert x (row :: rows) = (rowBump x row).1 :: rows := by
  simp [rowInsert, h]

/-- A letter bumped from the first row is inserted into the remaining rows. -/
theorem rowInsert_cons_of_eq_some {x y : α} {row : List α} (rows : List (List α))
    (h : (rowBump x row).2 = some y) :
    rowInsert x (row :: rows) = (rowBump x row).1 :: rowInsert y rows := by
  simp [rowInsert, h]

/-- If nothing is bumped from the first row, the new cell is in the first row. -/
theorem rowInsertIndex_cons_of_eq_none {x : α} {row : List α} (rows : List (List α))
    (h : (rowBump x row).2 = none) : rowInsertIndex x (row :: rows) = 0 := by
  simp [rowInsertIndex, h]

/-- If a letter is bumped from the first row, the new cell is where its insertion into the
remaining rows puts it. -/
theorem rowInsertIndex_cons_of_eq_some {x y : α} {row : List α} (rows : List (List α))
    (h : (rowBump x row).2 = some y) :
    rowInsertIndex x (row :: rows) = rowInsertIndex y rows + 1 := by
  simp [rowInsertIndex, h]

/-- The first row of `T ← x` is the first row of `T` (empty if `T` is) after the first bump. -/
theorem headD_rowInsert (x : α) (rows : List (List α)) :
    (rowInsert x rows).headD [] = (rowBump x (rows.headD [])).1 := by
  cases rows with
  | nil => simp
  | cons row rows => cases h : (rowBump x row).2 <;> simp [rowInsert, h]

/-- **Row insertion conserves the letters**: `T ← x` has the letters of `T` together with `x`. -/
theorem flatten_rowInsert_perm (x : α) (rows : List (List α)) :
    (rowInsert x rows).flatten.Perm (x :: rows.flatten) := by
  induction rows generalizing x with
  | nil => simp
  | cons row rows ih =>
    have hp := rowBump_perm x row
    cases h : (rowBump x row).2 with
    | none =>
      rw [rowInsert_cons_of_eq_none rows h, flatten_cons, flatten_cons, ← cons_append]
      exact Perm.append_right _ (by simpa [h] using hp)
    | some y =>
      rw [rowInsert_cons_of_eq_some rows h, flatten_cons, flatten_cons, ← cons_append]
      refine ((ih y).append_left _).trans ?_
      rw [h] at hp
      simpa using hp.append_right rows.flatten

/-- The new cell is in an existing row or in the row just below the last one. -/
theorem rowInsertIndex_le_length (x : α) (rows : List (List α)) :
    rowInsertIndex x rows ≤ rows.length := by
  induction rows generalizing x with
  | nil => simp
  | cons row rows ih =>
    cases h : (rowBump x row).2 with
    | none => simp [rowInsertIndex_cons_of_eq_none rows h]
    | some y => simpa [rowInsertIndex_cons_of_eq_some rows h] using ih y

/-- **The shape of `T ← x`**: the row `TauCeti.rowInsertIndex x T` gains one cell and every
other row keeps its length. Rows beyond the last one are read as empty. -/
theorem length_getD_rowInsert (x : α) (rows : List (List α)) (i : ℕ) :
    ((rowInsert x rows).getD i []).length =
      (rows.getD i []).length + if i = rowInsertIndex x rows then 1 else 0 := by
  induction rows generalizing x i with
  | nil => cases i <;> simp
  | cons row rows ih =>
    have hl := length_rowBump x row
    cases h : (rowBump x row).2 with
    | none =>
      rw [h] at hl
      rw [rowInsert_cons_of_eq_none rows h, rowInsertIndex_cons_of_eq_none rows h]
      cases i <;> simp_all
    | some y =>
      rw [h] at hl
      rw [rowInsert_cons_of_eq_some rows h, rowInsertIndex_cons_of_eq_some rows h]
      cases i with
      | zero => simp_all
      | succ i => simpa using ih y i

/-- `T ← x` has one more row than `T` exactly when the new cell starts a new row. -/
theorem length_rowInsert (x : α) (rows : List (List α)) :
    (rowInsert x rows).length = max rows.length (rowInsertIndex x rows + 1) := by
  induction rows generalizing x with
  | nil => simp
  | cons row rows ih =>
    cases h : (rowBump x row).2 with
    | none => simp [rowInsert_cons_of_eq_none rows h, rowInsertIndex_cons_of_eq_none rows h]
    | some y =>
      simp only [rowInsert_cons_of_eq_some rows h, rowInsertIndex_cons_of_eq_some rows h,
        length_cons, ih y]
      omega

/-! ### Insertion preserves tableaux -/

/-- The column step of row insertion: if `upper` sits on top of `lower` and inserting `x` into
`upper` bumps `y`, then the new upper row sits on top of the result of inserting `y` into
`lower`. The bumped letter lands weakly to the left of the column it left. -/
private theorem isRowAbove_rowBump {x y : α} {upper lower : List α}
    (h : upper.IsRowAbove lower) (hbump : (rowBump x upper).2 = some y) :
    (rowBump x upper).1.IsRowAbove (rowBump y lower).1 := by
  obtain ⟨j, hj, hU', hUj, hpre, hxy⟩ :=
    exists_set_of_rowBump_snd_eq_some hbump
  rw [hU']
  cases hlow : (rowBump y lower).2 with
  | none =>
    have hle := (rowBump_snd_eq_none_iff y lower).mp hlow
    rw [rowBump_of_forall_le y lower hle]
    -- every entry of `lower` is at most `y`, so `lower` ends strictly before column `j`
    have hlen : lower.length ≤ j := by
      by_contra hcon
      have := h.getElem_lt j hj (by omega)
      exact absurd (hle _ (getElem_mem (by omega))) (not_le.mpr (hUj ▸ this))
    refine ⟨by simp; omega, fun c hu hl => ?_⟩
    simp only [length_append, length_cons, length_nil] at hl
    rw [getElem_set]
    by_cases hc : c < lower.length
    · rw [getElem_append_left hc, ite_eq_right (by omega)]
      exact h.getElem_lt c (by simpa using hu) hc
    · have hc' : c = lower.length := by omega
      subst hc'
      rw [getElem_append_right (by omega)]
      simp only [Nat.sub_self, getElem_cons_zero]
      split_ifs with hjc
      · exact hxy
      · exact (hpre _ (by omega)).trans_lt hxy
  | some w =>
    obtain ⟨j', hj', hL', _, hpre', hyw⟩ :=
      exists_set_of_rowBump_snd_eq_some hlow
    rw [hL']
    -- the first entry of `lower` exceeding `y` is weakly left of column `j`
    have hjj : j' ≤ j := by
      by_contra hcon
      have := h.getElem_lt j hj (by omega)
      exact absurd (hpre' j (by omega)) (not_le.mpr (hUj ▸ this))
    refine ⟨by simpa using h.length_le, fun c hu hl => ?_⟩
    simp only [List.length_set] at hu hl
    rw [getElem_set, getElem_set]
    split_ifs with h1 h2 h2
    · exact hxy
    · subst h1
      exact hxy.trans (hUj ▸ h.getElem_lt _ hj hl)
    · exact (hpre c (by omega)).trans_lt hxy
    · exact h.getElem_lt c hu hl

/-- **Row insertion preserves tableaux.** -/
theorem _root_.List.IsTableauRows.rowInsert {rows : List (List α)} (h : rows.IsTableauRows)
    (x : α) : (rowInsert x rows).IsTableauRows := by
  induction rows generalizing x with
  | nil => simp [isTableauRows_cons, sortedLE_nil]
  | cons row rows ih =>
    obtain ⟨hne, hs, habove, hrows⟩ := isTableauRows_cons.mp h
    have hs' := sortedLE_rowBump x hs
    have hne' : (rowBump x row).1 ≠ [] := by
      have := length_rowBump x row
      intro h0
      rw [h0] at this
      cases hb : (rowBump x row).2 <;> simp_all
    cases hb : (rowBump x row).2 with
    | none =>
      rw [rowInsert_cons_of_eq_none rows hb]
      refine isTableauRows_cons.mpr ⟨hne', hs', ?_, hrows⟩
      rw [rowBump_of_forall_le x row ((rowBump_snd_eq_none_iff x row).mp hb)]
      exact habove.append_right _
    | some y =>
      rw [rowInsert_cons_of_eq_some rows hb]
      refine isTableauRows_cons.mpr ⟨hne', hs', ?_, ih hrows y⟩
      rw [headD_rowInsert]
      exact isRowAbove_rowBump habove hb

/-- **The new cell of `T ← x` is a corner**: the row below it is strictly shorter. -/
theorem length_getD_succ_rowInsertIndex_lt {rows : List (List α)} (h : rows.IsTableauRows)
    (x : α) :
    ((rowInsert x rows).getD (rowInsertIndex x rows + 1) []).length <
      ((rowInsert x rows).getD (rowInsertIndex x rows) []).length := by
  rw [length_getD_rowInsert, length_getD_rowInsert, ite_eq_right (by omega), ite_eq_left rfl]
  exact Nat.lt_succ_of_le (h.length_getD_succ_le _)

/-- **A new cell below the first row sits under a longer row**: if `T ← x` adds its cell in row
`i + 1`, then row `i + 1` of `T` is strictly shorter than row `i`. -/
theorem length_getD_succ_lt_of_rowInsertIndex_eq_succ {rows : List (List α)}
    (h : rows.IsTableauRows) {x : α} {i : ℕ} (hi : rowInsertIndex x rows = i + 1) :
    (rows.getD (i + 1) []).length < (rows.getD i []).length := by
  have := (h.rowInsert x).length_getD_succ_le i
  rw [length_getD_rowInsert, length_getD_rowInsert, hi] at this
  split_ifs at this <;> omega

/-! ### Reverse insertion -/

/-- **Reverse row insertion** from the end of row `k`: remove the last entry of row `k`
(deleting the row if it becomes empty), insert it into row `k - 1` by
`TauCeti.reverseRowBump`, insert the letter returned into row `k - 2`, and so on up to the first
row. The second component is the letter returned by the first row, or `none` if some step
fails, which does not happen at a corner of a tableau. -/
def reverseRowInsert : ℕ → List (List α) → List (List α) × Option α
  | _, [] => ([], none)
  | 0, row :: rows => (if row.dropLast = [] then rows else row.dropLast :: rows, row.getLast?)
  | k + 1, row :: rows =>
    (reverseRowInsert k rows).2.elim (row :: (reverseRowInsert k rows).1, none) fun y =>
      ((reverseRowBump y row).1 :: (reverseRowInsert k rows).1, (reverseRowBump y row).2)

/-- Reverse insertion into the empty tableau fails. -/
@[simp]
theorem reverseRowInsert_nil (k : ℕ) : reverseRowInsert k ([] : List (List α)) = ([], none) := by
  cases k <;> rfl

/-- Reverse insertion from the end of the first row removes its last entry and returns it. -/
theorem reverseRowInsert_zero_cons (row : List α) (rows : List (List α)) :
    reverseRowInsert 0 (row :: rows) =
      (if row.dropLast = [] then rows else row.dropLast :: rows, row.getLast?) := (rfl)

/-- A letter returned by reverse insertion into the rows below the first is reverse bumped into
the first row. -/
theorem reverseRowInsert_succ_cons_of_eq_some {k : ℕ} {y : α} (row : List α)
    {rows : List (List α)} (h : (reverseRowInsert k rows).2 = some y) :
    reverseRowInsert (k + 1) (row :: rows) =
      ((reverseRowBump y row).1 :: (reverseRowInsert k rows).1, (reverseRowBump y row).2) := by
  simp [reverseRowInsert, h]

/-- If reverse insertion into the rows below the first fails, it fails. -/
theorem reverseRowInsert_succ_cons_of_eq_none {k : ℕ} (row : List α) {rows : List (List α)}
    (h : (reverseRowInsert k rows).2 = none) :
    reverseRowInsert (k + 1) (row :: rows) = (row :: (reverseRowInsert k rows).1, none) := by
  simp [reverseRowInsert, h]

/-- **Reverse insertion undoes insertion**: reverse inserting from the new cell of `T ← x`
recovers `T` and returns `x`. Only the rows of `T` being nonempty and weakly increasing is used. -/
theorem reverseRowInsert_rowInsert (x : α) {rows : List (List α)} (hne : [] ∉ rows)
    (hs : ∀ row ∈ rows, row.SortedLE) :
    reverseRowInsert (rowInsertIndex x rows) (rowInsert x rows) = (rows, some x) := by
  induction rows generalizing x with
  | nil => simp [reverseRowInsert_zero_cons]
  | cons row rows ih =>
    have hrow : row ≠ [] := fun h => hne (h ▸ mem_cons_self)
    cases hb : (rowBump x row).2 with
    | none =>
      rw [rowInsert_cons_of_eq_none rows hb, rowInsertIndex_cons_of_eq_none rows hb,
        rowBump_of_forall_le x row ((rowBump_snd_eq_none_iff x row).mp hb),
        reverseRowInsert_zero_cons]
      simp [hrow]
    | some y =>
      have ih' := ih y (fun h => hne (mem_cons_of_mem _ h))
        (fun r hr => hs r (mem_cons_of_mem _ hr))
      rw [rowInsert_cons_of_eq_some rows hb, rowInsertIndex_cons_of_eq_some rows hb,
        reverseRowInsert_succ_cons_of_eq_some _ (by rw [ih']), ih',
        reverseRowBump_rowBump_of_sortedLE x y (hs row mem_cons_self) hb]

/-- At a corner of the first row, a first row with a single entry is the whole tableau. -/
private theorem eq_nil_of_dropLast_eq_nil {α : Type*} [Preorder α]
    {row : List α} {rows : List (List α)}
    (h : (row :: rows).IsTableauRows)
    (hk : ((row :: rows).getD 1 []).length < ((row :: rows).getD 0 []).length)
    (hd : row.dropLast = []) : rows = [] := by
  obtain ⟨hne, -, -, hrows⟩ := isTableauRows_cons.mp h
  cases rows with
  | nil => rfl
  | cons lower rows =>
    have h1 := congrArg length hd
    rw [length_dropLast, length_nil] at h1
    have := length_pos_iff.mpr hne
    have hlow := length_pos_iff.mpr (isTableauRows_cons.mp hrows).1
    simp at hk
    omega

/-- The column relation between an old row `L` and the row `L'` replacing it after reverse
insertion, when the letter `L[c]` was ejected from column `c`: `L'` is no longer, its entries
are no smaller, and from column `c` on they exceed the ejected letter. -/
private structure ReverseStep (L L' : List α) (c : ℕ) (hc : c < L.length) : Prop where
  length_le : L'.length ≤ L.length
  getElem_le : ∀ (j : ℕ) (h₁ : j < L.length) (h₂ : j < L'.length), L[j] ≤ L'[j]
  getElem_lt : ∀ (j : ℕ) (h₂ : j < L'.length), c ≤ j → L[c] < L'[j]

/-- The column step of reverse insertion: if `U` sits on top of `L` and the letter `L[c]`
ejected from `L` reverse bumps `x` out of `U`, then the new upper row sits on top of the new
lower row, and the relation `ReverseStep` passes from `(L, L')` to the upper rows. -/
private theorem reverseStep_reverseRowBump {U L L' : List α} {c : ℕ} {hc : c < L.length}
    (hUL : U.IsRowAbove L) (hstep : ReverseStep L L' c hc) :
    ∃ d, ∃ hd : d < U.length, (reverseRowBump L[c] U).2 = some U[d] ∧
      (reverseRowBump L[c] U).1.IsRowAbove L' ∧ ReverseStep U (reverseRowBump L[c] U).1 d hd := by
  -- column `c` of `U` holds an entry smaller than the incoming letter, so the bump succeeds
  have hcU : c < U.length := hc.trans_le hUL.length_le
  have hsome : (reverseRowBump L[c] U).2 ≠ none := by
    rw [ne_eq, reverseRowBump_snd_eq_none_iff]
    exact fun hall => absurd (hall _ (getElem_mem hcU)) (not_le.mpr (hUL.getElem_lt c hcU hc))
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hsome
  obtain ⟨d, hd, hU', hUd, hpost, hxy⟩ :=
    exists_set_of_reverseRowBump_snd_eq_some hx
  -- the replaced position is weakly right of column `c`
  have hcd : c ≤ d := by
    by_contra hcon
    exact absurd (hpost c hcU (by omega)) (not_le.mpr (hUL.getElem_lt c hcU hc))
  refine ⟨d, hd, by rw [hx, hUd], ?_, ?_⟩
  · rw [hU']
    refine ⟨by simpa using hstep.length_le.trans hUL.length_le, fun j hu hl => ?_⟩
    simp only [List.length_set] at hu
    rw [getElem_set]
    split_ifs with hdj
    · subst hdj
      exact hstep.getElem_lt d hl hcd
    · have hjL := hl.trans_le hstep.length_le
      exact (hUL.getElem_lt j hu hjL).trans_le (hstep.getElem_le j hjL hl)
  · rw [hU']
    refine ⟨by simp, fun j h₁ h₂ => ?_, fun j h₂ hdj => ?_⟩
    · rw [getElem_set]
      split_ifs with hdj
      · subst hdj
        exact hUd ▸ hxy.le
      · exact le_rfl
    · simp only [List.length_set] at h₂
      rw [getElem_set]
      split_ifs with hdj'
      · exact hUd ▸ hxy
      · exact hUd ▸ hxy.trans_le (hpost j h₂ (by omega))

/-- The invariant of reverse insertion from a corner: the letter returned was ejected from
some column `c` of the first row, the result is a tableau, and its first row satisfies
`ReverseStep`. Reinserting the returned letter recovers the tableau and the chosen corner. -/
private theorem exists_reverseRowInsert_of_isTableauRows {k : ℕ} {rows : List (List α)}
    (h : rows.IsTableauRows)
    (hk : (rows.getD (k + 1) []).length < (rows.getD k []).length) :
    ∃ c, ∃ hc : c < (rows.headD []).length,
      (reverseRowInsert k rows).2 = some (rows.headD [])[c] ∧
        (reverseRowInsert k rows).1.IsTableauRows ∧
        ReverseStep (rows.headD []) ((reverseRowInsert k rows).1.headD []) c hc ∧
        rowInsert (rows.headD [])[c] (reverseRowInsert k rows).1 = rows ∧
        rowInsertIndex (rows.headD [])[c] (reverseRowInsert k rows).1 = k := by
  induction rows generalizing k with
  | nil => simp at hk
  | cons row rows ih =>
    obtain ⟨hne, hs, habove, hrows⟩ := isTableauRows_cons.mp h
    simp only [headD_cons]
    cases k with
    | zero =>
      -- remove the last entry of the first row
      have hlen : 0 < row.length := length_pos_iff.mpr hne
      have hlast : row.dropLast ++ [row[row.length - 1]] = row := by
        simpa only [getLast_eq_getElem] using dropLast_concat_getLast hne
      have hle : ∀ z ∈ row.dropLast, z ≤ row[row.length - 1] := by
        have hs' := hs
        rw [← hlast, sortedLE_append] at hs'
        exact fun z hz => hs'.2.2 z hz _ mem_cons_self
      refine ⟨row.length - 1, by omega, ?_⟩
      by_cases hd : row.dropLast = []
      · -- a one-cell first row at a corner is the whole tableau
        obtain rfl := eq_nil_of_dropLast_eq_nil h hk hd
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp [reverseRowInsert_zero_cons, getLast?_eq_getElem?]
        · simp [reverseRowInsert_zero_cons, hd]
        · simp only [reverseRowInsert_zero_cons, ite_eq_left hd, headD_nil]
          exact ⟨by simp, fun _ _ h₂ => absurd h₂ (by simp), fun _ h₂ _ => absurd h₂ (by simp)⟩
        · simpa [reverseRowInsert_zero_cons, hd] using congrArg (fun r => [r]) hlast
        · simp [reverseRowInsert_zero_cons, hd]
      · have hk' : (rows.headD []).length ≤ row.dropLast.length := by
          cases rows with
          | nil => simp
          | cons lower rows => simp at hk ⊢; omega
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp [reverseRowInsert_zero_cons, getLast?_eq_getElem?]
        · rw [reverseRowInsert_zero_cons, ite_eq_right hd]
          refine isTableauRows_cons.mpr ⟨hd, sortedLE_iff_pairwise.mpr
            ((sortedLE_iff_pairwise.mp hs).sublist (dropLast_sublist _)), ⟨hk', fun j hu hl => ?_⟩,
            hrows⟩
          rw [getElem_dropLast]
          exact habove.getElem_lt j (by simp at hu; omega) hl
        · rw [reverseRowInsert_zero_cons, ite_eq_right hd]
          refine ⟨by simp, fun j h₁ h₂ => ?_, fun j h₂ hj => ?_⟩
          · simp [getElem_dropLast]
          · simp at h₂; omega
        · simp only [reverseRowInsert_zero_cons, ite_eq_right hd]
          rw [rowInsert_cons_of_eq_none rows ((rowBump_snd_eq_none_iff _ _).mpr hle),
            rowBump_of_forall_le _ _ hle, hlast]
        · simp only [reverseRowInsert_zero_cons, ite_eq_right hd]
          exact rowInsertIndex_cons_of_eq_none rows ((rowBump_snd_eq_none_iff _ _).mpr hle)
    | succ k =>
      obtain ⟨c, hc, hret, htab, hstep, hins, hidx⟩ := ih hrows (by simpa using hk)
      obtain ⟨d, hd, hx, hU, hstep'⟩ := reverseStep_reverseRowBump habove hstep
      -- Recover the first row by the local inverse, and the remaining rows by induction.
      have hb := rowBump_reverseRowBump_of_sortedLE _ _ hs hx
      rw [reverseRowInsert_succ_cons_of_eq_some row hret]
      refine ⟨d, hd, hx, isTableauRows_cons.mpr ⟨?_, ?_, hU, htab⟩, hstep', ?_, ?_⟩
      · intro h0
        have := length_reverseRowBump (rows.headD [])[c] row
        rw [h0, hx] at this
        simp only [length_nil, Option.toList_some, length_singleton, Nat.zero_add] at this
        exact hne (length_eq_zero_iff.mp (by omega))
      · exact sortedLE_reverseRowBump _ hs
      · rw [rowInsert_cons_of_eq_some _ (by rw [hb]), hb, hins]
      · rw [rowInsertIndex_cons_of_eq_some _ (by rw [hb]), hidx]

/-- **Reverse insertion preserves tableaux at corners**: reverse inserting from the end of a
row `k` of a tableau whose next row is strictly shorter yields a tableau. -/
theorem _root_.List.IsTableauRows.reverseRowInsert {k : ℕ} {rows : List (List α)}
    (h : rows.IsTableauRows)
    (hk : (rows.getD (k + 1) []).length < (rows.getD k []).length) :
    (reverseRowInsert k rows).1.IsTableauRows := by
  obtain ⟨-, -, -, htab, -⟩ := exists_reverseRowInsert_of_isTableauRows h hk
  exact htab

/-- **Insertion undoes reverse insertion at a corner.** If row `k + 1` of a tableau `T` is
strictly shorter than row `k`, then reverse insertion from the end of row `k` returns a letter
`x` and a tableau `T'` such that `T' ← x` is `T`, with its new cell in row `k`. -/
theorem rowInsert_reverseRowInsert {k : ℕ} {rows : List (List α)} (h : rows.IsTableauRows)
    (hk : (rows.getD (k + 1) []).length < (rows.getD k []).length) :
    ∃ x, (reverseRowInsert k rows).2 = some x ∧
      rowInsert x (reverseRowInsert k rows).1 = rows ∧
        rowInsertIndex x (reverseRowInsert k rows).1 = k := by
  obtain ⟨c, hc, hret, -, -, hins, hidx⟩ := exists_reverseRowInsert_of_isTableauRows h hk
  exact ⟨_, hret, hins, hidx⟩

/-! ### Insertion as a bijection -/

/-- **Row insertion is a bijection** between pairs of a tableau and a letter, and pairs of a
tableau and a row `k` ending in a corner, that is, whose next row is strictly shorter. It sends
`(T, x)` to `T ← x` with the row of its new cell; the inverse is reverse row insertion. -/
def rowInsertEquiv :
    {rows : List (List α) // rows.IsTableauRows} × α ≃
      {p : List (List α) × ℕ //
        p.1.IsTableauRows ∧ (p.1.getD (p.2 + 1) []).length < (p.1.getD p.2 []).length} where
  toFun p := ⟨(rowInsert p.2 p.1.1, rowInsertIndex p.2 p.1.1), p.1.2.rowInsert p.2,
    length_getD_succ_rowInsertIndex_lt p.1.2 p.2⟩
  invFun p := (⟨(reverseRowInsert p.1.2 p.1.1).1, p.2.1.reverseRowInsert p.2.2⟩,
    (reverseRowInsert p.1.2 p.1.1).2.get
      (Option.isSome_iff_exists.mpr ((rowInsert_reverseRowInsert p.2.1 p.2.2).imp fun _ h => h.1)))
  left_inv p := by
    have h := reverseRowInsert_rowInsert p.2 p.1.2.nil_notMem p.1.2.sortedLE
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp [h]
    · simp [h]
  right_inv p := by
    obtain ⟨x, hx, hins, hidx⟩ := rowInsert_reverseRowInsert p.2.1 p.2.2
    refine Subtype.ext (Prod.ext ?_ ?_)
    · simpa [hx] using hins
    · simpa [hx] using hidx

/-- `rowInsertEquiv` sends `(T, x)` to `T ← x` with the row of its new cell. -/
@[simp]
theorem rowInsertEquiv_apply_coe (rows : {rows : List (List α) // rows.IsTableauRows}) (x : α) :
    (rowInsertEquiv (rows, x) : List (List α) × ℕ) =
      (rowInsert x rows.1, rowInsertIndex x rows.1) := (rfl)

/-- The tableau of `rowInsertEquiv.symm p` is the result of reverse row insertion. -/
@[simp]
theorem rowInsertEquiv_symm_apply_fst_coe
    (p : {p : List (List α) × ℕ //
      p.1.IsTableauRows ∧ (p.1.getD (p.2 + 1) []).length < (p.1.getD p.2 []).length}) :
    ((rowInsertEquiv.symm p).1 : List (List α)) = (reverseRowInsert p.1.2 p.1.1).1 := (rfl)

/-- The letter of `rowInsertEquiv.symm p` is the letter returned by reverse row insertion. -/
theorem some_rowInsertEquiv_symm_apply_snd
    (p : {p : List (List α) × ℕ //
      p.1.IsTableauRows ∧ (p.1.getD (p.2 + 1) []).length < (p.1.getD p.2 []).length}) :
    some (rowInsertEquiv.symm p).2 = (reverseRowInsert p.1.2 p.1.1).2 := by
  simp [rowInsertEquiv]

end TauCeti
