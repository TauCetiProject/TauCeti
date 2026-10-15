/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Prod.Lex
public import TauCeti.Combinatorics.Young.Schensted.Bumping

/-!
# The Robinson--Schensted--Knuth correspondence for two-line arrays

A **two-line array** is a list of pairs `(u₁, v₁), (u₂, v₂), …, (uₙ, vₙ)` which is weakly
increasing in the lexicographic order: `u₁ ≤ u₂ ≤ ⋯ ≤ uₙ`, and `vₖ ≤ vₖ₊₁` whenever
`uₖ = uₖ₊₁`. Such arrays are the same thing as finitely supported matrices of natural numbers,
the entry in position `(u, v)` being the number of occurrences of the pair `(u, v)`.

Knuth's generalization of the Robinson--Schensted correspondence inserts the bottom letters
`v₁, v₂, …, vₙ` one after another into the empty tableau by Schensted row insertion, giving the
**insertion tableau** `P`, and records the top letter `uₖ` at the end of the row in which the
insertion of `vₖ` adds its new cell, giving the **recording tableau** `Q`. Both are semistandard
tableaux of the same shape, `P` has the bottom letters as entries and `Q` the top letters, and
every such pair arises from exactly one two-line array. The proof that `Q` is semistandard and
that the array can be recovered rests on the bumping lemma
(`TauCeti.rowInsert_column_lt_of_le`): the letters inserted under equal top letters weakly
increase, so they add their cells in strictly increasing columns, and the cells recorded with a
given top letter form a horizontal strip. The last of them is therefore the rightmost occurrence
of the largest entry of `Q`, which sits at the end of the highest row ending in that entry;
reverse row insertion from that cell (`TauCeti.reverseRowInsert`) undoes the last step.

## Main definitions

* `TauCeti.appendToRow`: append a letter at the end of a given row of a list of rows.
* `TauCeti.robinsonSchenstedKnuth`: the insertion and recording tableaux of a list of pairs.
* `TauCeti.robinsonSchenstedKnuthEquiv`: the Robinson--Schensted--Knuth correspondence, as a
  bijection from two-line arrays onto pairs of semistandard tableaux of the same shape.

## Main statements

* `TauCeti.length_getD_robinsonSchenstedKnuth_fst`: the two tableaux have the same shape.
* `TauCeti.flatten_robinsonSchenstedKnuth_fst_perm` and
  `TauCeti.flatten_robinsonSchenstedKnuth_snd_perm`: the entries of the insertion and recording
  tableaux are the bottom and the top letters of the array.
* `TauCeti.isTableauRows_robinsonSchenstedKnuth_snd`: the recording tableau of a two-line array is
  semistandard.
* `TauCeti.robinsonSchenstedKnuth_injOn` and `TauCeti.exists_robinsonSchenstedKnuth_eq_iff`: the
  correspondence is injective on two-line arrays, and its image consists of the pairs of
  semistandard tableaux of the same shape.

## References

* D. E. Knuth, *Permutations, matrices, and generalized Young tableaux*, Pacific J. Math. 34
  (1970), 709--727.
* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Section 4.1.
* R. P. Stanley, *Enumerative Combinatorics*, Vol. 2, Cambridge University Press (1999),
  Section 7.11.
-/

public section

namespace TauCeti

open List

variable {α β : Type*}

/-! ### Appending a letter to a row -/

/-- Append the letter `a` at the end of row `k` of a list of rows. If `k` is at least the number
of rows, `a` starts a new last row. -/
def appendToRow (a : α) : ℕ → List (List α) → List (List α)
  | _, [] => [[a]]
  | 0, row :: rows => (row ++ [a]) :: rows
  | k + 1, row :: rows => row :: appendToRow a k rows

/-- **The rows of `TauCeti.appendToRow a k`**: row `k` gains the letter `a` at its end, and every
other row is unchanged. Rows beyond the last one are read as empty. -/
theorem getD_appendToRow (a : α) {k : ℕ} {rows : List (List α)} (hk : k ≤ rows.length) (i : ℕ) :
    (appendToRow a k rows).getD i [] = if i = k then rows.getD k [] ++ [a] else rows.getD i [] := by
  induction rows generalizing k i with
  | nil =>
    obtain rfl : k = 0 := by simpa using hk
    cases i <;> simp [appendToRow]
  | cons row rows ih =>
    cases k with
    | zero => cases i <;> simp [appendToRow]
    | succ k =>
      cases i with
      | zero => simp [appendToRow]
      | succ i => simpa [appendToRow] using ih (by simpa using hk) i

/-- Appending to row `k` adds a new row exactly when `k` is the number of rows. -/
theorem length_appendToRow (a : α) {k : ℕ} {rows : List (List α)} (hk : k ≤ rows.length) :
    (appendToRow a k rows).length = max rows.length (k + 1) := by
  induction rows generalizing k with
  | nil =>
    obtain rfl : k = 0 := by simpa using hk
    simp [appendToRow]
  | cons row rows ih =>
    cases k with
    | zero => simp [appendToRow]
    | succ k =>
      simp only [appendToRow, length_cons, ih (by simpa using hk : k ≤ rows.length)]
      omega

/-- Appending to a row adds the letter to the entries. -/
theorem flatten_appendToRow_perm (a : α) (k : ℕ) (rows : List (List α)) :
    (appendToRow a k rows).flatten.Perm (rows.flatten ++ [a]) := by
  induction rows generalizing k with
  | nil => simp [appendToRow]
  | cons row rows ih =>
    cases k with
    | zero =>
      simpa [appendToRow] using (perm_append_comm (l₁ := [a]) (l₂ := rows.flatten)).append_left row
    | succ k => simpa [appendToRow] using (ih k).append_left row

/-- **Appending to a row preserves tableaux** when the new cell is a corner of the new shape and
its entry fits: it is at least every entry of its row, and greater than the entry above it. -/
theorem _root_.List.IsTableauRows.appendToRow [Preorder α] {rows : List (List α)}
    (h : rows.IsTableauRows) {a : α} {k : ℕ} (hk : k ≤ rows.length)
    (hle : ∀ x ∈ rows.getD k [], x ≤ a)
    (habove : ∀ i, k = i + 1 → ∃ hlen : (rows.getD k []).length < (rows.getD i []).length,
      (rows.getD i [])[(rows.getD k []).length] < a) :
    (appendToRow a k rows).IsTableauRows := by
  induction rows generalizing k with
  | nil =>
    obtain rfl : k = 0 := by simpa using hk
    simpa [TauCeti.appendToRow, isTableauRows_cons] using
      sortedLE_iff_pairwise.mpr (pairwise_singleton _ a)
  | cons row rows ih =>
    obtain ⟨hne, hs, hab, hrows⟩ := isTableauRows_cons.mp h
    cases k with
    | zero =>
      refine isTableauRows_cons.mpr ⟨by simp, ?_, hab.append_right _, hrows⟩
      exact sortedLE_iff_pairwise.mpr (pairwise_append.mpr ⟨sortedLE_iff_pairwise.mp hs,
        pairwise_singleton _ _, fun x hx y hy => by
          simpa [mem_singleton.mp hy] using hle x (by simpa using hx)⟩)
    | succ k =>
      refine isTableauRows_cons.mpr ⟨hne, hs, ?_, ih hrows (by simpa using hk)
        (by simpa using hle) fun i hi => by simpa using habove (i + 1) (by omega)⟩
      cases k with
      | zero =>
        obtain ⟨hlen, hlt⟩ := habove 0 rfl
        cases rows with
        | nil => simpa [TauCeti.appendToRow] using (isRowAbove_nil row).append_singleton hlen hlt
        | cons lower rows => simpa [TauCeti.appendToRow] using hab.append_singleton hlen hlt
      | succ k =>
        cases rows with
        | nil => simp at hk
        | cons lower rows => simpa [TauCeti.appendToRow] using hab

/-! ### Removing the last letter of a row -/

/-- Remove the last letter of row `k` of a list of rows, deleting the row if it becomes empty.
At a corner of a tableau this undoes `TauCeti.appendToRow`. -/
private def dropLastOfRow : ℕ → List (List α) → List (List α)
  | _, [] => []
  | 0, row :: rows => if row.dropLast = [] then rows else row.dropLast :: rows
  | k + 1, row :: rows => row :: dropLastOfRow k rows

private theorem dropLastOfRow_appendToRow (a : α) {k : ℕ} {rows : List (List α)}
    (hne : [] ∉ rows) (hk : k ≤ rows.length) : dropLastOfRow k (appendToRow a k rows) = rows := by
  induction rows generalizing k with
  | nil =>
    obtain rfl : k = 0 := by simpa using hk
    simp [appendToRow, dropLastOfRow]
  | cons row rows ih =>
    have hrow : row ≠ [] := fun h => hne (h ▸ mem_cons_self)
    cases k with
    | zero => simp [appendToRow, dropLastOfRow, hrow]
    | succ k =>
      simpa [appendToRow, dropLastOfRow] using
        ih (fun h => hne (mem_cons_of_mem _ h)) (by simpa using hk)

private theorem getD_dropLastOfRow [Preorder α] {k : ℕ} {rows : List (List α)}
    (h : rows.IsTableauRows) (hk : (rows.getD (k + 1) []).length < (rows.getD k []).length)
    (i : ℕ) :
    (dropLastOfRow k rows).getD i [] =
      if i = k then (rows.getD k []).dropLast else rows.getD i [] := by
  induction rows generalizing k i with
  | nil => simp at hk
  | cons row rows ih =>
    cases k with
    | zero =>
      by_cases hd : row.dropLast = []
      · obtain rfl := h.eq_nil_of_dropLast_eq_nil (by simpa using hk) hd
        cases i <;> simp [dropLastOfRow, hd]
      · cases i <;> simp [dropLastOfRow, hd]
    | succ k =>
      cases i with
      | zero => simp [dropLastOfRow]
      | succ i => simpa [dropLastOfRow] using ih h.tail (by simpa using hk) i

private theorem appendToRow_dropLastOfRow [Preorder α] {k : ℕ} {rows : List (List α)}
    (h : rows.IsTableauRows) (hk : (rows.getD (k + 1) []).length < (rows.getD k []).length)
    {a : α} (ha : (rows.getD k []).getLast? = some a) :
    appendToRow a k (dropLastOfRow k rows) = rows := by
  induction rows generalizing k with
  | nil => simp at ha
  | cons row rows ih =>
    cases k with
    | zero =>
      obtain ⟨ys, rfl⟩ := getLast?_eq_some_iff.mp (by simpa using ha)
      by_cases hd : ys = []
      · subst hd
        obtain rfl := h.eq_nil_of_dropLast_eq_nil (by simpa using hk) (by simp)
        simp [appendToRow, dropLastOfRow]
      · simp [appendToRow, dropLastOfRow, hd]
    | succ k =>
      simpa [appendToRow, dropLastOfRow] using ih h.tail (by simpa using hk) (by simpa using ha)

private theorem _root_.List.IsTableauRows.dropLastOfRow [Preorder α] {k : ℕ}
    {rows : List (List α)} (h : rows.IsTableauRows)
    (hk : (rows.getD (k + 1) []).length < (rows.getD k []).length) :
    (dropLastOfRow k rows).IsTableauRows := by
  induction rows generalizing k with
  | nil => simp at hk
  | cons row rows ih =>
    obtain ⟨hne, hs, hab, hrows⟩ := isTableauRows_cons.mp h
    cases k with
    | zero =>
      by_cases hd : row.dropLast = []
      · simpa [TauCeti.dropLastOfRow, hd] using hrows
      · simp only [TauCeti.dropLastOfRow, hd, ite_false]
        have hk' : (rows.headD []).length ≤ row.dropLast.length := by
          cases rows with
          | nil => simp
          | cons lower rows => simp at hk ⊢; omega
        refine isTableauRows_cons.mpr ⟨hd, sortedLE_iff_pairwise.mpr
          ((sortedLE_iff_pairwise.mp hs).sublist (dropLast_sublist _)), ⟨hk', fun j hu hl => ?_⟩,
          hrows⟩
        rw [getElem_dropLast]
        exact hab.getElem_lt j (by simp at hu; omega) hl
    | succ k =>
      refine isTableauRows_cons.mpr ⟨hne, hs, ?_, ih hrows (by simpa using hk)⟩
      cases k with
      | zero =>
        cases rows with
        | nil => simp [TauCeti.dropLastOfRow]
        | cons lower rows =>
          by_cases hd : lower.dropLast = []
          · obtain rfl := hrows.eq_nil_of_dropLast_eq_nil (by simpa using hk) hd
            simp [TauCeti.dropLastOfRow, hd]
          · simp only [TauCeti.dropLastOfRow, hd, ite_false, headD_cons]
            refine ⟨by rw [length_dropLast]; exact (Nat.sub_le _ _).trans hab.length_le,
              fun j hu hl => ?_⟩
            rw [getElem_dropLast]
            exact hab.getElem_lt j hu _
      | succ k =>
        cases rows with
        | nil => simp [TauCeti.dropLastOfRow]
        | cons lower rows => simpa [TauCeti.dropLastOfRow] using hab

/-! ### The correspondence -/

section Correspondence

variable [LinearOrder β]

/-- The **Robinson--Schensted--Knuth correspondence** of a list of pairs
`(u₁, v₁), …, (uₙ, vₙ)`: the rows of the insertion tableau `(⋯((∅ ← v₁) ← v₂) ⋯) ← vₙ`, together
with the rows of the recording tableau, obtained by appending `uₖ` at the end of the row in which
the insertion of `vₖ` adds its new cell. -/
def robinsonSchenstedKnuth (ws : List (α × β)) : List (List β) × List (List α) :=
  ws.foldl (fun p w => (rowInsert w.2 p.1, appendToRow w.1 (rowInsertIndex w.2 p.1) p.2)) ([], [])

/-- The empty list of pairs has two empty tableaux. -/
@[simp]
theorem robinsonSchenstedKnuth_nil :
    robinsonSchenstedKnuth ([] : List (α × β)) = ([], []) := (rfl)

/-- Appending a pair `w` inserts `w.2` into the insertion tableau, and appends `w.1` to the row
of the recording tableau in which the new cell lies. -/
@[simp]
theorem robinsonSchenstedKnuth_append_singleton (ws : List (α × β)) (w : α × β) :
    robinsonSchenstedKnuth (ws ++ [w]) =
      (rowInsert w.2 (robinsonSchenstedKnuth ws).1,
        appendToRow w.1 (rowInsertIndex w.2 (robinsonSchenstedKnuth ws).1)
          (robinsonSchenstedKnuth ws).2) := by
  simp [robinsonSchenstedKnuth]

/-- The insertion tableau is a tableau. -/
theorem isTableauRows_robinsonSchenstedKnuth_fst (ws : List (α × β)) :
    (robinsonSchenstedKnuth ws).1.IsTableauRows := by
  induction ws using reverseRecOn with
  | nil => simp
  | append_singleton ws w ih => simpa using ih.rowInsert w.2

/-- The two tableaux have the same number of rows. -/
theorem length_robinsonSchenstedKnuth_snd (ws : List (α × β)) :
    (robinsonSchenstedKnuth ws).2.length = (robinsonSchenstedKnuth ws).1.length := by
  induction ws using reverseRecOn with
  | nil => simp
  | append_singleton ws w ih =>
    rw [robinsonSchenstedKnuth_append_singleton, length_rowInsert,
      length_appendToRow _ (ih ▸ rowInsertIndex_le_length _ _), ih]

private theorem rowInsertIndex_le_length_snd (ws : List (α × β)) (b : β) :
    rowInsertIndex b (robinsonSchenstedKnuth ws).1 ≤ (robinsonSchenstedKnuth ws).2.length :=
  length_robinsonSchenstedKnuth_snd ws ▸ rowInsertIndex_le_length _ _

/-- **The two tableaux have the same shape**: row `i` of the insertion tableau has as many cells
as row `i` of the recording tableau. -/
theorem length_getD_robinsonSchenstedKnuth_fst (ws : List (α × β)) (i : ℕ) :
    ((robinsonSchenstedKnuth ws).1.getD i []).length =
      ((robinsonSchenstedKnuth ws).2.getD i []).length := by
  induction ws using reverseRecOn with
  | nil => simp
  | append_singleton ws w ih =>
    rw [robinsonSchenstedKnuth_append_singleton, length_getD_rowInsert,
      getD_appendToRow _ (rowInsertIndex_le_length_snd ws w.2)]
    split_ifs with h
    · subst h
      rw [length_append, length_singleton, ih]
    · rw [Nat.add_zero, ih]

/-- **The insertion tableau has the bottom letters as entries.** -/
theorem flatten_robinsonSchenstedKnuth_fst_perm (ws : List (α × β)) :
    (robinsonSchenstedKnuth ws).1.flatten.Perm (ws.map Prod.snd) := by
  induction ws using reverseRecOn with
  | nil => simp
  | append_singleton ws w ih =>
    rw [robinsonSchenstedKnuth_append_singleton, map_append, map_singleton]
    exact (flatten_rowInsert_perm _ _).trans ((ih.cons _).trans (perm_append_singleton _ _).symm)

/-- **The recording tableau has the top letters as entries.** -/
theorem flatten_robinsonSchenstedKnuth_snd_perm (ws : List (α × β)) :
    (robinsonSchenstedKnuth ws).2.flatten.Perm (ws.map Prod.fst) := by
  induction ws using reverseRecOn with
  | nil => simp
  | append_singleton ws w ih =>
    rw [robinsonSchenstedKnuth_append_singleton, map_append, map_singleton]
    exact (flatten_appendToRow_perm _ _ _).trans (ih.append_right _)

variable [LinearOrder α]

/-- Every earlier pair of a two-line array is lexicographically at most a later one. -/
private theorem toLex_le_of_mem {ws : List (α × β)} {w v : α × β}
    (h : ((ws ++ [w]).map toLex).SortedLE) (hv : v ∈ ws) : toLex v ≤ toLex w := by
  simp only [map_append, map_singleton, sortedLE_append, mem_map, mem_singleton] at h
  exact h.2.2 _ ⟨v, hv, rfl⟩ _ rfl

/-- A list of pairs followed by one more pair is a two-line array exactly when the list is one
and its last pair is lexicographically at most the new pair. -/
private theorem sortedLE_map_toLex_append_singleton {ws : List (α × β)} {w : α × β} :
    ((ws ++ [w]).map toLex).SortedLE ↔
      (ws.map toLex).SortedLE ∧ ∀ v ∈ ws.getLast?, toLex v ≤ toLex w := by
  rw [map_append, map_singleton, sortedLE_iff_isChain, sortedLE_iff_isChain, isChain_append,
    getLast?_map]
  cases ws.getLast? <;> simp

/-- The entries of the recording tableau of the earlier pairs of a two-line array are at most the
last top letter. -/
private theorem le_of_mem_flatten_snd {ws : List (α × β)} {w : α × β}
    (h : ((ws ++ [w]).map toLex).SortedLE) {x : α}
    (hx : x ∈ (robinsonSchenstedKnuth ws).2.flatten) : x ≤ w.1 := by
  obtain ⟨v, hv, rfl⟩ := mem_map.mp ((flatten_robinsonSchenstedKnuth_snd_perm ws).subset hx)
  exact Prod.Lex.monotone_fst _ _ (toLex_le_of_mem h hv)

/-- **The cells recorded with the last top letter form a horizontal strip**: in the recording
tableau of the earlier pairs of a two-line array ending in `(a, b)`, every cell containing `a` lies
strictly to the left of the cell added by inserting `b`. -/
private theorem lt_of_getElem?_getD_snd_eq_some (ws : List (α × β)) (a : α) (b : β)
    (h : ((ws ++ [(a, b)]).map toLex).SortedLE) {i j : ℕ}
    (ha : ((robinsonSchenstedKnuth ws).2.getD i [])[j]? = some a) :
    j < ((robinsonSchenstedKnuth ws).1.getD (rowInsertIndex b (robinsonSchenstedKnuth ws).1)
      []).length := by
  induction ws using reverseRecOn generalizing a b i j with
  | nil => simp at ha
  | append_singleton ws w ih =>
    obtain ⟨hws, hlast⟩ := sortedLE_map_toLex_append_singleton.mp h
    have hwab := hlast w (by simp)
    have hP := isTableauRows_robinsonSchenstedKnuth_fst ws
    -- If `w` also has top letter `a`, its bottom letter is at most `b`, so by the bumping lemma
    -- the cell added for `w` lies strictly left of the cell added for `b`.
    have hcol (hw : w.1 = a) :
        ((robinsonSchenstedKnuth ws).1.getD (rowInsertIndex w.2 (robinsonSchenstedKnuth ws).1)
          []).length <
        ((rowInsert w.2 (robinsonSchenstedKnuth ws).1).getD
          (rowInsertIndex b (rowInsert w.2 (robinsonSchenstedKnuth ws).1)) []).length := by
      refine rowInsert_column_lt_of_le hP ?_
      rcases Prod.Lex.toLex_le_toLex.mp hwab with hlt | ⟨-, hle⟩
      · exact absurd hw (ne_of_lt hlt)
      · exact hle
    -- An old cell containing `a` forces `w.1 = a`, and then lies left of the cell added for `w`.
    have hold (ha' : ((robinsonSchenstedKnuth ws).2.getD i [])[j]? = some a) := by
      have hw : w.1 = a := le_antisymm (Prod.Lex.monotone_fst _ _ hwab)
        (le_of_mem_flatten_snd hws (mem_flatten_of_mem_getD (mem_of_getElem? ha')))
      exact (ih w.1 w.2 hws (hw ▸ ha')).trans (hcol hw)
    rw [robinsonSchenstedKnuth_append_singleton] at ha ⊢
    rw [getD_appendToRow _ (rowInsertIndex_le_length_snd ws w.2)] at ha
    split_ifs at ha with hi
    · subst hi
      by_cases hj : j < ((robinsonSchenstedKnuth ws).2.getD
          (rowInsertIndex w.2 (robinsonSchenstedKnuth ws).1) []).length
      · rw [getElem?_append_left hj] at ha
        exact hold ha
      · rw [getElem?_append_right (not_lt.mp hj), getElem?_singleton] at ha
        split_ifs at ha with h0
        obtain rfl : w.1 = a := by simpa using ha
        obtain rfl : j = ((robinsonSchenstedKnuth ws).2.getD
            (rowInsertIndex w.2 (robinsonSchenstedKnuth ws).1) []).length := by omega
        rw [← length_getD_robinsonSchenstedKnuth_fst]
        exact hcol rfl
    · exact hold ha

/-- **The recording tableau of a two-line array is a tableau.** -/
theorem isTableauRows_robinsonSchenstedKnuth_snd {ws : List (α × β)}
    (h : (ws.map toLex).SortedLE) : (robinsonSchenstedKnuth ws).2.IsTableauRows := by
  induction ws using reverseRecOn with
  | nil => simp
  | append_singleton ws w ih =>
    have hws := (sortedLE_map_toLex_append_singleton.mp h).1
    have hP := isTableauRows_robinsonSchenstedKnuth_fst ws
    rw [robinsonSchenstedKnuth_append_singleton]
    refine (ih hws).appendToRow (rowInsertIndex_le_length_snd ws w.2)
      (fun x hx => le_of_mem_flatten_snd h (mem_flatten_of_mem_getD hx)) fun i hi => ?_
    have hlen := length_getD_succ_lt_of_rowInsertIndex_eq_succ hP hi
    rw [← hi, length_getD_robinsonSchenstedKnuth_fst, length_getD_robinsonSchenstedKnuth_fst]
      at hlen
    refine ⟨hlen, lt_of_le_of_ne
      (le_of_mem_flatten_snd h (mem_flatten_of_mem_getD (getElem_mem _))) fun heq => ?_⟩
    -- The entry above the new cell is not the new top letter, by the horizontal strip property.
    have := lt_of_getElem?_getD_snd_eq_some ws w.1 w.2 h
      (List.getElem?_eq_some_iff.mpr ⟨hlen, heq⟩)
    rw [length_getD_robinsonSchenstedKnuth_fst, hi] at this
    exact lt_irrefl _ (hi ▸ this)

/-- The last top letter of a two-line array is the entry recorded at the end of the row of the
last new cell, and no higher row of the recording tableau ends in it. -/
private theorem getLast?_getD_robinsonSchenstedKnuth_snd (ws : List (α × β)) (a : α) (b : β)
    (h : ((ws ++ [(a, b)]).map toLex).SortedLE) :
    ((robinsonSchenstedKnuth (ws ++ [(a, b)])).2.getD
        (rowInsertIndex b (robinsonSchenstedKnuth ws).1) []).getLast? = some a ∧
      ∀ i < rowInsertIndex b (robinsonSchenstedKnuth ws).1,
        ((robinsonSchenstedKnuth (ws ++ [(a, b)])).2.getD i []).getLast? ≠ some a := by
  have hk := rowInsertIndex_le_length_snd ws b
  simp only [robinsonSchenstedKnuth_append_singleton, getD_appendToRow _ hk, ite_true]
  refine ⟨by simp, fun i hi hlast => ?_⟩
  simp only [hi.ne, ite_false] at hlast
  obtain ⟨ys, hys⟩ := getLast?_eq_some_iff.mp hlast
  -- That row ends in `a` at column `ys.length`, which is left of the new cell, yet the row is at
  -- least as long as the row above the new cell, which is longer than the new cell's column.
  have hcol := lt_of_getElem?_getD_snd_eq_some ws a b h (i := i) (j := ys.length)
    (by rw [hys]; simp)
  have hP := isTableauRows_robinsonSchenstedKnuth_fst ws
  obtain ⟨m, hm⟩ : ∃ m, rowInsertIndex b (robinsonSchenstedKnuth ws).1 = m + 1 :=
    Nat.exists_eq_add_of_lt (Nat.zero_le _ |>.trans_lt hi) |>.imp fun _ h => by omega
  have hlen := length_getD_succ_lt_of_rowInsertIndex_eq_succ hP hm
  have hanti' : Antitone fun n => ((robinsonSchenstedKnuth ws).1.getD n []).length :=
    antitone_nat_of_succ_le hP.length_getD_succ_le
  have hanti := hanti' (show i ≤ m by omega)
  dsimp only at hanti
  rw [length_getD_robinsonSchenstedKnuth_fst ws i] at hanti
  rw [hys] at hanti
  simp only [length_append, length_singleton] at hanti
  rw [← hm] at hlen
  omega

/-- **The Robinson--Schensted--Knuth correspondence is injective on two-line arrays**: a
two-line array is determined by its insertion and recording tableaux. -/
theorem robinsonSchenstedKnuth_injOn :
    Set.InjOn (robinsonSchenstedKnuth (α := α) (β := β)) {ws | (ws.map toLex).SortedLE} := by
  intro ws hws vs hvs h
  have hlen (us : List (α × β)) : (robinsonSchenstedKnuth us).2.flatten.length = us.length := by
    simpa using (flatten_robinsonSchenstedKnuth_snd_perm us).length_eq
  induction ws using reverseRecOn generalizing vs with
  | nil =>
    have := hlen vs
    rw [← h] at this
    simpa using this.symm
  | append_singleton ws w ih =>
    obtain rfl | ⟨vs, v, rfl⟩ := vs.eq_nil_or_concat'
    · have := hlen (ws ++ [w])
      rw [h] at this
      simp at this
    have hw := hws
    have hv := hvs
    simp only [Set.mem_ofPred_eq] at hw hv
    obtain ⟨a, b⟩ := w
    obtain ⟨a', b'⟩ := v
    obtain ⟨hlastw, hminw⟩ := getLast?_getD_robinsonSchenstedKnuth_snd ws a b hw
    obtain ⟨hlastv, hminv⟩ := getLast?_getD_robinsonSchenstedKnuth_snd vs a' b' hv
    -- Both last top letters are the largest entry of the common recording tableau.
    have hmax {us : List (α × β)} {u : α × β} (hu : ((us ++ [u]).map toLex).SortedLE) {x : α}
        (hx : x ∈ (robinsonSchenstedKnuth (us ++ [u])).2.flatten) : x ≤ u.1 := by
      obtain ⟨v, hv, rfl⟩ := mem_map.mp ((flatten_robinsonSchenstedKnuth_snd_perm _).subset hx)
      rcases mem_append.mp hv with hv | hv
      · exact Prod.Lex.monotone_fst _ _ (toLex_le_of_mem hu hv)
      · simp [mem_singleton.mp hv]
    have hmem {x : α} {rows : List (List α)} {i : ℕ}
        (hrow : (rows.getD i []).getLast? = some x) : x ∈ rows.flatten :=
      mem_flatten_of_mem_getD (mem_of_getLast? hrow)
    have haa' : a = a' := le_antisymm (hmax hv (h ▸ hmem hlastw))
      (hmax hw (h ▸ hmem hlastv))
    subst haa'
    -- The rows of the two last new cells agree: each is the highest row ending in `a`.
    have hk : rowInsertIndex b (robinsonSchenstedKnuth ws).1 =
        rowInsertIndex b' (robinsonSchenstedKnuth vs).1 := by
      rcases lt_trichotomy (rowInsertIndex b (robinsonSchenstedKnuth ws).1)
        (rowInsertIndex b' (robinsonSchenstedKnuth vs).1) with hlt | heq | hgt
      · exact absurd (h ▸ hlastw) (hminv _ hlt)
      · exact heq
      · exact absurd (h ▸ hlastv) (hminw _ hgt)
    simp only [robinsonSchenstedKnuth_append_singleton, Prod.mk.injEq] at h
    obtain ⟨hins, hrec⟩ := h
    -- A single row insertion is injective, so the last bottom letters and earlier tableaux agree.
    have := rowInsertEquiv.injective
      (a₁ := (⟨_, isTableauRows_robinsonSchenstedKnuth_fst ws⟩, b))
      (a₂ := (⟨_, isTableauRows_robinsonSchenstedKnuth_fst vs⟩, b'))
      (Subtype.ext (by simp [hins, hk]))
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at this
    obtain ⟨hP, rfl⟩ := this
    have hQ : (robinsonSchenstedKnuth ws).2 = (robinsonSchenstedKnuth vs).2 := by
      have hws' := (sortedLE_map_toLex_append_singleton.mp hw).1
      have hvs' := (sortedLE_map_toLex_append_singleton.mp hv).1
      rw [← dropLastOfRow_appendToRow a
          (isTableauRows_robinsonSchenstedKnuth_snd hws').nil_notMem
          (rowInsertIndex_le_length_snd ws b), hrec, ← hk,
        dropLastOfRow_appendToRow a (isTableauRows_robinsonSchenstedKnuth_snd hvs').nil_notMem
          (hk ▸ rowInsertIndex_le_length_snd vs b)]
    rw [ih (sortedLE_map_toLex_append_singleton.mp hw).1
      (sortedLE_map_toLex_append_singleton.mp hv).1 (Prod.ext hP hQ)]

/-- In a nonempty tableau whose largest entry is `a`, the highest row ending in `a` ends in a
corner: the row below it is strictly shorter. -/
private theorem length_getD_succ_lt_of_getLast?_eq_some {rows : List (List α)}
    (h : rows.IsTableauRows) {a : α} (hmax : ∀ x ∈ rows.flatten, x ≤ a) {k : ℕ}
    (hk : (rows.getD k []).getLast? = some a) :
    (rows.getD (k + 1) []).length < (rows.getD k []).length := by
  obtain ⟨ys, hys⟩ := getLast?_eq_some_iff.mp hk
  by_contra hcon
  have hlen : ys.length < (rows.getD (k + 1) []).length := by
    rw [hys, length_append, length_singleton] at hcon
    omega
  have hlt := (h.isRowAbove_getD k).getElem_lt ys.length (by rw [hys]; simp) hlen
  have hx := hmax _ (mem_flatten_of_mem_getD (getElem_mem hlen))
  simp only [hys, getElem_append_right le_rfl, Nat.sub_self, getElem_singleton] at hlt
  exact absurd (hlt.trans_le hx) (lt_irrefl a)

/-- In a tableau, the largest entry ends some row. -/
private theorem exists_getLast?_getD_eq_some {rows : List (List α)} (h : rows.IsTableauRows)
    {a : α} (ha : a ∈ rows.flatten) (hmax : ∀ x ∈ rows.flatten, x ≤ a) :
    ∃ i, (rows.getD i []).getLast? = some a := by
  obtain ⟨row, hrow, har⟩ := mem_flatten.mp ha
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem hrow
  refine ⟨i, ?_⟩
  rw [getD_eq_getElem?_getD, getElem?_eq_getElem hi, Option.getD_some]
  obtain hnil | ⟨ys, z, hyz⟩ := rows[i].eq_nil_or_concat'
  · simp [hnil] at har
  -- The last entry `z` of the row is at least every entry of the row, `a` among them.
  have hle : ∀ x ∈ ys, x ≤ z := by
    have hs := h.sortedLE _ (getElem_mem hi)
    rw [hyz, sortedLE_append] at hs
    exact fun x hx => hs.2.2 x hx z mem_cons_self
  have hza : z = a := le_antisymm (hmax z (mem_flatten.mpr ⟨_, getElem_mem hi, by simp [hyz]⟩)) (by
    rw [hyz, mem_append, mem_singleton] at har
    rcases har with har | rfl
    · exact hle a har
    · exact le_rfl)
  simp [hyz, hza]

/-- **Recovering the order of a two-line array**: appending `(a, b)` to a two-line array gives a
two-line array if `a` is at least every top letter so far, and no row of the recording tableau
above the row of the cell added by inserting `b` ends in `a`. -/
private theorem sortedLE_map_toLex_append_singleton_of_forall {ws : List (α × β)}
    (hws : (ws.map toLex).SortedLE) {a : α} {b : β}
    (hmax : ∀ x ∈ (robinsonSchenstedKnuth ws).2.flatten, x ≤ a)
    (hrow : ∀ i < rowInsertIndex b (robinsonSchenstedKnuth ws).1,
      ((robinsonSchenstedKnuth ws).2.getD i []).getLast? ≠ some a) :
    ((ws ++ [(a, b)]).map toLex).SortedLE := by
  rw [sortedLE_map_toLex_append_singleton]
  refine ⟨hws, fun v hv => ?_⟩
  obtain ⟨vs, rfl⟩ := getLast?_eq_some_iff.mp hv
  obtain ⟨a', b'⟩ := v
  obtain ⟨hlast, -⟩ := getLast?_getD_robinsonSchenstedKnuth_snd vs a' b' hws
  -- The previous top letter `a'` is an entry of the recording tableau, so it is at most `a`.
  rcases (hmax a' (mem_flatten_of_mem_getD (mem_of_getLast? hlast))).lt_or_eq with hlt | rfl
  · exact Prod.Lex.toLex_le_toLex.mpr (Or.inl hlt)
  refine Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, ?_⟩)
  -- If `a' = a`, the previous new cell lies weakly below the new one, so `b' ≤ b` by the
  -- bumping lemma.
  refine (rowInsertIndex_le_iff (isTableauRows_robinsonSchenstedKnuth_fst vs).sortedLE b' b).mp ?_
  have hP : (robinsonSchenstedKnuth (vs ++ [(a', b')])).1 =
      rowInsert b' (robinsonSchenstedKnuth vs).1 := by simp
  rw [← hP]
  exact not_lt.mp fun hlt => hrow _ hlt hlast

/-- **The image of the Robinson--Schensted--Knuth correspondence**: a pair of lists of rows is the
pair of insertion and recording tableaux of some two-line array exactly when both are tableaux of
the same shape. -/
theorem exists_robinsonSchenstedKnuth_eq_iff {p : List (List β) × List (List α)} :
    (∃ ws : List (α × β), (ws.map toLex).SortedLE ∧ robinsonSchenstedKnuth ws = p) ↔
      p.1.IsTableauRows ∧ p.2.IsTableauRows ∧
        ∀ i, (p.1.getD i []).length = (p.2.getD i []).length := by
  constructor
  · rintro ⟨ws, hws, rfl⟩
    exact ⟨isTableauRows_robinsonSchenstedKnuth_fst ws,
      isTableauRows_robinsonSchenstedKnuth_snd hws, length_getD_robinsonSchenstedKnuth_fst ws⟩
  obtain ⟨P, Q⟩ := p
  rintro ⟨hP, hQ, hshape⟩
  obtain ⟨n, hn⟩ : ∃ n, Q.flatten.length = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing P Q with
  | _ n ih =>
  dsimp only at hP hQ hshape ⊢
  by_cases hQnil : Q = []
  · subst hQnil
    obtain rfl : P = [] := by
      cases P with
      | nil => rfl
      | cons row rows =>
        have := hshape 0
        simp only [getD_cons_zero, getD_nil, length_nil, length_eq_zero_iff] at this
        exact absurd this (isTableauRows_cons.mp hP).1
    exact ⟨[], by simpa using sortedLE_nil (α := α ×ₗ β), rfl⟩
  -- The largest entry `a` of `Q` ends some row; the highest such row `k` ends in a corner.
  have hflat : Q.flatten ≠ [] := by
    obtain ⟨row, rows, rfl⟩ := exists_cons_of_ne_nil hQnil
    simp [(isTableauRows_cons.mp hQ).1]
  obtain ⟨a, ha, hmax⟩ : ∃ a ∈ Q.flatten, ∀ x ∈ Q.flatten, x ≤ a := by
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (mt (argmax_eq_none (f := id)).mp hflat)
    exact ⟨a, argmax_mem ha, fun x hx => le_of_mem_argmax (f := id) hx ha⟩
  have hex := exists_getLast?_getD_eq_some hQ ha hmax
  classical
  have hk : (Q.getD (Nat.find hex) []).getLast? = some a := Nat.find_spec hex
  have hcornerQ := length_getD_succ_lt_of_getLast?_eq_some hQ hmax hk
  have hcornerP : (P.getD (Nat.find hex + 1) []).length < (P.getD (Nat.find hex) []).length := by
    rw [hshape, hshape]
    exact hcornerQ
  -- Undo the last step: reverse insertion in `P`, and removal of the last `a` from row `k` of `Q`.
  obtain ⟨b, -, hins, hidx⟩ := rowInsert_reverseRowInsert hP hcornerP
  have hQeq := appendToRow_dropLastOfRow hQ hcornerQ hk
  have hgetQ' := getD_dropLastOfRow hQ hcornerQ
  have hshape' (i : ℕ) : ((reverseRowInsert (Nat.find hex) P).1.getD i []).length =
      ((dropLastOfRow (Nat.find hex) Q).getD i []).length := by
    have h1 := length_getD_rowInsert b (reverseRowInsert (Nat.find hex) P).1 i
    rw [hins, hidx, hshape] at h1
    rw [hgetQ' i]
    split_ifs at h1 ⊢ with hik
    · subst hik
      rw [length_dropLast]
      omega
    · omega
  have hperm := flatten_appendToRow_perm a (Nat.find hex) (dropLastOfRow (Nat.find hex) Q)
  rw [hQeq] at hperm
  have hlen' : (dropLastOfRow (Nat.find hex) Q).flatten.length < n := by
    rw [← hn, hperm.length_eq, length_append, length_singleton]
    omega
  obtain ⟨ws, hws, hrsk⟩ := ih _ hlen' _ _ (hP.reverseRowInsert hcornerP)
    (hQ.dropLastOfRow hcornerQ) hshape' rfl
  refine ⟨ws ++ [(a, b)], sortedLE_map_toLex_append_singleton_of_forall hws
    (fun x hx => hmax x (hperm.symm.subset (mem_append_left [a] (by rwa [hrsk] at hx))))
    fun i hi => ?_, ?_⟩
  · -- The rows above row `k` are unchanged, and none of them ends in `a` by the choice of `k`.
    rw [hrsk] at hi ⊢
    rw [hidx] at hi
    simp only [hgetQ' i, hi.ne, ite_false]
    exact Nat.find_min hex hi
  · rw [robinsonSchenstedKnuth_append_singleton, hrsk]
    simp only
    rw [hidx, hins, hQeq]

/-- **The Robinson--Schensted--Knuth correspondence**: inserting the bottom letters of a two-line
array into the empty tableau and recording the top letters in the rows of the new cells is a
bijection from two-line arrays onto the pairs of tableaux of the same shape. -/
noncomputable def robinsonSchenstedKnuthEquiv :
    {ws : List (α × β) // (ws.map toLex).SortedLE} ≃
      {p : List (List β) × List (List α) // p.1.IsTableauRows ∧ p.2.IsTableauRows ∧
        ∀ i, (p.1.getD i []).length = (p.2.getD i []).length} :=
  Equiv.ofBijective
    (fun ws => ⟨robinsonSchenstedKnuth ws.1,
      exists_robinsonSchenstedKnuth_eq_iff.mp ⟨ws.1, ws.2, rfl⟩⟩)
    ⟨fun ws vs h => Subtype.ext (robinsonSchenstedKnuth_injOn ws.2 vs.2 (congrArg Subtype.val h)),
      fun p => (exists_robinsonSchenstedKnuth_eq_iff.mpr p.2).elim fun ws hws =>
        ⟨⟨ws, hws.1⟩, Subtype.ext hws.2⟩⟩

/-- `robinsonSchenstedKnuthEquiv` sends a two-line array to its insertion and recording
tableaux. -/
@[simp]
theorem robinsonSchenstedKnuthEquiv_apply_coe
    (ws : {ws : List (α × β) // (ws.map toLex).SortedLE}) :
    (robinsonSchenstedKnuthEquiv ws : List (List β) × List (List α)) =
      robinsonSchenstedKnuth ws.1 := (rfl)

end Correspondence

end TauCeti
