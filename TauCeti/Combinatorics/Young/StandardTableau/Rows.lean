/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.StandardTableau.Basic
public import TauCeti.Combinatorics.Young.Schensted
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn

/-!
# Standard tableaux as lists of rows

`StandardYoungTableau.toRows` lists the entries of a standard tableau from left to right in each
row, with the rows ordered from top to bottom. These rows satisfy `List.IsTableauRows`, have the
prescribed shape, and contain every label exactly once. Conversely, these three properties
characterize the lists arising from standard tableaux, giving `StandardYoungTableau.rowsEquiv`.

This connects bijective cell labelings with the list representation used by Schensted insertion.
In particular, an insertion tableau containing each label once can be read as a standard tableau
without changing its entries or its shape. Empty shapes are included.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Sections 1.1 and 4.1.
* B. E. Sagan, *The Symmetric Group*, second edition, Springer GTM 203 (2001), Section 3.1.
-/

public section

namespace TauCeti.StandardYoungTableau

open List

variable {μ : YoungDiagram}

/-- The rows of a standard tableau, listed from top to bottom and left to right. -/
def toRows (T : StandardYoungTableau μ) : List (List (Fin μ.card)) :=
  ofFn fun i : Fin (μ.colLen 0) => ofFn fun j : Fin (μ.rowLen i) =>
    T ⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩

/-- The row representation enumerates each row in increasing column order. -/
theorem toRows_def (T : StandardYoungTableau μ) :
    T.toRows = ofFn fun i : Fin (μ.colLen 0) => ofFn fun j : Fin (μ.rowLen i) =>
      T ⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩ := (rfl)

/-- The number of rows is the height of the first column. -/
@[simp]
theorem length_toRows (T : StandardYoungTableau μ) : T.toRows.length = μ.colLen 0 := by
  simp [toRows]

/-- The row lengths of a standard tableau agree with its shape. -/
@[simp]
theorem map_length_toRows (T : StandardYoungTableau μ) : T.toRows.map length = μ.rowLens := by
  simp [toRows, YoungDiagram.rowLens, ← ofFn_getElem_eq_map]

/-- Reading a row in its natural column order recovers its entries. -/
@[simp]
theorem getElem_toRows (T : StandardYoungTableau μ) (i : ℕ) (hi : i < T.toRows.length) :
    T.toRows[i] = ofFn fun j : Fin (μ.rowLen i) =>
      T ⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩ := by
  simp [toRows]

/-- Reading a row beyond the shape gives length zero; otherwise it has the shape's row length. -/
@[simp]
theorem length_getD_getElem?_toRows (T : StandardYoungTableau μ) (i : ℕ) :
    (T.toRows[i]?.getD []).length = μ.rowLen i := by
  rw [← getD_eq_getElem?_getD, ← getD_map T.toRows [] length, map_length_toRows]
  exact YoungDiagram.getD_rowLens μ i

/-- Looking up the coordinates of a cell in the row representation recovers its label. -/
theorem getElem?_getD_toRows (T : StandardYoungTableau μ) (c : ↥μ.cells) :
    (T.toRows.getD c.1.1 [])[c.1.2]? = some (T c) := by
  have hi : c.1.1 < T.toRows.length := by
    simpa using YoungDiagram.mem_iff_lt_colLen.mp
      (μ.up_left_mem le_rfl (Nat.zero_le _) c.2)
  have hj : c.1.2 < μ.rowLen c.1.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.2
  rw [getD_eq_getElem T.toRows [] hi]
  simp [hj]

/-- A standard tableau's row representation is a semistandard tableau. -/
theorem isTableauRows_toRows (T : StandardYoungTableau μ) : T.toRows.IsTableauRows := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [toRows, mem_ofFn]
    rintro ⟨i, hi⟩
    have hpos : 0 < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp
      (YoungDiagram.mem_iff_lt_colLen.mpr i.isLt)
    have := congrArg length hi
    simp only [length_ofFn, length_nil] at this
    omega
  · simp only [toRows, forall_mem_ofFn_iff]
    intro i
    apply sortedLE_iff_pairwise.mpr
    apply pairwise_ofFn.mpr
    intro j k hjk
    exact (T.row_strict (Fin.lt_def.mp hjk)
      (YoungDiagram.mem_iff_lt_rowLen.mpr k.isLt)).le
  · apply Pairwise.isChain
    simp only [toRows, pairwise_ofFn]
    intro i k hik
    refine ⟨by simpa using μ.rowLen_anti i k (Fin.le_def.mp hik.le), ?_⟩
    intro j hu hl
    simp only [length_ofFn] at hu hl
    simpa using T.col_strict (Fin.lt_def.mp hik) (YoungDiagram.mem_iff_lt_rowLen.mpr hl)

/-- The rows contain each label exactly once. -/
theorem flatten_toRows_perm (T : StandardYoungTableau μ) :
    T.toRows.flatten.Perm (finRange μ.card) := by
  have hmem (x : Fin μ.card) : x ∈ T.toRows.flatten := by
    obtain ⟨c, rfl⟩ := T.surjective x
    have hi : c.1.1 < μ.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp
      (μ.up_left_mem le_rfl (Nat.zero_le _) c.2)
    have hj : c.1.2 < μ.rowLen c.1.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.2
    simp only [toRows, mem_flatten, mem_ofFn]
    refine ⟨_, ⟨⟨c.1.1, hi⟩, rfl⟩, ?_⟩
    exact mem_ofFn.mpr ⟨⟨c.1.2, hj⟩, rfl⟩
  have hlen : T.toRows.flatten.length = μ.card := by
    rw [length_flatten, map_length_toRows, YoungDiagram.sum_rowLens_eq_card]
  exact ((subperm_of_subset (nodup_finRange μ.card) (fun x _ => hmem x)).perm_of_length_le
    (by simp [hlen])).symm

/-- The row representation determines a standard tableau. -/
theorem toRows_injective : Function.Injective (toRows (μ := μ)) := by
  intro T U h
  apply ext
  intro c
  have heq := congrArg (fun rows => (rows.getD c.1.1 [])[c.1.2]?) h
  simpa only [getElem?_getD_toRows T c, getElem?_getD_toRows U c, Option.some.injEq] using heq

/-- A list of rows comes from a standard tableau exactly when it is a semistandard tableau
of the given shape containing each label exactly once. -/
theorem exists_toRows_eq_iff {rows : List (List (Fin μ.card))} :
    (∃ T : StandardYoungTableau μ, T.toRows = rows) ↔
      rows.IsTableauRows ∧ rows.map length = μ.rowLens ∧
        rows.flatten.Perm (finRange μ.card) := by
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨T.isTableauRows_toRows, T.map_length_toRows, T.flatten_toRows_perm⟩
  rintro ⟨htab, hshape, hcontent⟩
  have hlen : rows.length = μ.colLen 0 := by
    simpa using congrArg length hshape
  have hrow (i : ℕ) : (rows.getD i []).length = μ.rowLen i := by
    rw [← getD_map rows [] length, hshape]
    exact YoungDiagram.getD_rowLens μ i
  let f (c : ↥μ.cells) : Fin μ.card :=
    (rows.getD c.1.1 [])[c.1.2]'(by
      rw [hrow]
      exact YoungDiagram.mem_iff_lt_rowLen.mp c.2)
  -- Full content makes the cell labeling surjective; equal cardinalities make it bijective.
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨row, hr, hx⟩ := mem_flatten.mp (hcontent.symm.subset (mem_finRange x))
    obtain ⟨i, hi, rfl⟩ := getElem_of_mem hr
    obtain ⟨j, hj, rfl⟩ := getElem_of_mem hx
    have hcell : (i, j) ∈ μ := by
      apply YoungDiagram.mem_iff_lt_rowLen.mpr
      rw [← hrow, getD_eq_getElem rows [] hi]
      exact hj
    refine ⟨⟨(i, j), hcell⟩, ?_⟩
    simp [f, hi]
  let T : StandardYoungTableau μ :=
    { toTableau := Equiv.ofBijective f
        ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj, by simp⟩)
      -- The content condition excludes repeated labels, strengthening weak row order.
      row_strict' := fun {i j k} hjk hcell => by
        have hi : i < rows.length := by
          rw [hlen]
          exact YoungDiagram.mem_iff_lt_colLen.mp
            (μ.up_left_mem le_rfl (Nat.zero_le _) hcell)
        have hsorted := (htab.sortedLE _ (getElem_mem hi)).sortedLT_of_nodup
          ((nodup_flatten.mp (hcontent.nodup_iff.mpr (nodup_finRange _))).1 _ (getElem_mem hi))
        simpa [f, hi] using
          hsorted.strictMono_get (a := ⟨j, by
            rw [← getD_eq_getElem rows [] hi, hrow]
            exact hjk.trans (YoungDiagram.mem_iff_lt_rowLen.mp hcell)⟩)
            (b := ⟨k, by
              rw [← getD_eq_getElem rows [] hi, hrow]
              exact YoungDiagram.mem_iff_lt_rowLen.mp hcell⟩) hjk
      -- Transitivity of `IsRowAbove` compares any two rows, not just adjacent rows.
      col_strict' := fun {i k j} hik hcell => by
        have hk : k < rows.length := by
          rw [hlen]
          exact YoungDiagram.mem_iff_lt_colLen.mp
            (μ.up_left_mem le_rfl (Nat.zero_le _) hcell)
        have habove := (pairwise_iff_getElem.mp htab.isChain.pairwise) i k
          (hik.trans hk) hk hik
        have hj : j < (rows.getD k []).length := by
          rw [hrow]
          exact YoungDiagram.mem_iff_lt_rowLen.mp hcell
        rw [getD_eq_getElem rows [] hk] at hj
        simpa [f, hk, hik.trans hk] using habove.getElem_lt j
            (hj.trans_le habove.length_le) hj }
  -- Enumerating the decoded cells recovers each original row entry.
  refine ⟨T, ext_getElem (by simp [hlen]) fun i hi hi' => ?_⟩
  rw [getElem_toRows]
  apply ext_getElem
  · simp only [length_ofFn]
    rw [← hrow, getD_eq_getElem rows [] hi']
  · intro j hj hj'
    simp only [List.getElem_ofFn]
    rw [← toTableau_apply]
    simp [T, f, hi']

/-- Standard tableaux of shape `μ` correspond to semistandard lists of rows of that shape
containing every label exactly once. -/
noncomputable def rowsEquiv (μ : YoungDiagram) :
    StandardYoungTableau μ ≃ {rows : List (List (Fin μ.card)) //
      rows.IsTableauRows ∧ rows.map length = μ.rowLens ∧
        rows.flatten.Perm (finRange μ.card)} :=
  Equiv.ofBijective
    (fun T => ⟨T.toRows, exists_toRows_eq_iff.mp ⟨T, rfl⟩⟩)
    ⟨fun _ _ h => toRows_injective (congrArg Subtype.val h), fun rows =>
      (exists_toRows_eq_iff.mpr rows.2).imp fun _ h => Subtype.ext h⟩

/-- The forward row equivalence lists the entries of the tableau by rows. -/
@[simp]
theorem rowsEquiv_apply_coe (T : StandardYoungTableau μ) :
    (rowsEquiv μ T : List (List (Fin μ.card))) = T.toRows := (rfl)

/-- Decoding a valid row list and reading it back recovers that list. -/
@[simp]
theorem toRows_rowsEquiv_symm (rows : {rows : List (List (Fin μ.card)) //
    rows.IsTableauRows ∧ rows.map length = μ.rowLens ∧
      rows.flatten.Perm (finRange μ.card)}) :
    ((rowsEquiv μ).symm rows).toRows = rows.val :=
  congrArg Subtype.val ((rowsEquiv μ).apply_symm_apply rows)

end TauCeti.StandardYoungTableau
