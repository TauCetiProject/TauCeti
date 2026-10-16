/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.StandardTableau.Basic
public import TauCeti.Combinatorics.Young.Schensted.Basic
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
@[simp]
theorem getElem?_getD_getElem?_toRows (T : StandardYoungTableau μ) (c : ↥μ.cells) :
    (T.toRows[c.1.1]?.getD [])[c.1.2]? = some (T c) := by
  have hi : c.1.1 < T.toRows.length := by simpa using μ.lt_colLen_zero_of_mem c.2
  have hj : c.1.2 < μ.rowLen c.1.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.2
  rw [getElem?_eq_getElem hi]
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
    have hj : c.1.2 < μ.rowLen c.1.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.2
    simp only [toRows, mem_flatten, mem_ofFn]
    refine ⟨_, ⟨⟨c.1.1, μ.lt_colLen_zero_of_mem c.2⟩, rfl⟩, ?_⟩
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
  have heq := congrArg (fun rows => (rows[c.1.1]?.getD [])[c.1.2]?) h
  simpa only [getElem?_getD_getElem?_toRows T c, getElem?_getD_getElem?_toRows U c,
    Option.some.injEq] using heq

/-! ### Decoding a list of rows -/

section ofRows

variable {rows : List (List (Fin μ.card))}

/-- A list of rows of shape `μ` has a row for the row of every cell of `μ`. -/
private theorem lt_length_of_mem (hshape : rows.map length = μ.rowLens) {i j : ℕ}
    (h : (i, j) ∈ μ) : i < rows.length := by
  simpa [← length_map (f := length), hshape] using μ.lt_colLen_zero_of_mem h

/-- In a list of rows of shape `μ`, each row has the length of the corresponding row of `μ`. -/
private theorem length_getElem_of_map_length (hshape : rows.map length = μ.rowLens) {i : ℕ}
    (hi : i < rows.length) : rows[i].length = μ.rowLen i := by
  rw [← YoungDiagram.getD_rowLens, ← hshape, getD_eq_getElem _ _ (by simpa using hi),
    getElem_map]

/-- In a list of rows of shape `μ`, the row of a cell of `μ` is long enough to hold it. -/
private theorem lt_length_getElem_of_mem (hshape : rows.map length = μ.rowLens) {i j : ℕ}
    (h : (i, j) ∈ μ) : j < (rows[i]'(lt_length_of_mem hshape h)).length := by
  rw [length_getElem_of_map_length hshape]
  exact YoungDiagram.mem_iff_lt_rowLen.mp h

/-- The cell labeling read off a list of rows of shape `μ`. -/
private def ofRowsFun (hshape : rows.map length = μ.rowLens) (c : ↥μ.cells) : Fin μ.card :=
  (rows[c.1.1]'(lt_length_of_mem hshape c.2))[c.1.2]'(lt_length_getElem_of_mem hshape c.2)

/-- Full content makes the cell labeling surjective. -/
private theorem ofRowsFun_surjective (hshape : rows.map length = μ.rowLens)
    (hcontent : rows.flatten.Perm (finRange μ.card)) : Function.Surjective (ofRowsFun hshape) := by
  intro x
  obtain ⟨row, hr, hx⟩ := mem_flatten.mp (hcontent.symm.subset (mem_finRange x))
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem hr
  obtain ⟨j, hj, rfl⟩ := getElem_of_mem hx
  rw [length_getElem_of_map_length hshape hi] at hj
  exact ⟨⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr hj⟩, rfl⟩

/-- The content condition excludes repeated labels, strengthening weak row order. -/
private theorem ofRowsFun_row_strict (htab : rows.IsTableauRows)
    (hshape : rows.map length = μ.rowLens) (hcontent : rows.flatten.Perm (finRange μ.card))
    {i j k : ℕ} (hjk : j < k) (hcell : (i, k) ∈ μ) :
    ofRowsFun hshape ⟨(i, j), μ.up_left_mem le_rfl hjk.le hcell⟩ <
      ofRowsFun hshape ⟨(i, k), hcell⟩ := by
  have hi := lt_length_of_mem hshape hcell
  have hsorted := (htab.sortedLE _ (getElem_mem hi)).sortedLT_of_nodup
    ((nodup_flatten.mp (hcontent.nodup_iff.mpr (nodup_finRange _))).1 _ (getElem_mem hi))
  exact hsorted.strictMono_get
    (a := ⟨j, hjk.trans (lt_length_getElem_of_mem hshape hcell)⟩)
    (b := ⟨k, lt_length_getElem_of_mem hshape hcell⟩) hjk

/-- Transitivity of `IsRowAbove` compares any two rows, not just adjacent rows. -/
private theorem ofRowsFun_col_strict (htab : rows.IsTableauRows)
    (hshape : rows.map length = μ.rowLens) {i k j : ℕ} (hik : i < k) (hcell : (k, j) ∈ μ) :
    ofRowsFun hshape ⟨(i, j), μ.up_left_mem hik.le le_rfl hcell⟩ <
      ofRowsFun hshape ⟨(k, j), hcell⟩ := by
  have hk := lt_length_of_mem hshape hcell
  have hj := lt_length_getElem_of_mem hshape hcell
  have habove := (pairwise_iff_getElem.mp htab.isChain.pairwise) i k (hik.trans hk) hk hik
  exact habove.getElem_lt j (hj.trans_le habove.length_le) hj

/-- The standard tableau whose rows are a semistandard list of rows of shape `μ` containing
every label exactly once. -/
private noncomputable def ofRows (htab : rows.IsTableauRows)
    (hshape : rows.map length = μ.rowLens) (hcontent : rows.flatten.Perm (finRange μ.card)) :
    StandardYoungTableau μ where
  toTableau := Equiv.ofBijective (ofRowsFun hshape)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨ofRowsFun_surjective hshape hcontent, by simp⟩)
  row_strict' := ofRowsFun_row_strict htab hshape hcontent
  col_strict' := ofRowsFun_col_strict htab hshape

/-- Enumerating the decoded cells recovers each original row entry. -/
private theorem toRows_ofRows (htab : rows.IsTableauRows)
    (hshape : rows.map length = μ.rowLens) (hcontent : rows.flatten.Perm (finRange μ.card)) :
    (ofRows htab hshape hcontent).toRows = rows := by
  have hlen : rows.length = μ.colLen 0 := by simpa using congrArg length hshape
  refine ext_getElem (by simp [hlen]) fun i hi hi' => ?_
  rw [getElem_toRows]
  exact ext_getElem (by simp [length_getElem_of_map_length hshape hi']) fun j _ _ => by
    rw [List.getElem_ofFn]
    rfl

end ofRows

/-- A list of rows comes from a standard tableau exactly when it is a semistandard tableau
of the given shape containing each label exactly once. -/
theorem exists_toRows_eq_iff {rows : List (List (Fin μ.card))} :
    (∃ T : StandardYoungTableau μ, T.toRows = rows) ↔
      rows.IsTableauRows ∧ rows.map length = μ.rowLens ∧
        rows.flatten.Perm (finRange μ.card) := by
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨T.isTableauRows_toRows, T.map_length_toRows, T.flatten_toRows_perm⟩
  · rintro ⟨htab, hshape, hcontent⟩
    exact ⟨ofRows htab hshape hcontent, toRows_ofRows htab hshape hcontent⟩

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

/-- The tableau decoded from a valid row list labels each cell by the entry in its row and
column. -/
@[simp]
theorem rowsEquiv_symm_apply (rows : {rows : List (List (Fin μ.card)) //
    rows.IsTableauRows ∧ rows.map length = μ.rowLens ∧
      rows.flatten.Perm (finRange μ.card)}) (c : ↥μ.cells) :
    (rowsEquiv μ).symm rows c = (rows.val[c.1.1]'(by
      simpa [← length_map (f := length), rows.2.2.1] using μ.lt_colLen_zero_of_mem c.2))[c.1.2]'(by
      rw [← getElem_map length, getElem_of_eq rows.2.2.1, YoungDiagram.get_rowLens]
      · exact YoungDiagram.mem_iff_lt_rowLen.mp c.2
      · simpa [rows.2.2.1] using μ.lt_colLen_zero_of_mem c.2) := by
  have key (rs : List (List (Fin μ.card))) (h : ((rowsEquiv μ).symm rows).toRows = rs) h₁ h₂ :
      (rowsEquiv μ).symm rows c = (rs[c.1.1]'h₁)[c.1.2]'h₂ := by
    subst h
    simp only [getElem_toRows, List.getElem_ofFn]
  exact key _ (toRows_rowsEquiv_symm rows) _ _

end TauCeti.StandardYoungTableau
