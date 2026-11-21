/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.StandardTableau.Basic
import TauCeti.Combinatorics.Young.HookLength.Basic
import TauCeti.Combinatorics.Young.StandardTableau.Order
import TauCeti.GroupTheory.Perm.Fin

/-!
# Contents of labels in standard Young tableaux

The content of a label `k` in a tableau `t` is `YoungTableau.labelContent t k`, the column minus the
row of the cell carrying `k`. This file records the facts about the contents of the labels of a
standard Young tableau that govern Young's seminormal form, chiefly of the nearby labels `k`,
`k + 1` and `k + 2`: in that form
the simple transposition of `k` and `k + 1` acts through the *axial distance*
`labelContent T (k + 1) - labelContent T k`:

* the axial distance is the difference of the contents of the cells carrying `k + 1` and `k`
  (`TauCeti.YoungTableau.axialDistance_eq_of_apply_eq`);
* contents of labels differ by less than the number of cells
  (`TauCeti.YoungTableau.abs_labelContent_sub_lt_card`), and transposing negates axial distances
  (`TauCeti.YoungTableau.axialDistance_transpose`);
* the label `0` of a standard tableau has content `0`
  (`TauCeti.StandardYoungTableau.labelContent_zero`);
* two labels differing by at most two lie on different diagonals, so their contents differ
  (`TauCeti.StandardYoungTableau.labelContent_ne_of_lt_of_le_add_two`);
* the axial distance `YoungTableau.axialDistance` of the labels `k` and `k + 1` of a standard
  tableau is nonzero (`TauCeti.StandardYoungTableau.axialDistance_ne_zero`); it is `1` exactly
  when the two labels lie in one row, and `-1` exactly when they lie in one column
  (`TauCeti.StandardYoungTableau.axialDistance_eq_one_iff`,
  `TauCeti.StandardYoungTableau.axialDistance_eq_neg_one_iff`);
* exchanging the labels `k` and `k + 1` of a standard tableau gives a standard tableau as soon as
  the axial distance is not `1` or `-1`, that is, as soon as the two labels do not lie next to each
  other in one row or one column (`TauCeti.StandardYoungTableau.swap`); this changes the tableau
  (`TauCeti.StandardYoungTableau.swap_ne_self`) and negates the axial distance
  (`TauCeti.YoungTableau.axialDistance_relabel_swap`); otherwise the exchange is not standard
  (`TauCeti.StandardYoungTableau.exists_toTableau_eq_relabel_swap_iff`);
* a standard tableau is determined by the contents of all its labels
  (`TauCeti.StandardYoungTableau.labelContent_injective`), so the Jucys–Murphy eigenvalues of
  Young's seminormal basis vectors tell the tableaux apart.

## References

* A. Ram, *Seminormal representations of Weyl groups and Iwahori-Hecke algebras*, Proc. London
  Math. Soc. 75 (1997), 99–133.
-/

public section

namespace TauCeti

namespace YoungTableau

variable {μ : YoungDiagram}

/-- The *axial distance* `labelContent t (k + 1) - labelContent t k` of the labels `k` and
`k + 1` of a tableau `t`. -/
def axialDistance (t : YoungTableau μ) (k : ℕ) (hk : k + 1 < μ.card) : ℤ :=
  labelContent t ⟨k + 1, hk⟩ - labelContent t ⟨k, by omega⟩

theorem axialDistance_def (t : YoungTableau μ) (k : ℕ) (hk : k + 1 < μ.card) :
    axialDistance t k hk = labelContent t ⟨k + 1, hk⟩ - labelContent t ⟨k, by omega⟩ := by
  rw [axialDistance]

/-- The axial distance of the labels `k` and `k + 1` is the content of the cell carrying `k + 1`
minus the content of the cell carrying `k`. -/
theorem axialDistance_eq_of_apply_eq (t : YoungTableau μ) {k : ℕ} {hk : k + 1 < μ.card}
    {c d : ↥μ.cells} (hc : t c = ⟨k, by omega⟩) (hd : t d = ⟨k + 1, hk⟩) :
    axialDistance t k hk = YoungDiagram.cellContent d - YoungDiagram.cellContent c := by
  rw [axialDistance_def, ← hc, ← hd, labelContent_apply, labelContent_apply]

/-- Two labels of a tableau have contents differing by less than the number of cells. -/
theorem abs_labelContent_sub_lt_card (t : YoungTableau μ) (a b : Fin μ.card) :
    |labelContent t a - labelContent t b| < μ.card := by
  rw [labelContent_def, labelContent_def]
  exact YoungDiagram.abs_cellContent_sub_lt_card ((YoungDiagram.mem_cells _).mp (t.symm a).property)
    ((YoungDiagram.mem_cells _).mp (t.symm b).property)

/-- The axial distance of two labels is less than the number of cells in absolute value. -/
theorem abs_axialDistance_lt_card (t : YoungTableau μ) (k : ℕ) (hk : k + 1 < μ.card) :
    |axialDistance t k hk| < μ.card := by
  rw [axialDistance_def]
  exact abs_labelContent_sub_lt_card t _ _

/-- Transposing a tableau negates its axial distances. -/
@[simp]
theorem axialDistance_transpose (t : YoungTableau μ) (k : ℕ) (hk : k + 1 < μ.transpose.card) :
    axialDistance (transpose t) k hk = -axialDistance t k (by simpa using hk) := by
  simp only [axialDistance_def, labelContent_transpose, Fin.cast_mk]
  ring

/-- Exchanging the labels `k` and `k + 1` negates their axial distance. -/
@[simp]
theorem axialDistance_relabel_swap (t : YoungTableau μ) (k : ℕ) (hk : k + 1 < μ.card) :
    axialDistance (relabel (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) t) k hk =
      -axialDistance t k hk := by
  simp [axialDistance_def, Equiv.swap_inv]

end YoungTableau

namespace StandardYoungTableau

variable {μ : YoungDiagram} (T : StandardYoungTableau μ)

/-- The label `0` of a standard Young tableau has content `0`: it is carried by the cell
`(0, 0)`. -/
@[simp]
theorem labelContent_mk_zero (h : 0 < μ.card) :
    YoungTableau.labelContent T.toTableau ⟨0, h⟩ = 0 := by
  obtain ⟨⟨⟨i, j⟩, hc⟩, hcT⟩ := T.surjective ⟨0, h⟩
  have h₀ : (0, 0) ∈ μ := μ.up_left_mem (Nat.zero_le i) (Nat.zero_le j) hc
  rw [← hcT, ← toTableau_apply, YoungTableau.labelContent_apply, YoungDiagram.cellContent_mk]
  by_contra hne
  have hlt := T.apply_lt_apply_of_mem h₀ hc (Nat.zero_le i) (Nat.zero_le j) (by omega)
  rw [hcT, Fin.lt_def] at hlt
  exact Nat.not_lt_zero _ hlt

/-- The label `0` of a standard Young tableau has content `0`. -/
@[simp]
theorem labelContent_zero [NeZero μ.card] : YoungTableau.labelContent T.toTableau 0 = 0 :=
  T.labelContent_mk_zero (Nat.pos_of_neZero _)

/-- Labels of a standard Young tableau that differ by at most two have different contents. Two
cells on one diagonal are separated in the product order by the two cells to the right of and
below the upper one, whose labels lie strictly between theirs. -/
theorem labelContent_ne_of_lt_of_le_add_two {a b : Fin μ.card} (hab : a < b)
    (hba : (b : ℕ) ≤ a + 2) :
    YoungTableau.labelContent T.toTableau a ≠ YoungTableau.labelContent T.toTableau b := by
  obtain ⟨⟨⟨i₁, j₁⟩, hc⟩, rfl⟩ := T.surjective a
  obtain ⟨⟨⟨i₂, j₂⟩, hd⟩, rfl⟩ := T.surjective b
  simp only [← toTableau_apply, YoungTableau.labelContent_apply, YoungDiagram.cellContent_mk]
  intro hcontent
  -- the cell of `b` lies strictly below and to the right of the cell of `a`
  have hlt : i₁ < i₂ := by
    rcases lt_trichotomy i₁ i₂ with h | rfl | h
    · exact h
    · obtain rfl : j₁ = j₂ := by omega
      exact absurd rfl hab.ne
    · exact absurd hab (T.apply_lt_apply_of_mem hd hc h.le (by omega) (Or.inl h)).not_gt
  have hr : (i₁, j₁ + 1) ∈ μ := μ.up_left_mem hlt.le (by omega) hd
  have hb : (i₁ + 1, j₁) ∈ μ := μ.up_left_mem (by omega) (by omega) hd
  have h₁ := T.apply_lt_apply_of_mem hc hr le_rfl (by omega) (by omega)
  have h₂ := T.apply_lt_apply_of_mem hr hd (by omega) (by omega) (by omega)
  have h₃ := T.apply_lt_apply_of_mem hc hb (by omega) le_rfl (by omega)
  have h₄ := T.apply_lt_apply_of_mem hb hd (by omega) (by omega) (by omega)
  have hrs : (T ⟨(i₁, j₁ + 1), hr⟩ : ℕ) ≠ T ⟨(i₁ + 1, j₁), hb⟩ := fun h' => by
    have := T.injective (Fin.ext h')
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at this
    omega
  rw [Fin.lt_def] at hab h₁ h₂ h₃ h₄
  omega

/-- If two labels of a standard tableau in one row are consecutive, their cells are adjacent. -/
private theorem eq_add_one_of_row {i j₁ j₂ : ℕ} (hj : j₁ < j₂) (hcell : (i, j₂) ∈ μ)
    (hcons : (T ⟨(i, j₂), hcell⟩ : ℕ) = T ⟨(i, j₁), μ.up_left_mem le_rfl hj.le hcell⟩ + 1) :
    j₂ = j₁ + 1 := by
  by_contra hne
  have hlt : j₁ + 1 < j₂ := by omega
  have h₁ := T.row_strict (Nat.lt_add_one j₁) (μ.up_left_mem le_rfl hlt.le hcell)
  have h₂ := T.row_strict hlt hcell
  rw [Fin.lt_def] at h₁ h₂
  omega

/-- If two labels of a standard tableau in one column are consecutive, their cells are
adjacent. -/
private theorem eq_add_one_of_col {i₁ i₂ j : ℕ} (hi : i₁ < i₂) (hcell : (i₂, j) ∈ μ)
    (hcons : (T ⟨(i₂, j), hcell⟩ : ℕ) = T ⟨(i₁, j), μ.up_left_mem hi.le le_rfl hcell⟩ + 1) :
    i₂ = i₁ + 1 :=
  T.transpose.eq_add_one_of_row hi (YoungDiagram.mem_transpose.mpr hcell) (by simpa using hcons)

/-- The cells carrying consecutive labels `k` and `k + 1` of a standard tableau are adjacent in a
row, adjacent in a column, or strictly below-left or strictly above-right of each other. -/
private theorem cells_of_consecutive {k : ℕ} (hk : k + 1 < μ.card) {i₁ j₁ i₂ j₂ : ℕ}
    (hc : (i₁, j₁) ∈ μ) (hd : (i₂, j₂) ∈ μ) (h₁ : T ⟨(i₁, j₁), hc⟩ = ⟨k, by omega⟩)
    (h₂ : T ⟨(i₂, j₂), hd⟩ = ⟨k + 1, hk⟩) :
    (i₂ = i₁ ∧ j₂ = j₁ + 1) ∨ (j₂ = j₁ ∧ i₂ = i₁ + 1) ∨ (i₁ < i₂ ∧ j₂ < j₁) ∨
      (i₂ < i₁ ∧ j₁ < j₂) := by
  -- the label `k + 1` cannot lie weakly above-left of the label `k`
  have hnot : ¬(i₂ ≤ i₁ ∧ j₂ ≤ j₁) := fun ⟨hi, hj⟩ => by
    have := T.apply_lt_apply_of_mem hd hc hi hj (by
      by_contra h'
      obtain ⟨rfl, rfl⟩ : i₂ = i₁ ∧ j₂ = j₁ := by omega
      rw [h₁, Fin.mk.injEq] at h₂
      omega)
    rw [h₁, h₂, Fin.mk_lt_mk] at this
    omega
  rcases lt_trichotomy i₁ i₂ with hi | rfl | hi
  · rcases lt_trichotomy j₁ j₂ with hj | rfl | hj
    · -- the cell `(i₁, j₁ + 1)` would carry a label strictly between `k` and `k + 1`
      have hr : (i₁, j₁ + 1) ∈ μ := μ.up_left_mem hi.le hj hd
      have ha := T.apply_lt_apply_of_mem hc hr le_rfl (by omega) (by omega)
      have hb := T.apply_lt_apply_of_mem hr hd hi.le hj (by omega)
      simp only [h₁, h₂, Fin.lt_def] at ha hb
      omega
    · exact Or.inr (Or.inl ⟨rfl, T.eq_add_one_of_col hi hd (by rw [h₁, h₂])⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hi, hj⟩))
  · rcases lt_or_ge j₁ j₂ with hj | hj
    · exact Or.inl ⟨rfl, T.eq_add_one_of_row hj hd (by rw [h₁, h₂])⟩
    · exact absurd ⟨le_rfl, hj⟩ hnot
  · rcases lt_or_ge j₁ j₂ with hj | hj
    · exact Or.inr (Or.inr (Or.inr ⟨hi, hj⟩))
    · exact absurd ⟨hi.le, hj⟩ hnot

/-- The axial distance of the labels `k` and `k + 1` of a standard tableau is `1` exactly when
they lie in one row. -/
theorem axialDistance_eq_one_iff (k : ℕ) (hk : k + 1 < μ.card) :
    YoungTableau.axialDistance T.toTableau k hk = 1 ↔
      YoungTableau.rowIndex T.toTableau ⟨k + 1, hk⟩ =
        YoungTableau.rowIndex T.toTableau ⟨k, by omega⟩ := by
  obtain ⟨⟨⟨i₁, j₁⟩, hc⟩, h₁⟩ := T.surjective ⟨k, by omega⟩
  obtain ⟨⟨⟨i₂, j₂⟩, hd⟩, h₂⟩ := T.surjective ⟨k + 1, hk⟩
  rw [YoungTableau.axialDistance_eq_of_apply_eq T.toTableau h₁ h₂, ← h₁, ← h₂, ← toTableau_apply,
    ← toTableau_apply, YoungTableau.rowIndex_apply, YoungTableau.rowIndex_apply]
  simp only [YoungDiagram.cellContent_mk]
  rcases T.cells_of_consecutive hk hc hd h₁ h₂ with h | h | h | h <;> omega

/-- The axial distance of the labels `k` and `k + 1` of a standard tableau is `-1` exactly when
they lie in one column. -/
theorem axialDistance_eq_neg_one_iff (k : ℕ) (hk : k + 1 < μ.card) :
    YoungTableau.axialDistance T.toTableau k hk = -1 ↔
      YoungTableau.colIndex T.toTableau ⟨k + 1, hk⟩ =
        YoungTableau.colIndex T.toTableau ⟨k, by omega⟩ := by
  obtain ⟨⟨⟨i₁, j₁⟩, hc⟩, h₁⟩ := T.surjective ⟨k, by omega⟩
  obtain ⟨⟨⟨i₂, j₂⟩, hd⟩, h₂⟩ := T.surjective ⟨k + 1, hk⟩
  rw [YoungTableau.axialDistance_eq_of_apply_eq T.toTableau h₁ h₂, ← h₁, ← h₂, ← toTableau_apply,
    ← toTableau_apply, YoungTableau.colIndex_apply, YoungTableau.colIndex_apply]
  simp only [YoungDiagram.cellContent_mk]
  rcases T.cells_of_consecutive hk hc hd h₁ h₂ with h | h | h | h <;> omega

/-- Exchanging the labels `k` and `k + 1` of a standard Young tableau whose axial distance
`content (k + 1) - content k` is neither `1` nor `-1`. These two labels then lie neither next to
each other in a row (axial distance `1`) nor next to each other in a column (axial distance
`-1`), and the result is again standard. -/
def swap (k : ℕ) (hk : k + 1 < μ.card) (h : |YoungTableau.axialDistance T.toTableau k hk| ≠ 1) :
    StandardYoungTableau μ where
  toTableau := YoungTableau.relabel (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) T.toTableau
  row_strict' {i j₁ j₂} hj hcell := by
    simp only [YoungTableau.relabel_apply, toTableau_apply]
    refine Fin.swap_apply_lt_swap_apply rfl (T.row_strict hj hcell) fun ⟨ha, hb⟩ => h ?_
    obtain rfl := T.eq_add_one_of_row hj hcell (by rw [ha, hb])
    rw [YoungTableau.axialDistance_eq_of_apply_eq T.toTableau ha hb]
    simp
  col_strict' {i₁ i₂ j} hi hcell := by
    simp only [YoungTableau.relabel_apply, toTableau_apply]
    refine Fin.swap_apply_lt_swap_apply rfl (T.col_strict hi hcell) fun ⟨ha, hb⟩ => h ?_
    obtain rfl := T.eq_add_one_of_col hi hcell (by rw [ha, hb])
    rw [YoungTableau.axialDistance_eq_of_apply_eq T.toTableau ha hb]
    simp

/-- The underlying tableau of `T.swap k hk h` is `T` relabeled by the transposition of `k` and
`k + 1`. -/
@[simp]
theorem toTableau_swap (k : ℕ) (hk : k + 1 < μ.card) (h) :
    (T.swap k hk h).toTableau =
      YoungTableau.relabel (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) T.toTableau :=
  (rfl)

/-- The label of a cell in `T.swap k hk h` is its label in `T` with `k` and `k + 1`
exchanged. -/
@[simp]
theorem swap_apply (k : ℕ) (hk : k + 1 < μ.card) (h) (c : ↥μ.cells) :
    T.swap k hk h c = Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩ (T c) := by
  rw [← toTableau_apply, toTableau_swap, YoungTableau.relabel_apply, toTableau_apply]

/-- The axial distance of the labels `k` and `k + 1` of a standard tableau is nonzero. -/
theorem axialDistance_ne_zero (k : ℕ) (hk : k + 1 < μ.card) :
    YoungTableau.axialDistance T.toTableau k hk ≠ 0 := by
  rw [YoungTableau.axialDistance_def, sub_ne_zero]
  exact (T.labelContent_ne_of_lt_of_le_add_two (Fin.mk_lt_mk.mpr (Nat.lt_add_one k))
    (by simp only; omega)).symm

/-- Exchanging the labels `k` and `k + 1` of a standard tableau gives a standard tableau exactly
when their axial distance is not `1` or `-1`. -/
theorem exists_toTableau_eq_relabel_swap_iff (k : ℕ) (hk : k + 1 < μ.card) :
    (∃ U : StandardYoungTableau μ,
        U.toTableau = YoungTableau.relabel (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) T.toTableau) ↔
      |YoungTableau.axialDistance T.toTableau k hk| ≠ 1 := by
  refine ⟨fun ⟨U, hU⟩ h => ?_, fun h => ⟨T.swap k hk h, rfl⟩⟩
  obtain ⟨⟨⟨i₁, j₁⟩, hc⟩, h₁⟩ := T.surjective ⟨k, by omega⟩
  obtain ⟨⟨⟨i₂, j₂⟩, hd⟩, h₂⟩ := T.surjective ⟨k + 1, hk⟩
  rw [YoungTableau.axialDistance_eq_of_apply_eq T.toTableau h₁ h₂, YoungDiagram.cellContent_mk,
    YoungDiagram.cellContent_mk, abs_eq zero_le_one] at h
  -- the two labels are adjacent, `k` weakly above-left of `k + 1`, and `U` exchanges them
  have hle : i₁ ≤ i₂ ∧ j₁ ≤ j₂ ∧ (i₁ < i₂ ∨ j₁ < j₂) := by
    rcases T.cells_of_consecutive hk hc hd h₁ h₂ with h' | h' | h' | h' <;> omega
  have hlt := U.apply_lt_apply_of_mem hc hd hle.1 hle.2.1 hle.2.2
  rw [← toTableau_apply, ← toTableau_apply, hU, YoungTableau.relabel_apply,
    YoungTableau.relabel_apply, toTableau_apply, toTableau_apply, h₁, h₂, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Fin.mk_lt_mk] at hlt
  omega

/-- Exchanging the labels `k` and `k + 1` changes the tableau. -/
theorem swap_ne_self (k : ℕ) (hk : k + 1 < μ.card) (h) : T.swap k hk h ≠ T := by
  intro hT
  have := congrArg (fun U : StandardYoungTableau μ => U.toTableau (T.toTableau.symm ⟨k, by omega⟩))
    hT
  simp only [toTableau_swap, YoungTableau.relabel_apply, Equiv.apply_symm_apply,
    Equiv.swap_apply_left, Fin.mk.injEq] at this
  omega

/-- Exchanging the labels `k` and `k + 1` twice returns the original tableau. -/
@[simp]
theorem swap_swap (k : ℕ) (hk : k + 1 < μ.card) (h h') : (T.swap k hk h).swap k hk h' = T :=
  toTableau_injective (by simp)

end StandardYoungTableau

/-! ### A standard tableau is determined by the contents of its labels -/

namespace StandardYoungTableau

variable {μ : YoungDiagram}

/-- Let two standard tableaux of one shape carry each label below `i` in the same cell. If the
label `i` lies in a strictly earlier row of the first tableau than of the second, its contents in
the two differ. Otherwise the cell `d` left of `i` in the second tableau carries a smaller label,
hence the same label in the first, and the cell in the row of `i` and the column of `d` would carry
in the first tableau a label both smaller than that of `d` and at least `i`. -/
private theorem labelContent_ne_of_rowIndex_lt {T U : StandardYoungTableau μ} {i : Fin μ.card}
    (h : ∀ j < i, T.toTableau.symm j = U.toTableau.symm j)
    (hrow : YoungTableau.rowIndex T.toTableau i < YoungTableau.rowIndex U.toTableau i) :
    YoungTableau.labelContent T.toTableau i ≠ YoungTableau.labelContent U.toTableau i := by
  intro hc
  rw [YoungTableau.labelContent_def, YoungTableau.labelContent_def] at hc
  rw [YoungTableau.rowIndex_def, YoungTableau.rowIndex_def] at hrow
  have hTa : T (T.toTableau.symm i) = i := by
    rw [← toTableau_apply, Equiv.apply_symm_apply]
  have hUb : U (U.toTableau.symm i) = i := by
    rw [← toTableau_apply, Equiv.apply_symm_apply]
  generalize T.toTableau.symm i = a at hc hrow hTa
  generalize U.toTableau.symm i = b at hc hrow hUb
  obtain ⟨⟨r, s⟩, ha⟩ := a
  obtain ⟨⟨r', s'⟩, hb⟩ := b
  simp only [YoungDiagram.cellContent_mk] at hc hrow
  have hb' : (r', s') ∈ μ := hb
  have ha' : (r, s) ∈ μ := ha
  have hd : (r', s' - 1) ∈ μ := μ.up_left_mem le_rfl (Nat.sub_le _ _) hb'
  have he : (r, s' - 1) ∈ μ := μ.up_left_mem hrow.le le_rfl hd
  -- the label `j` of the cell `d = (r', s' - 1)` in `U` is smaller than `i`
  have hji : U ⟨(r', s' - 1), hd⟩ < i :=
    hUb ▸ U.apply_lt_apply_of_mem hd hb' le_rfl (by omega) (Or.inr (by omega))
  -- so `T` gives `d` the same label
  have hTd : T ⟨(r', s' - 1), hd⟩ = U ⟨(r', s' - 1), hd⟩ := by
    have hsymm := h _ hji
    rw [← toTableau_apply U, Equiv.symm_apply_apply, Equiv.symm_apply_eq] at hsymm
    simpa using hsymm.symm
  have h₁ : T ⟨(r, s' - 1), he⟩ < i :=
    (T.apply_lt_apply_of_mem he hd hrow.le le_rfl (Or.inl hrow)).trans (hTd ▸ hji)
  have h₂ : i ≤ T ⟨(r, s' - 1), he⟩ := by
    rcases (show s ≤ s' - 1 by omega).lt_or_eq with hs | hs
    · exact hTa ▸ (T.apply_lt_apply_of_mem ha' he le_rfl hs.le (Or.inr hs)).le
    · obtain rfl : s = s' - 1 := hs
      exact hTa.ge
  exact lt_irrefl i (h₂.trans_lt h₁)

/-- **A standard Young tableau is determined by the contents of its labels**, as it is by their
rows (`TauCeti.StandardYoungTableau.rowIndex_injective`). -/
theorem labelContent_injective (μ : YoungDiagram) :
    Function.Injective fun T : StandardYoungTableau μ => YoungTableau.labelContent T.toTableau := by
  intro T U hTU
  have hc : ∀ i, YoungTableau.labelContent T.toTableau i =
      YoungTableau.labelContent U.toTableau i := congrFun hTU
  have key : ∀ i, T.toTableau.symm i = U.toTableau.symm i := by
    intro i
    induction i using WellFoundedLT.induction with
    | _ i ih =>
    rcases lt_trichotomy (YoungTableau.rowIndex T.toTableau i)
        (YoungTableau.rowIndex U.toTableau i) with hr | hr | hr
    · exact absurd (hc i) (labelContent_ne_of_rowIndex_lt ih hr)
    · have hcol : YoungTableau.colIndex T.toTableau i = YoungTableau.colIndex U.toTableau i := by
        have hci := hc i
        rw [YoungTableau.labelContent_eq_colIndex_sub_rowIndex,
          YoungTableau.labelContent_eq_colIndex_sub_rowIndex, hr] at hci
        omega
      rw [YoungTableau.rowIndex_def, YoungTableau.rowIndex_def] at hr
      rw [YoungTableau.colIndex_def, YoungTableau.colIndex_def] at hcol
      exact Subtype.ext (Prod.ext hr hcol)
    · exact absurd (hc i).symm (labelContent_ne_of_rowIndex_lt (fun j hj => (ih j hj).symm) hr)
  exact toTableau_injective (Equiv.symm_bijective.injective (Equiv.ext key))

end StandardYoungTableau

end TauCeti
