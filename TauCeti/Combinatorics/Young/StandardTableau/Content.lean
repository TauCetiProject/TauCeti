/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.StandardTableau.Basic
import TauCeti.Combinatorics.Young.StandardTableau.Order
import TauCeti.GroupTheory.Perm.Fin

/-!
# Contents of nearby labels in standard Young tableaux

The content of a label `k` in a tableau `t` is `YoungTableau.labelContent t k`, the column minus the
row of the cell carrying `k`. This file records the facts about the contents of the labels
`k`, `k + 1` and `k + 2` of a standard Young tableau that govern Young's seminormal form, in which
the simple transposition of `k` and `k + 1` acts through the *axial distance*
`labelContent T (k + 1) - labelContent T k`:

* the axial distance is the difference of the contents of the cells carrying `k + 1` and `k`
  (`TauCeti.YoungTableau.axialDistance_eq_of_apply_eq`);
* the label `0` sits in the corner `(0, 0)`, of content `0`
  (`TauCeti.StandardYoungTableau.labelContent_zero`);
* two labels differing by at most two lie on different diagonals, so their contents differ
  (`TauCeti.StandardYoungTableau.labelContent_ne_of_lt_of_le_add_two`);
* the axial distance `YoungTableau.axialDistance` of the labels `k` and `k + 1` of a standard
  tableau is nonzero (`TauCeti.StandardYoungTableau.axialDistance_ne_zero`);
* exchanging the labels `k` and `k + 1` of a standard tableau gives a standard tableau as soon as
  the axial distance is not `1` or `-1`, that is, as soon as the two labels do not lie next to each
  other in one row or one column (`TauCeti.StandardYoungTableau.swap`); this changes the tableau
  (`TauCeti.StandardYoungTableau.swap_ne_self`) and negates the axial distance
  (`TauCeti.YoungTableau.axialDistance_relabel_swap`).

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

/-- Exchanging the labels `k` and `k + 1` negates their axial distance. -/
@[simp]
theorem axialDistance_relabel_swap (t : YoungTableau μ) (k : ℕ) (hk : k + 1 < μ.card) :
    axialDistance (relabel (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) t) k hk =
      -axialDistance t k hk := by
  simp [axialDistance_def, Equiv.swap_inv]

end YoungTableau

namespace StandardYoungTableau

variable {μ : YoungDiagram} (T : StandardYoungTableau μ)

/-- The label `0` of a standard Young tableau sits in the corner `(0, 0)`, of content `0`. -/
theorem labelContent_zero (h : 0 < μ.card) : YoungTableau.labelContent T.toTableau ⟨0, h⟩ = 0 := by
  obtain ⟨⟨⟨i, j⟩, hc⟩, hcT⟩ := T.surjective ⟨0, h⟩
  have h₀ : (0, 0) ∈ μ := μ.up_left_mem (Nat.zero_le i) (Nat.zero_le j) hc
  rw [← hcT, ← toTableau_apply, YoungTableau.labelContent_apply, YoungDiagram.cellContent_mk]
  by_contra hne
  have hlt := T.apply_lt_apply_of_mem h₀ hc (Nat.zero_le i) (Nat.zero_le j) (by omega)
  rw [hcT, Fin.lt_def] at hlt
  exact Nat.not_lt_zero _ hlt

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
    i₂ = i₁ + 1 := by
  by_contra hne
  have hlt : i₁ + 1 < i₂ := by omega
  have h₁ := T.col_strict (Nat.lt_add_one i₁) (μ.up_left_mem hlt.le le_rfl hcell)
  have h₂ := T.col_strict hlt hcell
  rw [Fin.lt_def] at h₁ h₂
  omega

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

/-- The axial distance of the labels `k` and `k + 1` of a standard tableau is nonzero. -/
theorem axialDistance_ne_zero (k : ℕ) (hk : k + 1 < μ.card) :
    YoungTableau.axialDistance T.toTableau k hk ≠ 0 := by
  rw [YoungTableau.axialDistance_def, sub_ne_zero]
  exact (T.labelContent_ne_of_lt_of_le_add_two (Fin.mk_lt_mk.mpr (Nat.lt_add_one k))
    (by simp only; omega)).symm

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
theorem swap_swap (k : ℕ) (hk : k + 1 < μ.card) (h h') : (T.swap k hk h).swap k hk h' = T := by
  apply DFunLike.ext
  intro c
  simp only [← toTableau_apply, toTableau_swap, YoungTableau.relabel_relabel, Equiv.swap_mul_self,
    YoungTableau.relabel_one]

end StandardYoungTableau

end TauCeti
