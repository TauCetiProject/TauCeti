/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Kostka
public import TauCeti.Order.Hom.Basic

/-!
# Rectangular Young diagrams and column chains of semistandard tableaux

The rectangular Young diagram `YoungDiagram.rect d m` has `d` rows and `m` columns, so its cells are
the pairs `(i, j)` with `i < d` and `j < m`. Reading a bounded semistandard Young tableau of shape
`YoungDiagram.rect d m` with entries in `{0, …, n - 1}` column by column identifies each column with
a strictly increasing map `Fin d ↪o Fin n`, and weak increase along rows becomes monotonicity across
columns with respect to the componentwise order on `Fin d ↪o Fin n`.

## Main definitions

* `YoungDiagram.rect d m`: the `d × m` rectangular Young diagram.
* `TauCeti.BoundedSSYT.rectColsEquiv n d m`: the equivalence
  `(Fin m →o (Fin d ↪o Fin n)) ≃ TauCeti.BoundedSSYT n (YoungDiagram.rect d m)` between monotone
  chains of `m` column embeddings and bounded rectangular semistandard tableaux.
-/

public section

namespace YoungDiagram

/-- The rectangular Young diagram with `d` rows and `m` columns, whose cells are
`{0, …, d - 1} × {0, …, m - 1}`. -/
def rect (d m : ℕ) : YoungDiagram where
  cells := Finset.range d ×ˢ Finset.range m
  isLowerSet := by
    rintro ⟨i₂, j₂⟩ ⟨i₁, j₁⟩ ⟨hi : i₁ ≤ i₂, hj : j₁ ≤ j₂⟩ hcell
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hcell ⊢
    exact ⟨hi.trans_lt hcell.1, hj.trans_lt hcell.2⟩

@[simp]
theorem cells_rect (d m : ℕ) : (rect d m).cells = Finset.range d ×ˢ Finset.range m :=
  (rfl)

@[simp]
theorem mem_rect {d m i j : ℕ} : (i, j) ∈ rect d m ↔ i < d ∧ j < m := by
  simp [← mem_cells]

@[simp]
theorem rect_zero_left (m : ℕ) : rect 0 m = ⊥ := by
  ext c
  simp

@[simp]
theorem rect_zero_right (d : ℕ) : rect d 0 = ⊥ := by
  ext c
  simp

@[simp]
theorem card_rect (d m : ℕ) : (rect d m).card = d * m := by
  simp [YoungDiagram.card]

@[simp]
theorem rowLen_rect (d m i : ℕ) : (rect d m).rowLen i = if i < d then m else 0 := by
  have h (j : ℕ) : j < (rect d m).rowLen i ↔ i < d ∧ j < m := by
    rw [← mem_iff_lt_rowLen, mem_rect]
  split_ifs with hi
  · have h₁ := h ((rect d m).rowLen i)
    have h₂ := h m
    omega
  · have h₀ := h 0
    omega

@[simp]
theorem colLen_rect (d m j : ℕ) : (rect d m).colLen j = if j < m then d else 0 := by
  have h (i : ℕ) : i < (rect d m).colLen j ↔ i < d ∧ j < m := by
    rw [← mem_iff_lt_colLen, mem_rect]
  split_ifs with hj
  · have h₁ := h ((rect d m).colLen j)
    have h₂ := h d
    omega
  · have h₀ := h 0
    omega

end YoungDiagram

namespace TauCeti.BoundedSSYT

/-- Assemble a bounded rectangular semistandard Young tableau from a monotone chain of `m` strictly
increasing columns `Fin d ↪o Fin n`. -/
private def ofRectCols {n d m : ℕ} (C : Fin m →o (Fin d ↪o Fin n)) :
    BoundedSSYT n (YoungDiagram.rect d m) :=
  ⟨{ entry i j := if h : i < d ∧ j < m then C ⟨j, h.2⟩ ⟨i, h.1⟩ else 0
     row_weak' {i j₁ j₂} hj hcell := by
       obtain ⟨hi, hj₂⟩ := YoungDiagram.mem_rect.1 hcell
       have h₁ : i < d ∧ j₁ < m := ⟨hi, hj.trans hj₂⟩
       have h₂ : i < d ∧ j₂ < m := ⟨hi, hj₂⟩
       simp only [h₁, h₂, and_self, dite_true]
       exact Fin.le_def.1 (C.monotone (Fin.le_def.2 hj.le) ⟨i, hi⟩)
     col_strict' {i₁ i₂ j} hi hcell := by
       obtain ⟨hi₂, hj⟩ := YoungDiagram.mem_rect.1 hcell
       have h₁ : i₁ < d ∧ j < m := ⟨hi.trans hi₂, hj⟩
       have h₂ : i₂ < d ∧ j < m := ⟨hi₂, hj⟩
       simp only [h₁, h₂, and_self, dite_true]
       exact Fin.lt_def.1 ((C ⟨j, hj⟩).strictMono hi)
     zeros' {i j} hnot := by
       rw [YoungDiagram.mem_rect] at hnot
       exact dite_eq_right hnot },
    fun i j hcell ↦ by
      obtain ⟨hi, hj⟩ := YoungDiagram.mem_rect.1 hcell
      change (if h : i < d ∧ j < m then (C ⟨j, h.2⟩ ⟨i, h.1⟩ : ℕ) else 0) < n
      rw [dite_eq_left ⟨hi, hj⟩]
      exact (C ⟨j, hj⟩ ⟨i, hi⟩).2⟩

/-- Read the columns of a bounded rectangular semistandard Young tableau as a monotone chain of `m`
order embeddings `Fin d ↪o Fin n`. -/
private def toRectCols {n d m : ℕ} (T : BoundedSSYT n (YoungDiagram.rect d m)) :
    Fin m →o (Fin d ↪o Fin n) where
  toFun c := OrderEmbedding.ofStrictMono
    (fun r : Fin d ↦ ⟨T.1 r c, T.entry_lt (YoungDiagram.mem_rect.2 ⟨r.2, c.2⟩)⟩)
    fun _ r₂ hr ↦ Fin.lt_def.2 (T.1.col_strict hr (YoungDiagram.mem_rect.2 ⟨r₂.2, c.2⟩))
  monotone' _ c₂ hc r :=
    Fin.le_def.2 (T.1.row_weak_of_le hc (YoungDiagram.mem_rect.2 ⟨r.2, c₂.2⟩))

/-- **Column-chain equivalence for rectangular semistandard tableaux.** A bounded semistandard Young
tableau of shape `YoungDiagram.rect d m` in the alphabet `{0, …, n - 1}` is the same data as a
monotone chain `Fin m →o (Fin d ↪o Fin n)` of `m` columns in the componentwise order. -/
def rectColsEquiv (n d m : ℕ) :
    (Fin m →o (Fin d ↪o Fin n)) ≃ BoundedSSYT n (YoungDiagram.rect d m) where
  toFun := ofRectCols
  invFun := toRectCols
  left_inv C := by
    ext c r
    change (if h : (r : ℕ) < d ∧ (c : ℕ) < m then (C ⟨c, h.2⟩ ⟨r, h.1⟩ : ℕ) else 0) = C c r
    exact dite_eq_left ⟨r.2, c.2⟩
  right_inv T := by
    refine Subtype.ext (SemistandardYoungTableau.ext fun i j ↦ ?_)
    change (if _ : i < d ∧ j < m then T.1 i j else 0) = T.1 i j
    by_cases h : i < d ∧ j < m
    · exact dite_eq_left h
    · exact (dite_eq_right h).trans (T.1.zeros (YoungDiagram.mem_rect.not.2 h)).symm

@[simp]
theorem rectColsEquiv_apply_entry {n d m : ℕ} (C : Fin m →o (Fin d ↪o Fin n)) (r : Fin d)
    (c : Fin m) : (rectColsEquiv n d m C).1 r c = C c r := by
  change (if h : (r : ℕ) < d ∧ (c : ℕ) < m then (C ⟨c, h.2⟩ ⟨r, h.1⟩ : ℕ) else 0) = C c r
  exact dite_eq_left ⟨r.2, c.2⟩

@[simp]
theorem rectColsEquiv_symm_apply_apply {n d m : ℕ} (T : BoundedSSYT n (YoungDiagram.rect d m))
    (c : Fin m) (r : Fin d) :
    (rectColsEquiv n d m).symm T c r =
      ⟨T.1 r c, T.entry_lt (YoungDiagram.mem_rect.2 ⟨r.2, c.2⟩)⟩ :=
  (rfl)

theorem val_rectColsEquiv_symm_apply_apply {n d m : ℕ} (T : BoundedSSYT n (YoungDiagram.rect d m))
    (c : Fin m) (r : Fin d) : ((rectColsEquiv n d m).symm T c r : ℕ) = T.1 r c :=
  (rfl)

end TauCeti.BoundedSSYT
