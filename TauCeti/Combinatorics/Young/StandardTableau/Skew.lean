/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.StandardTableau.Basic
public import TauCeti.Combinatorics.Young.SkewTableau

/-!
# Standard skew Young tableaux

A standard tableau of skew shape `outer / inner` labels its cells bijectively by
`Fin (outer.card - inner.card)`, increasingly along rows and columns. These are the
standard tableaux used in standardisation and jeu de taquin. The containment of diagrams
is part of the data; no comparisons are imposed across cells removed by the inner shape.

This file supplies the finite carrier, its embedding into semistandard skew tableaux,
transposition, and the entry-preserving equivalence with `StandardYoungTableau` when the
inner diagram is empty. Transposition preserves the numeric labels and exchanges the
row and column conditions.

## References

* W. Fulton, *Young Tableaux*, Sections 1.1 and 2.1.
-/

public section

namespace TauCeti

/-- A standard tableau of skew shape `outer / inner`: a bijective labeling of the skew
cells by consecutive labels starting at zero, strictly increasing in rows and columns. -/
structure SkewStandardYoungTableau (inner outer : YoungDiagram) where
  /-- The inner diagram is contained in the outer diagram. -/
  le : inner ≤ outer
  /-- The bijective labeling of the skew cells. -/
  labeling : ↥(outer.cells \ inner.cells) ≃ Fin (outer.card - inner.card)
  /-- Labels increase along rows of the skew shape. -/
  row_strict' : ∀ (a b : ↥(outer.cells \ inner.cells)),
    a.1.1 = b.1.1 → a.1.2 < b.1.2 → labeling a < labeling b
  /-- Labels increase down columns of the skew shape. -/
  col_strict' : ∀ (a b : ↥(outer.cells \ inner.cells)),
    a.1.2 = b.1.2 → a.1.1 < b.1.1 → labeling a < labeling b

namespace SkewStandardYoungTableau

variable {inner outer : YoungDiagram}

instance : FunLike (SkewStandardYoungTableau inner outer)
    ↥(outer.cells \ inner.cells) (Fin (outer.card - inner.card)) where
  coe T := T.labeling
  coe_injective T U h := by
    cases T
    cases U
    congr
    exact Equiv.ext (congrFun h)

/-- Evaluating the underlying labeling agrees with evaluating the tableau. -/
@[simp]
theorem labeling_apply (T : SkewStandardYoungTableau inner outer)
    (c : ↥(outer.cells \ inner.cells)) : T.labeling c = T c :=
  (rfl)

/-- Standard skew tableaux are determined by their labels on the skew cells. -/
@[ext]
theorem ext {T U : SkewStandardYoungTableau inner outer} (h : ∀ c, T c = U c) : T = U :=
  DFunLike.ext T U h

/-- Each label occurs exactly once. -/
theorem bijective (T : SkewStandardYoungTableau inner outer) : Function.Bijective T :=
  T.labeling.bijective

/-- Labels increase along rows. -/
theorem row_strict (T : SkewStandardYoungTableau inner outer)
    (a b : ↥(outer.cells \ inner.cells)) (hi : a.1.1 = b.1.1) (hj : a.1.2 < b.1.2) :
    T a < T b :=
  T.row_strict' a b hi hj

/-- Labels increase down columns. -/
theorem col_strict (T : SkewStandardYoungTableau inner outer)
    (a b : ↥(outer.cells \ inner.cells)) (hj : a.1.2 = b.1.2) (hi : a.1.1 < b.1.1) :
    T a < T b :=
  T.col_strict' a b hj hi

/-- There are finitely many standard tableaux of a fixed skew shape. -/
noncomputable instance : Fintype (SkewStandardYoungTableau inner outer) :=
  FunLike.fintype _

/-- Forget standardness, retaining the numeric labels and filling all other cells by zero. -/
def toSemistandard (T : SkewStandardYoungTableau inner outer) :
    SkewSemistandardYoungTableau inner outer where
  entry i j := if h : (i, j) ∈ outer.cells \ inner.cells then (T ⟨(i, j), h⟩).val else 0
  le := T.le
  row_weak' {i j₁ j₂} hj h₁ h₂ := by
    have ha : (i, j₁) ∈ outer.cells \ inner.cells :=
      Finset.mem_sdiff.mpr ⟨outer.up_left_mem le_rfl hj.le h₂, h₁⟩
    have hb : (i, j₂) ∈ outer.cells \ inner.cells :=
      Finset.mem_sdiff.mpr ⟨h₂, fun h => h₁ (inner.up_left_mem le_rfl hj.le h)⟩
    simpa only [dite_eq_left ha, dite_eq_left hb] using
      (Fin.lt_def.mp (T.row_strict ⟨_, ha⟩ ⟨_, hb⟩ rfl hj)).le
  col_strict' {i₁ i₂ j} hi h₁ h₂ := by
    have ha : (i₁, j) ∈ outer.cells \ inner.cells :=
      Finset.mem_sdiff.mpr ⟨outer.up_left_mem hi.le le_rfl h₂, h₁⟩
    have hb : (i₂, j) ∈ outer.cells \ inner.cells :=
      Finset.mem_sdiff.mpr ⟨h₂, fun h => h₁ (inner.up_left_mem hi.le le_rfl h)⟩
    simpa only [dite_eq_left ha, dite_eq_left hb] using
      Fin.lt_def.mp (T.col_strict ⟨_, ha⟩ ⟨_, hb⟩ rfl hi)
  zeros_inner' h := dite_eq_right (fun hc => (Finset.mem_sdiff.mp hc).2 h)
  zeros' h := dite_eq_right (fun hc => h (Finset.mem_sdiff.mp hc).1)

/-- Forgetting standardness preserves the entry on each skew cell. -/
@[simp]
theorem toSemistandard_apply (T : SkewStandardYoungTableau inner outer)
    (c : ↥(outer.cells \ inner.cells)) : T.toSemistandard c.1.1 c.1.2 = (T c).val := by
  rw [← SkewSemistandardYoungTableau.entry_eq_coe]
  exact dite_eq_left c.2

/-- Forgetting standardness loses no information. -/
theorem toSemistandard_injective :
    Function.Injective (toSemistandard (inner := inner) (outer := outer)) := by
  intro T U h
  apply ext
  intro c
  apply Fin.ext
  simpa only [toSemistandard_apply] using congrArg (fun S => S c.1.1 c.1.2) h

/-- Each label below the size of the skew shape occurs once, and no other label occurs. -/
@[simp]
theorem content_toSemistandard (T : SkewStandardYoungTableau inner outer) (k : ℕ) :
    T.toSemistandard.content k = if k < outer.card - inner.card then 1 else 0 := by
  rw [SkewSemistandardYoungTableau.content_apply]
  by_cases hk : k < outer.card - inner.card
  · rw [ite_eq_left hk, Finset.card_eq_one]
    refine ⟨(T.labeling.symm ⟨k, hk⟩).1, ?_⟩
    ext c
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, h⟩
      have he : T.labeling ⟨c, hc⟩ = ⟨k, hk⟩ :=
        Fin.ext ((toSemistandard_apply T ⟨c, hc⟩).symm.trans h)
      exact congrArg Subtype.val (T.labeling.injective (he.trans
        (T.labeling.apply_symm_apply ⟨k, hk⟩).symm))
    · rintro rfl
      exact ⟨(T.labeling.symm ⟨k, hk⟩).2, by
        rw [toSemistandard_apply, ← labeling_apply, Equiv.apply_symm_apply]⟩
  · rw [ite_eq_right hk, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc h
    have he := toSemistandard_apply T ⟨c, hc⟩
    exact hk (h ▸ he ▸ (T ⟨c, hc⟩).isLt)

private def transposeCells (inner outer : YoungDiagram) :
    ↥(outer.transpose.cells \ inner.transpose.cells) ≃ ↥(outer.cells \ inner.cells) :=
  (Equiv.prodComm ℕ ℕ).subtypeEquiv fun c => by
    simp only [Finset.mem_sdiff, YoungDiagram.mem_cells, YoungDiagram.mem_transpose]
    rfl

@[simp]
private theorem transposeCells_apply (c : ↥(outer.transpose.cells \ inner.transpose.cells)) :
    (transposeCells inner outer c).1 = c.1.swap := (rfl)

@[simp]
private theorem transposeCells_symm_apply (c : ↥(outer.cells \ inner.cells)) :
    ((transposeCells inner outer).symm c).1 = c.1.swap := (rfl)

/-- Transposition exchanges rows and columns and retains the numeric labels. -/
def transpose (T : SkewStandardYoungTableau inner outer) :
    SkewStandardYoungTableau inner.transpose outer.transpose where
  le := YoungDiagram.transpose_mono T.le
  labeling := (transposeCells inner outer).trans (T.labeling.trans
    (finCongr (by rw [YoungDiagram.card_transpose, YoungDiagram.card_transpose])))
  row_strict' a b hi hj := by
    simpa only [Equiv.trans_apply, Fin.lt_def, finCongr_apply_coe, labeling_apply] using
      T.col_strict (transposeCells inner outer a) (transposeCells inner outer b) hi hj
  col_strict' a b hj hi := by
    simpa only [Equiv.trans_apply, Fin.lt_def, finCongr_apply_coe, labeling_apply] using
      T.row_strict (transposeCells inner outer a) (transposeCells inner outer b) hj hi

/-- Transposition keeps the label of the corresponding cell. -/
@[simp]
theorem transpose_apply_val (T : SkewStandardYoungTableau inner outer)
    (c : ↥(outer.transpose.cells \ inner.transpose.cells)) :
    (T.transpose c).val = (T ⟨c.1.swap, by
      simpa only [Finset.mem_sdiff, YoungDiagram.mem_cells,
        YoungDiagram.mem_transpose] using c.2⟩).val :=
  (rfl)

private def untranspose (T : SkewStandardYoungTableau inner.transpose outer.transpose) :
    SkewStandardYoungTableau inner outer where
  le := YoungDiagram.transpose_le_iff.mp T.le
  labeling := (transposeCells inner outer).symm.trans (T.labeling.trans
    (finCongr (by rw [YoungDiagram.card_transpose, YoungDiagram.card_transpose])))
  row_strict' a b hi hj := by
    simpa only [Equiv.trans_apply, Fin.lt_def, finCongr_apply_coe, labeling_apply] using
      T.col_strict ((transposeCells inner outer).symm a)
        ((transposeCells inner outer).symm b) hi hj
  col_strict' a b hj hi := by
    simpa only [Equiv.trans_apply, Fin.lt_def, finCongr_apply_coe, labeling_apply] using
      T.row_strict ((transposeCells inner outer).symm a)
        ((transposeCells inner outer).symm b) hj hi

/-- Transposition is an equivalence between standard tableaux of transposed skew shapes. -/
def transposeEquiv (inner outer : YoungDiagram) :
    SkewStandardYoungTableau inner outer ≃
      SkewStandardYoungTableau inner.transpose outer.transpose where
  toFun := transpose
  invFun := untranspose
  left_inv T := by
    apply ext
    intro c
    apply Fin.ext
    simp [transpose, untranspose, ← labeling_apply]
  right_inv T := by
    apply ext
    intro c
    apply Fin.ext
    simp [transpose, untranspose, ← labeling_apply]

/-- The forward transpose equivalence is transposition. -/
@[simp]
theorem transposeEquiv_apply (T : SkewStandardYoungTableau inner outer) :
    transposeEquiv inner outer T = T.transpose :=
  (rfl)

/-- Applying the inverse transpose equivalence to a transposed tableau recovers it. -/
@[simp]
theorem transposeEquiv_symm_transpose (T : SkewStandardYoungTableau inner outer) :
    (transposeEquiv inner outer).symm T.transpose = T :=
  (transposeEquiv inner outer).symm_apply_apply T

/-- Transposing the inverse transpose comparison recovers the original tableau. -/
@[simp]
theorem transpose_transposeEquiv_symm
    (T : SkewStandardYoungTableau inner.transpose outer.transpose) :
    ((transposeEquiv inner outer).symm T).transpose = T :=
  (transposeEquiv inner outer).apply_symm_apply T

/-- The inverse transpose equivalence swaps the coordinates and retains the labels. -/
@[simp]
theorem transposeEquiv_symm_apply_val
    (T : SkewStandardYoungTableau inner.transpose outer.transpose)
    (c : ↥(outer.cells \ inner.cells)) :
    (((transposeEquiv inner outer).symm T) c).val = (T ⟨c.1.swap, by
      simpa only [Finset.mem_sdiff, YoungDiagram.mem_cells,
        YoungDiagram.mem_transpose, Prod.swap_swap] using c.2⟩).val :=
  (rfl)

private def botCells (outer : YoungDiagram) : ↥(outer.cells \ (⊥ : YoungDiagram).cells) ≃
    ↥outer.cells :=
  Equiv.subtypeEquivRight fun c => by simp

/-- Standard skew tableaux with empty inner diagram are exactly standard straight tableaux. -/
def botEquiv (outer : YoungDiagram) :
    SkewStandardYoungTableau ⊥ outer ≃ StandardYoungTableau outer where
  toFun T :=
    { toTableau := (botCells outer).symm.trans
        (T.labeling.trans (finCongr (by simp [YoungDiagram.card])))
      row_strict' h hc := by
        exact T.row_strict _ _ rfl h
      col_strict' h hc := by
        exact T.col_strict _ _ rfl h }
  invFun T :=
    { le := bot_le
      labeling := (botCells outer).trans
        (T.toTableau.trans (finCongr (by simp [YoungDiagram.card])))
      row_strict' a b hi hj := by
        obtain ⟨⟨i, j₁⟩, ha⟩ := a
        obtain ⟨⟨i', j₂⟩, hb⟩ := b
        dsimp at hi hj
        subst i'
        exact T.row_strict hj (Finset.mem_sdiff.mp hb).1
      col_strict' a b hj hi := by
        obtain ⟨⟨i₁, j⟩, ha⟩ := a
        obtain ⟨⟨i₂, j'⟩, hb⟩ := b
        dsimp at hi hj
        subst j'
        exact T.col_strict hi (Finset.mem_sdiff.mp hb).1 }
  left_inv T := by
    ext c
    rfl
  right_inv T := by
    ext c
    rfl

/-- The straight-shape comparison preserves each numeric label. -/
@[simp]
theorem botEquiv_apply_val (T : SkewStandardYoungTableau ⊥ outer) (c : ↥outer.cells) :
    (botEquiv outer T c).val = (T ⟨c.1, by simp [c.2]⟩).val :=
  (rfl)

/-- The inverse straight-shape comparison preserves each numeric label. -/
theorem botEquiv_symm_apply_val (T : StandardYoungTableau outer)
    (c : ↥(outer.cells \ (⊥ : YoungDiagram).cells)) :
    ((botEquiv outer).symm T c).val = (T ⟨c.1, (Finset.mem_sdiff.mp c.2).1⟩).val :=
  (rfl)

/-- The semistandard tableau underlying the inverse straight-shape comparison has the
original numeric labels. -/
@[simp]
theorem toSemistandard_botEquiv_symm_apply (T : StandardYoungTableau outer)
    (c : ↥outer.cells) :
    ((botEquiv outer).symm T).toSemistandard c.1.1 c.1.2 = (T c).val := by
  rw [toSemistandard_apply _ ⟨c.1, by simp [c.2]⟩, botEquiv_symm_apply_val]

/-- The unique tableau on an empty skew shape has no labels. -/
def empty (μ : YoungDiagram) : SkewStandardYoungTableau μ μ where
  le := le_rfl
  labeling :=
    haveI : IsEmpty ↥(μ.cells \ μ.cells) := ⟨fun c => by simpa using c.2⟩
    (Equiv.equivOfIsEmpty _ (Fin 0)).trans (finCongr (Nat.sub_self μ.card).symm)
  row_strict' a := False.elim (by simpa using a.2)
  col_strict' a := False.elim (by simpa using a.2)

/-- An empty skew shape has only one standard tableau. -/
instance (μ : YoungDiagram) : Unique (SkewStandardYoungTableau μ μ) where
  default := empty μ
  uniq T := by
    apply ext
    intro c
    exact False.elim (by simpa using c.2)

end SkewStandardYoungTableau

end TauCeti
