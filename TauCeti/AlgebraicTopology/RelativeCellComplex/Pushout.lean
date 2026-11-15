/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import TauCeti.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape

/-!
# Cobase change of relative cell complexes

Let `c : RelativeCellComplex basicCell f` present `f : X ⟶ Y` as a transfinite composition of cell
attachments, and let `g : X ⟶ Z` be any morphism. Then the cobase change
`pushout.inr f g : Z ⟶ pushout f g` is again a relative cell complex for the same family of basic
cells (`HomotopicalAlgebra.RelativeCellComplex.pushout`): it is obtained from `Z` by attaching the
cells of `c`, at the same steps and along the attaching maps of `c` followed by the stage
inclusions. In topology, this is the statement that gluing a relative CW complex `(Y, X)` to a
space `Z` along a map `X → Z` gives a relative CW complex `(Z ∪_X Y, Z)` with the same cells.

The `j`-th stage of the new complex is the pushout of the `j`-th stage of `c` along `g`
(`CategoryTheory.TransfiniteCompositionOfShape.pushout`). Each of its steps is the pushout of the
corresponding step of `c`
(`CategoryTheory.TransfiniteCompositionOfShape.isPushout_pushoutStageMap`), so the pushout squares
attaching the cells of `c` paste with it.

## Main definitions

* `HomotopicalAlgebra.RelativeCellComplex.pushout`: the cobase change of a relative cell complex.
* `HomotopicalAlgebra.RelativeCellComplex.pushoutCellsEquiv`: its cells are those of the original
  complex.

## Main results

* `HomotopicalAlgebra.RelativeCellComplex.pushout_cells_ι`: the inclusion of a cell of the cobase
  change is the inclusion of the corresponding cell of the original complex, followed by
  `pushout.inl f g`; `HomotopicalAlgebra.RelativeCellComplex.pushout_cells_ι'` states this for
  an arbitrary cell, through `HomotopicalAlgebra.RelativeCellComplex.pushoutCellsEquiv`.

## References

* M. Hovey, *Model Categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 2.1, for the stability of relative cell complexes under cobase change.
-/

public section

universe w w' t v u

open CategoryTheory Limits

namespace HomotopicalAlgebra.RelativeCellComplex

variable {C : Type u} [Category.{v} C]
  {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → C} {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i}
  {X Y : C} {f : X ⟶ Y} (c : RelativeCellComplex.{w} basicCell f) {Z : C}
  (g : X ⟶ Z) [HasPushoutsAlong g]

/-- **Cobase change of a relative cell complex.** If `f : X ⟶ Y` is a relative cell complex and
`g : X ⟶ Z` is any morphism, then `pushout.inr f g : Z ⟶ pushout f g` is a relative cell complex
for the same basic cells: its `j`-th stage is the pushout of the `j`-th stage of `f` along `g`,
and it attaches the cells of `f` at the same steps, along the attaching maps of `f` followed by
the maps to these pushouts. The body is exposed so that the cells of the cobase change are the
cells of `c` by definition. -/
@[expose] noncomputable def pushout : RelativeCellComplex.{w} basicCell (pushout.inr f g) :=
  .mk (c.toTransfiniteCompositionOfShape.pushout g) fun j hj ↦
    { (c.attachCells j hj) with
      g₁ := (c.attachCells j hj).g₁ ≫ pushout.inl (c.toStage j) g
      g₂ := (c.attachCells j hj).g₂ ≫ pushout.inl (c.toStage (Order.succ j)) g
      isPushout := (c.attachCells j hj).isPushout.paste_horiz
        (c.isPushout_pushoutStageMap g _).flip }

/-- The cells of the cobase change `c.pushout g` are the cells of `c`. Exposed so that a cell and
its image are attached at the same step by definition, as the statement of `pushout_cells_ι'`
needs. -/
@[expose] def pushoutCellsEquiv : (c.pushout g).Cells ≃ c.Cells where
  toFun γ := ⟨γ.j, γ.hj, γ.k⟩
  invFun γ := ⟨γ.j, γ.hj, γ.k⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `c.pushoutCellsEquiv g` preserves the step at which a cell is attached. -/
@[simp]
lemma pushoutCellsEquiv_apply_j (γ : (c.pushout g).Cells) : (c.pushoutCellsEquiv g γ).j = γ.j :=
  (rfl)

/-- `(c.pushoutCellsEquiv g).symm` preserves the step at which a cell is attached. -/
@[simp]
lemma pushoutCellsEquiv_symm_apply_j (γ : c.Cells) : ((c.pushoutCellsEquiv g).symm γ).j = γ.j :=
  (rfl)

/-- A cell attached at step `j` of the cobase change `c.pushout g` is the corresponding cell of
`c`, followed by the map from the `(j + 1)`-th stage of `c` to its cobase change. -/
lemma pushout_attachCells_cell (j : J) (hj : ¬IsMax j) (k : (c.attachCells j hj).ι) :
    ((c.pushout g).attachCells j hj).cell k =
      (c.attachCells j hj).cell k ≫ Limits.pushout.inl (c.toStage (Order.succ j)) g :=
  (Category.assoc _ _ _).symm

/-- The inclusion of a cell of the cobase change `c.pushout g` is the inclusion of the
corresponding cell of `c`, followed by `pushout.inl f g`. -/
@[simp, reassoc]
lemma pushout_cells_ι (j : J) (hj : ¬IsMax j) (k : (c.attachCells j hj).ι) :
    Cells.ι (c := c.pushout g) ⟨j, hj, k⟩ =
      Cells.ι (c := c) ⟨j, hj, k⟩ ≫ Limits.pushout.inl f g := by
  -- The inclusion of a cell of `c.pushout g` is its attaching map followed by
  -- `c.pushoutStageIncl g`, by definition.
  refine (c.pushout_attachCells_cell g j hj k =≫ c.pushoutStageIncl g (Order.succ j)).trans ?_
  -- Restate the goal with the stages of `c.pushout g` read as pushouts, so that `simp` applies.
  change ((c.attachCells j hj).cell k ≫ Limits.pushout.inl (c.toStage (Order.succ j)) g) ≫
      c.pushoutStageIncl g (Order.succ j) =
    ((c.attachCells j hj).cell k ≫ c.incl.app (Order.succ j)) ≫ Limits.pushout.inl f g
  simp

/-- The inclusion of any cell `γ` of the cobase change `c.pushout g` is the inclusion of the cell
`c.pushoutCellsEquiv g γ` of `c`, followed by `pushout.inl f g`. -/
@[reassoc]
lemma pushout_cells_ι' (γ : (c.pushout g).Cells) :
    γ.ι = (c.pushoutCellsEquiv g γ).ι ≫ Limits.pushout.inl f g := by
  obtain ⟨j, hj, k⟩ := γ
  exact c.pushout_cells_ι g j hj k

end HomotopicalAlgebra.RelativeCellComplex
