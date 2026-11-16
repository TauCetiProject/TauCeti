/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic

/-!
# Functoriality and reindexing of relative cell complexes

A colimit-preserving functor carries cell attachments to cell attachments
(`HomotopicalAlgebra.AttachCells.map`) and relative cell complexes to relative cell complexes
(`HomotopicalAlgebra.RelativeCellComplex.map`), preserving the indexing of cells and acting on each
cell inclusion by applying the functor (`HomotopicalAlgebra.RelativeCellComplex.map_cells_ι`).

This file also extends Mathlib's arrow-isomorphism transport and cell-type reindexing from
individual cell attachments and transfinite compositions to relative cell complexes:
* `HomotopicalAlgebra.RelativeCellComplex.ofArrowIso`: transports a relative cell complex along an
  isomorphism of arrows `Arrow.mk f ≅ Arrow.mk f'`, composing each cell inclusion with the target
  isomorphism.
* `HomotopicalAlgebra.RelativeCellComplex.reindexCellTypes`: replaces the family of basic cells
  along arrow isomorphisms, precomposing each cell inclusion with the corresponding target
  isomorphism.

Together these operations transfer cell decompositions across adjunctions, such as pushing the
skeletal cell complex of a simplicial set forward along geometric realization to obtain a
categorical CW structure.

## References

* M. Hovey, *Model Categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 2.1.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press, 1990.
-/

public section

universe w w' t t' v v' u u'

open CategoryTheory Limits

namespace HomotopicalAlgebra

namespace AttachCells

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {α : Type t} {A B : α → C} {g : ∀ a, A a ⟶ B a} {X₁ X₂ : C} {f : X₁ ⟶ X₂}
  (c : AttachCells.{w} g f)

/-- A functor preserving the relevant coproducts and pushout sends a cell attachment to a cell
attachment with the same cell index type and mapped basic cells. -/
@[expose] noncomputable def map (F : C ⥤ D)
    [PreservesColimit (Discrete.functor fun i ↦ A (c.π i)) F]
    [PreservesColimit (Discrete.functor fun i ↦ B (c.π i)) F]
    [PreservesColimit (span c.g₁ c.m) F] :
    AttachCells.{w} (fun a ↦ F.map (g a)) (F.map f) where
  ι := c.ι
  π := c.π
  cofan₁ := Cofan.mk (F.obj c.cofan₁.pt) fun i ↦ F.map (c.cofan₁.inj i)
  cofan₂ := Cofan.mk (F.obj c.cofan₂.pt) fun i ↦ F.map (c.cofan₂.inj i)
  isColimit₁ := (Cofan.isColimitMapCoconeEquiv F _ c.cofan₁) (isColimitOfPreserves F c.isColimit₁)
  isColimit₂ := (Cofan.isColimitMapCoconeEquiv F _ c.cofan₂) (isColimitOfPreserves F c.isColimit₂)
  m := F.map c.m
  hm i := (F.map_comp _ _).symm.trans ((congrArg F.map (c.hm i)).trans (F.map_comp _ _))
  g₁ := F.map c.g₁
  g₂ := F.map c.g₂
  isPushout := c.isPushout.map F

/-- The inclusion of a cell in `c.map F` is `F.map` of the original cell inclusion. -/
@[simp, reassoc]
lemma map_cell (F : C ⥤ D)
    [PreservesColimit (Discrete.functor fun i ↦ A (c.π i)) F]
    [PreservesColimit (Discrete.functor fun i ↦ B (c.π i)) F]
    [PreservesColimit (span c.g₁ c.m) F] (i : c.ι) :
    (c.map F).cell i = F.map (c.cell i) :=
  (F.map_comp _ _).symm

/-- The inclusion of a cell after reindexing cell types is the original cell inclusion precomposed
with the inverse target isomorphism. -/
@[simp, reassoc]
lemma reindexCellTypes_cell {α' : Type t'} {A' B' : α' → C} (g' : ∀ i', A' i' ⟶ B' i')
    (a : α → α') (ha : ∀ i, Arrow.mk (g i) ≅ Arrow.mk (g' (a i))) (i : c.ι) :
    (c.reindexCellTypes g' a ha).cell i =
      Arrow.rightFunc.map (ha (c.π i)).inv ≫ c.cell i :=
  Category.assoc _ _ _

end AttachCells

namespace RelativeCellComplex

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → C}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i}
  {X Y : C} {f : X ⟶ Y} (c : RelativeCellComplex.{w} basicCell f)

section Map

variable (F : C ⥤ D) [PreservesWellOrderContinuousOfShape J F] [PreservesColimitsOfShape J F]
  [∀ j hj, PreservesColimit (Discrete.functor fun i ↦ A j ((c.attachCells j hj).π i)) F]
  [∀ j hj, PreservesColimit (Discrete.functor fun i ↦ B j ((c.attachCells j hj).π i)) F]
  [∀ j hj, PreservesColimit (span (c.attachCells j hj).g₁ (c.attachCells j hj).m) F]

/-- Push a relative cell complex forward along a functor preserving the relevant colimits.
The stages are the images of the stages of `c`, and the cells at each step are unchanged. -/
@[expose] noncomputable def map :
    RelativeCellComplex.{w} (fun j i ↦ F.map (basicCell j i)) (F.map f) :=
  .mk (c.toTransfiniteCompositionOfShape.map F) fun j hj ↦ (c.attachCells j hj).map F

/-- The cells of `c.map F` are the cells of `c`. -/
@[expose] def mapCellsEquiv : (c.map F).Cells ≃ c.Cells where
  toFun γ := ⟨γ.j, γ.hj, γ.k⟩
  invFun γ := ⟨γ.j, γ.hj, γ.k⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma mapCellsEquiv_apply_j (γ : (c.map F).Cells) : (c.mapCellsEquiv F γ).j = γ.j := (rfl)

@[simp]
lemma mapCellsEquiv_symm_apply_j (γ : c.Cells) : ((c.mapCellsEquiv F).symm γ).j = γ.j := (rfl)

/-- The inclusion of a cell in `c.map F` is `F.map` of the inclusion of the corresponding cell of
`c`. -/
@[simp, reassoc]
lemma map_cells_ι (j : J) (hj : ¬IsMax j) (k : (c.attachCells j hj).ι) :
    Cells.ι (c := c.map F) ⟨j, hj, k⟩ = F.map (Cells.ι (c := c) ⟨j, hj, k⟩) :=
  (((AttachCells.map_cell (c.attachCells j hj) F k) =≫ _).trans <|
    (F.map _ ≫= Category.comp_id _).trans (F.map_comp _ _).symm)

/-- Variant of `map_cells_ι` for an arbitrary cell, stated through `mapCellsEquiv`. -/
@[reassoc]
lemma map_cells_ι' (γ : (c.map F).Cells) :
    γ.ι = F.map (c.mapCellsEquiv F γ).ι :=
  c.map_cells_ι F γ.j γ.hj γ.k

end Map

section OfArrowIso

variable {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f')

/-- Transport a relative cell complex along an isomorphism of arrows `Arrow.mk f ≅ Arrow.mk f'`.
The functor of stages and cell attachments are unchanged; the colimit cocone is postcomposed with
the target isomorphism. -/
@[expose] def ofArrowIso : RelativeCellComplex.{w} basicCell f' :=
  .mk (c.toTransfiniteCompositionOfShape.ofArrowIso e) c.attachCells

/-- The cells of `c.ofArrowIso e` are the cells of `c`. -/
@[expose] def ofArrowIsoCellsEquiv : (c.ofArrowIso e).Cells ≃ c.Cells where
  toFun γ := ⟨γ.j, γ.hj, γ.k⟩
  invFun γ := ⟨γ.j, γ.hj, γ.k⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma ofArrowIsoCellsEquiv_apply_j (γ : (c.ofArrowIso e).Cells) :
    (c.ofArrowIsoCellsEquiv e γ).j = γ.j := (rfl)

@[simp]
lemma ofArrowIsoCellsEquiv_symm_apply_j (γ : c.Cells) :
    ((c.ofArrowIsoCellsEquiv e).symm γ).j = γ.j := (rfl)

/-- The inclusion of a cell in `c.ofArrowIso e` is the inclusion of the corresponding cell of `c`
followed by the target isomorphism `e.hom.right`. -/
@[simp, reassoc]
lemma ofArrowIso_cells_ι (j : J) (hj : ¬IsMax j) (k : (c.attachCells j hj).ι) :
    Cells.ι (c := c.ofArrowIso e) ⟨j, hj, k⟩ = Cells.ι (c := c) ⟨j, hj, k⟩ ≫ e.hom.right :=
  (Category.assoc _ _ _).symm

/-- Variant of `ofArrowIso_cells_ι` for an arbitrary cell, stated through
`ofArrowIsoCellsEquiv`. -/
@[reassoc]
lemma ofArrowIso_cells_ι' (γ : (c.ofArrowIso e).Cells) :
    γ.ι = (c.ofArrowIsoCellsEquiv e γ).ι ≫ e.hom.right :=
  c.ofArrowIso_cells_ι e γ.j γ.hj γ.k

end OfArrowIso

section ReindexCellTypes

variable {α' : J → Type t'} {A' B' : (j : J) → α' j → C}
  (basicCell' : (j : J) → (i' : α' j) → A' j i' ⟶ B' j i')
  (a : (j : J) → α j → α' j)
  (ha : ∀ j i, Arrow.mk (basicCell j i) ≅ Arrow.mk (basicCell' j (a j i)))

/-- Replace the basic cells of a relative cell complex along arrow isomorphisms `ha`. The stages
and cell index types are unchanged; each cell inclusion is precomposed with the inverse target
isomorphism. -/
@[expose] def reindexCellTypes : RelativeCellComplex.{w} basicCell' f :=
  .mk c.toTransfiniteCompositionOfShape fun j hj ↦
    (c.attachCells j hj).reindexCellTypes (basicCell' j) (a j) (ha j)

/-- The cells of `c.reindexCellTypes basicCell' a ha` are the cells of `c`. -/
@[expose] def reindexCellTypesCellsEquiv :
    (c.reindexCellTypes basicCell' a ha).Cells ≃ c.Cells where
  toFun γ := ⟨γ.j, γ.hj, γ.k⟩
  invFun γ := ⟨γ.j, γ.hj, γ.k⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma reindexCellTypesCellsEquiv_apply_j (γ : (c.reindexCellTypes basicCell' a ha).Cells) :
    (c.reindexCellTypesCellsEquiv basicCell' a ha γ).j = γ.j := (rfl)

@[simp]
lemma reindexCellTypesCellsEquiv_symm_apply_j (γ : c.Cells) :
    ((c.reindexCellTypesCellsEquiv basicCell' a ha).symm γ).j = γ.j := (rfl)

/-- The inclusion of a cell in `c.reindexCellTypes basicCell' a ha` is the inclusion of the
corresponding cell of `c` precomposed with the inverse target isomorphism. -/
@[simp, reassoc]
lemma reindexCellTypes_cells_ι (j : J) (hj : ¬IsMax j) (k : (c.attachCells j hj).ι) :
    Cells.ι (c := c.reindexCellTypes basicCell' a ha) ⟨j, hj, k⟩ =
      Arrow.rightFunc.map (ha j ((c.attachCells j hj).π k)).inv ≫
        Cells.ι (c := c) ⟨j, hj, k⟩ :=
  ((AttachCells.reindexCellTypes_cell (c.attachCells j hj) (basicCell' j) (a j) (ha j) k) =≫
    _).trans (Category.assoc _ _ _)

/-- Variant of `reindexCellTypes_cells_ι` for an arbitrary cell, stated through
`reindexCellTypesCellsEquiv`. -/
@[reassoc]
lemma reindexCellTypes_cells_ι' (γ : (c.reindexCellTypes basicCell' a ha).Cells) :
    γ.ι = Arrow.rightFunc.map (ha γ.j (c.reindexCellTypesCellsEquiv basicCell' a ha γ).i).inv ≫
      (c.reindexCellTypesCellsEquiv basicCell' a ha γ).ι :=
  c.reindexCellTypes_cells_ι basicCell' a ha γ.j γ.hj γ.k

end ReindexCellTypes

end RelativeCellComplex

end HomotopicalAlgebra
