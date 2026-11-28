/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import TauCeti.AlgebraicTopology.RelativeCellComplex.AttachCells
public import TauCeti.CategoryTheory.Limits.Preserves.Shapes.Preorder

/-!
# Functoriality and reindexing of relative cell complexes

A colimit-preserving functor carries relative cell complexes to relative cell complexes
(`HomotopicalAlgebra.RelativeCellComplex.map`), preserving the indexing of cells
(`HomotopicalAlgebra.RelativeCellComplex.mapCellsEquiv`,
`HomotopicalAlgebra.RelativeCellComplex.mapAttachCellsEquiv`) and acting on each cell inclusion by
applying the functor (`HomotopicalAlgebra.RelativeCellComplex.map_cells_ι`).

This file also extends Mathlib's arrow-isomorphism transport and cell-type reindexing from
individual cell attachments and transfinite compositions to relative cell complexes:
* `HomotopicalAlgebra.RelativeCellComplex.ofArrowIso`: transports a relative cell complex along an
  isomorphism of arrows `Arrow.mk f ≅ Arrow.mk f'`, composing each cell inclusion with the target
  isomorphism.
* `HomotopicalAlgebra.RelativeCellComplex.reindexCellTypes`: replaces the family of basic cells
  along arrow isomorphisms, precomposing each cell inclusion with the inverse of the corresponding
  target isomorphism.

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
The stages are the images of the stages of `c`, and at each step `(c.map F).attachCells j hj` has
the same cell index type `.ι` as `c.attachCells j hj`, while the attachment maps are transported by
`F`. -/
noncomputable def map :
    RelativeCellComplex.{w} (fun j i ↦ F.map (basicCell j i)) (F.map f) :=
  .mk (c.toTransfiniteCompositionOfShape.map F) fun j hj ↦ (c.attachCells j hj).map F

/-- The stage functor of `c.map F` is `c.F ⋙ F`. -/
@[simp]
lemma map_F : (c.map F).F = c.F ⋙ F := by
  simp [map]

/-- The `j`-th stage inclusion of `c.map F` into `F.obj Y` is `F.map (c.incl.app j)`, aligned
along `c.map_F F`. -/
@[simp, reassoc]
lemma map_incl_app (j : J) :
    (c.map F).incl.app j =
      eqToHom (congrArg (fun G ↦ G.obj j) (c.map_F F)) ≫ F.map (c.incl.app j) := by
  suffices (c.map F).incl.app j = F.map (c.incl.app j) by
    rw [this]
    change F.map (c.incl.app j) =
      eqToHom (rfl : F.obj (c.F.obj j) = F.obj (c.F.obj j)) ≫ F.map (c.incl.app j)
    simp
  simp [map]
  rfl

/-- The initial stage isomorphism of `c.map F` is `F.mapIso c.isoBot`, aligned along
`c.map_F F`. -/
@[simp]
lemma map_isoBot :
    (c.map F).isoBot =
      eqToIso (congrArg (fun G ↦ G.obj ⊥) (c.map_F F)) ≪≫ F.mapIso c.isoBot := by
  ext
  change F.map c.isoBot.hom =
    (eqToIso (rfl : F.obj (c.F.obj ⊥) = F.obj (c.F.obj ⊥))).hom ≫ F.map c.isoBot.hom
  simp

/-- The attachment indices at step `j` of `c.map F` identify with those of `c`. -/
def mapAttachCellsEquiv (j : J) (hj : ¬IsMax j) :
    ((c.map F).attachCells j hj).ι ≃ (c.attachCells j hj).ι :=
  (c.attachCells j hj).mapEquiv F

/-- The basic-cell indexing map at step `j` of `c.map F` agrees with that of `c` under
`mapAttachCellsEquiv`. -/
@[simp]
lemma mapAttachCellsEquiv_π (j : J) (hj : ¬IsMax j)
    (k : ((c.map F).attachCells j hj).ι) :
    ((c.map F).attachCells j hj).π k =
      (c.attachCells j hj).π (c.mapAttachCellsEquiv F j hj k) :=
  (c.attachCells j hj).map_π F k

/-- The cells of `c.map F` are in canonical bijection with the cells of `c`. -/
def mapCellsEquiv : (c.map F).Cells ≃ c.Cells where
  toFun γ := ⟨γ.j, γ.hj, c.mapAttachCellsEquiv F γ.j γ.hj γ.k⟩
  invFun γ := ⟨γ.j, γ.hj, (c.mapAttachCellsEquiv F γ.j γ.hj).symm γ.k⟩
  left_inv γ := by cases γ; simp
  right_inv γ := by cases γ; simp

@[simp]
lemma mapCellsEquiv_apply_j (γ : (c.map F).Cells) : (c.mapCellsEquiv F γ).j = γ.j := by rfl

@[simp]
lemma mapCellsEquiv_symm_apply_j (γ : c.Cells) : ((c.mapCellsEquiv F).symm γ).j = γ.j := by rfl

@[simp]
lemma mapCellsEquiv_mk (j : J) (hj : ¬IsMax j) (k : ((c.map F).attachCells j hj).ι) :
    c.mapCellsEquiv F ⟨j, hj, k⟩ = ⟨j, hj, c.mapAttachCellsEquiv F j hj k⟩ := by
  rfl

@[simp]
lemma mapCellsEquiv_symm_mk (j : J) (hj : ¬IsMax j) (k : (c.attachCells j hj).ι) :
    (c.mapCellsEquiv F).symm ⟨j, hj, k⟩ = ⟨j, hj, (c.mapAttachCellsEquiv F j hj).symm k⟩ := by
  rfl

/-- The inclusion of a cell in `c.map F` is `F.map` of the inclusion of the corresponding cell of
`c`. -/
@[simp, reassoc]
lemma map_cells_ι (j : J) (hj : ¬IsMax j) (k : ((c.map F).attachCells j hj).ι) :
    Cells.ι (c := c.map F) ⟨j, hj, k⟩ =
      eqToHom (congrArg (fun i ↦ F.obj (B j i)) (c.mapAttachCellsEquiv_π F j hj k)) ≫
        F.map (Cells.ι (c := c) ⟨j, hj, c.mapAttachCellsEquiv F j hj k⟩) := by
  let k' : ((c.attachCells j hj).map F).ι := k
  have h1 : Cells.ι (c := c.map F) ⟨j, hj, k⟩ =
      ((c.attachCells j hj).map F).cell k' ≫ F.map (c.incl.app (Order.succ j)) := by
    change ((c.attachCells j hj).map F).cell k' ≫ (c.map F).incl.app (Order.succ j) = _
    simp [map]
  rw [h1, AttachCells.map_cell, Category.assoc, ← F.map_comp]
  rfl

end Map

section OfArrowIso

variable {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f')

/-- Transport a relative cell complex along an isomorphism of arrows `Arrow.mk f ≅ Arrow.mk f'`.
The functor of stages and cell attachments are unchanged; the colimit cocone is postcomposed with
the target isomorphism. -/
def ofArrowIso : RelativeCellComplex.{w} basicCell f' :=
  .mk (c.toTransfiniteCompositionOfShape.ofArrowIso e) c.attachCells

/-- The stage functor of `c.ofArrowIso e` is `c.F`. -/
@[simp]
lemma ofArrowIso_F : (c.ofArrowIso e).F = c.F := by
  simp [ofArrowIso]

/-- The `j`-th stage inclusion of `c.ofArrowIso e` is `c.incl.app j ≫ e.hom.right`, aligned along
`c.ofArrowIso_F e`. -/
@[simp, reassoc]
lemma ofArrowIso_incl_app (j : J) :
    (c.ofArrowIso e).incl.app j =
      eqToHom (congrArg (fun G ↦ G.obj j) (c.ofArrowIso_F e)) ≫ c.incl.app j ≫ e.hom.right := by
  change c.incl.app j ≫ e.hom.right =
    eqToHom (rfl : c.F.obj j = c.F.obj j) ≫ c.incl.app j ≫ e.hom.right
  simp

/-- The initial stage isomorphism of `c.ofArrowIso e` is `c.isoBot ≪≫ Arrow.leftFunc.mapIso e`,
aligned along `c.ofArrowIso_F e`. -/
@[simp]
lemma ofArrowIso_isoBot :
    (c.ofArrowIso e).isoBot =
      eqToIso (congrArg (fun G ↦ G.obj ⊥) (c.ofArrowIso_F e)) ≪≫
        c.isoBot ≪≫ Arrow.leftFunc.mapIso e := by
  ext
  change c.isoBot.hom ≫ e.hom.left =
    (eqToIso (rfl : c.F.obj ⊥ = c.F.obj ⊥)).hom ≫ c.isoBot.hom ≫ e.hom.left
  simp

/-- The attachment indices at step `j` of `c.ofArrowIso e` identify with those of `c`. -/
def ofArrowIsoAttachCellsEquiv (j : J) (hj : ¬IsMax j) :
    ((c.ofArrowIso e).attachCells j hj).ι ≃ (c.attachCells j hj).ι :=
  Equiv.refl _

/-- The basic-cell indexing map at step `j` of `c.ofArrowIso e` agrees with that of `c` under
`ofArrowIsoAttachCellsEquiv`. -/
@[simp]
lemma ofArrowIsoAttachCellsEquiv_π (j : J) (hj : ¬IsMax j)
    (k : ((c.ofArrowIso e).attachCells j hj).ι) :
    ((c.ofArrowIso e).attachCells j hj).π k =
      (c.attachCells j hj).π (c.ofArrowIsoAttachCellsEquiv e j hj k) :=
  (rfl)

/-- The cells of `c.ofArrowIso e` are in canonical bijection with the cells of `c`. -/
def ofArrowIsoCellsEquiv : (c.ofArrowIso e).Cells ≃ c.Cells where
  toFun γ := ⟨γ.j, γ.hj, c.ofArrowIsoAttachCellsEquiv e γ.j γ.hj γ.k⟩
  invFun γ := ⟨γ.j, γ.hj, (c.ofArrowIsoAttachCellsEquiv e γ.j γ.hj).symm γ.k⟩
  left_inv _ := (rfl)
  right_inv _ := (rfl)

@[simp]
lemma ofArrowIsoCellsEquiv_apply_j (γ : (c.ofArrowIso e).Cells) :
    (c.ofArrowIsoCellsEquiv e γ).j = γ.j := (rfl)

@[simp]
lemma ofArrowIsoCellsEquiv_symm_apply_j (γ : c.Cells) :
    ((c.ofArrowIsoCellsEquiv e).symm γ).j = γ.j := (rfl)

@[simp]
lemma ofArrowIsoCellsEquiv_mk (j : J) (hj : ¬IsMax j)
    (k : ((c.ofArrowIso e).attachCells j hj).ι) :
    c.ofArrowIsoCellsEquiv e ⟨j, hj, k⟩ = ⟨j, hj, c.ofArrowIsoAttachCellsEquiv e j hj k⟩ :=
  (rfl)

@[simp]
lemma ofArrowIsoCellsEquiv_symm_mk (j : J) (hj : ¬IsMax j) (k : (c.attachCells j hj).ι) :
    (c.ofArrowIsoCellsEquiv e).symm ⟨j, hj, k⟩ =
      ⟨j, hj, (c.ofArrowIsoAttachCellsEquiv e j hj).symm k⟩ :=
  (rfl)

/-- The inclusion of a cell in `c.ofArrowIso e` is the inclusion of the corresponding cell of `c`
followed by the target isomorphism `e.hom.right`. -/
@[simp, reassoc]
lemma ofArrowIso_cells_ι (j : J) (hj : ¬IsMax j)
    (k : ((c.ofArrowIso e).attachCells j hj).ι) :
    Cells.ι (c := c.ofArrowIso e) ⟨j, hj, k⟩ =
      eqToHom (congrArg (fun i ↦ B j i) (c.ofArrowIsoAttachCellsEquiv_π e j hj k)) ≫
        Cells.ι (c := c) ⟨j, hj, c.ofArrowIsoAttachCellsEquiv e j hj k⟩ ≫ e.hom.right := by
  dsimp only [Cells.ι, ofArrowIso, ofArrowIsoAttachCellsEquiv] at k ⊢
  change (c.attachCells j hj).cell k ≫ c.incl.app (Order.succ j) ≫ e.hom.right =
    eqToHom (rfl : B j ((c.attachCells j hj).π k) = B j ((c.attachCells j hj).π k)) ≫
      ((c.attachCells j hj).cell k ≫ c.incl.app (Order.succ j)) ≫ e.hom.right
  simp

end OfArrowIso

section ReindexCellTypes

variable {α' : J → Type t'} {A' B' : (j : J) → α' j → C}
  (basicCell' : (j : J) → (i' : α' j) → A' j i' ⟶ B' j i')
  (a : (j : J) → α j → α' j)
  (ha : ∀ j i, Arrow.mk (basicCell j i) ≅ Arrow.mk (basicCell' j (a j i)))

/-- Replace the basic cells of a relative cell complex along arrow isomorphisms `ha`. The stages
and cell index types are unchanged; each cell inclusion is precomposed with the inverse target
isomorphism. -/
def reindexCellTypes : RelativeCellComplex.{w} basicCell' f :=
  .mk c.toTransfiniteCompositionOfShape fun j hj ↦
    (c.attachCells j hj).reindexCellTypes (basicCell' j) (a j) (ha j)

/-- The stage functor of `c.reindexCellTypes basicCell' a ha` is `c.F`. -/
@[simp]
lemma reindexCellTypes_F : (c.reindexCellTypes basicCell' a ha).F = c.F := by
  simp [reindexCellTypes]

/-- The `j`-th stage inclusion of `c.reindexCellTypes basicCell' a ha` is `c.incl.app j`, aligned
along `c.reindexCellTypes_F`. -/
@[simp, reassoc]
lemma reindexCellTypes_incl_app (j : J) :
    (c.reindexCellTypes basicCell' a ha).incl.app j =
      eqToHom (congrArg (fun G ↦ G.obj j) (c.reindexCellTypes_F basicCell' a ha)) ≫
        c.incl.app j := by
  change c.incl.app j = eqToHom (rfl : c.F.obj j = c.F.obj j) ≫ c.incl.app j
  simp

/-- The initial stage isomorphism of `c.reindexCellTypes basicCell' a ha` is `c.isoBot`, aligned
along `c.reindexCellTypes_F`. -/
@[simp]
lemma reindexCellTypes_isoBot :
    (c.reindexCellTypes basicCell' a ha).isoBot =
      eqToIso (congrArg (fun G ↦ G.obj ⊥) (c.reindexCellTypes_F basicCell' a ha)) ≪≫
        c.isoBot := by
  ext
  change c.isoBot.hom = (eqToIso (rfl : c.F.obj ⊥ = c.F.obj ⊥)).hom ≫ c.isoBot.hom
  simp

/-- The attachment indices at step `j` of `c.reindexCellTypes basicCell' a ha` identify with those
of `c`. -/
def reindexCellTypesAttachCellsEquiv (j : J) (hj : ¬IsMax j) :
    ((c.reindexCellTypes basicCell' a ha).attachCells j hj).ι ≃ (c.attachCells j hj).ι :=
  Equiv.refl _

/-- The basic-cell indexing map at step `j` of `c.reindexCellTypes basicCell' a ha` agrees with
`a j` composed with the indexing map of `c` under `reindexCellTypesAttachCellsEquiv`. -/
@[simp]
lemma reindexCellTypesAttachCellsEquiv_π (j : J) (hj : ¬IsMax j)
    (k : ((c.reindexCellTypes basicCell' a ha).attachCells j hj).ι) :
    ((c.reindexCellTypes basicCell' a ha).attachCells j hj).π k =
      a j ((c.attachCells j hj).π
        (c.reindexCellTypesAttachCellsEquiv basicCell' a ha j hj k)) :=
  (rfl)

/-- The cells of `c.reindexCellTypes basicCell' a ha` are in canonical bijection with the cells of
`c`. -/
def reindexCellTypesCellsEquiv :
    (c.reindexCellTypes basicCell' a ha).Cells ≃ c.Cells where
  toFun γ := ⟨γ.j, γ.hj, c.reindexCellTypesAttachCellsEquiv basicCell' a ha γ.j γ.hj γ.k⟩
  invFun γ := ⟨γ.j, γ.hj, (c.reindexCellTypesAttachCellsEquiv basicCell' a ha γ.j γ.hj).symm γ.k⟩
  left_inv _ := (rfl)
  right_inv _ := (rfl)

@[simp]
lemma reindexCellTypesCellsEquiv_apply_j (γ : (c.reindexCellTypes basicCell' a ha).Cells) :
    (c.reindexCellTypesCellsEquiv basicCell' a ha γ).j = γ.j := (rfl)

@[simp]
lemma reindexCellTypesCellsEquiv_symm_apply_j (γ : c.Cells) :
    ((c.reindexCellTypesCellsEquiv basicCell' a ha).symm γ).j = γ.j := (rfl)

@[simp]
lemma reindexCellTypesCellsEquiv_mk (j : J) (hj : ¬IsMax j)
    (k : ((c.reindexCellTypes basicCell' a ha).attachCells j hj).ι) :
    c.reindexCellTypesCellsEquiv basicCell' a ha ⟨j, hj, k⟩ =
      ⟨j, hj, c.reindexCellTypesAttachCellsEquiv basicCell' a ha j hj k⟩ :=
  (rfl)

@[simp]
lemma reindexCellTypesCellsEquiv_symm_mk (j : J) (hj : ¬IsMax j) (k : (c.attachCells j hj).ι) :
    (c.reindexCellTypesCellsEquiv basicCell' a ha).symm ⟨j, hj, k⟩ =
      ⟨j, hj, (c.reindexCellTypesAttachCellsEquiv basicCell' a ha j hj).symm k⟩ :=
  (rfl)

/-- The inclusion of a cell in `c.reindexCellTypes basicCell' a ha` is the inclusion of the
corresponding cell of `c` precomposed with the inverse target isomorphism. -/
@[simp, reassoc]
lemma reindexCellTypes_cells_ι (j : J) (hj : ¬IsMax j)
    (k : ((c.reindexCellTypes basicCell' a ha).attachCells j hj).ι) :
    Cells.ι (c := c.reindexCellTypes basicCell' a ha) ⟨j, hj, k⟩ =
      eqToHom (congrArg (fun i' ↦ B' j i')
          (c.reindexCellTypesAttachCellsEquiv_π basicCell' a ha j hj k)) ≫
        Arrow.rightFunc.map (ha j ((c.attachCells j hj).π
          (c.reindexCellTypesAttachCellsEquiv basicCell' a ha j hj k))).inv ≫
          Cells.ι (c := c)
            ⟨j, hj, c.reindexCellTypesAttachCellsEquiv basicCell' a ha j hj k⟩ := by
  let k' : (c.attachCells j hj).ι := k
  have h1 : Cells.ι (c := c.reindexCellTypes basicCell' a ha) ⟨j, hj, k⟩ =
      (Arrow.rightFunc.map (ha j ((c.attachCells j hj).π k')).inv ≫
        (c.attachCells j hj).cell k') ≫ c.incl.app (Order.succ j) := by
    change ((c.attachCells j hj).reindexCellTypes (basicCell' j) (a j) (ha j)).cell k' ≫
        c.incl.app (Order.succ j) = _
    rw [AttachCells.reindexCellTypes_cell]
    rfl
  rw [h1, Category.assoc]
  change Arrow.rightFunc.map (ha j ((c.attachCells j hj).π k')).inv ≫
      (c.attachCells j hj).cell k' ≫ c.incl.app (Order.succ j) =
    eqToHom (rfl : B' j (a j ((c.attachCells j hj).π k')) =
      B' j (a j ((c.attachCells j hj).π k'))) ≫
      Arrow.rightFunc.map (ha j ((c.attachCells j hj).π k')).inv ≫
        (c.attachCells j hj).cell k' ≫ c.incl.app (Order.succ j)
  simp

end ReindexCellTypes

end RelativeCellComplex

end HomotopicalAlgebra
