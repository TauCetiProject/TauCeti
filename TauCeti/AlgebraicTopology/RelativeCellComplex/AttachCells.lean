/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

/-!
# Cell attachments: empty, functorial, and reindexed attachments

In a category with an initial object, an isomorphism `f : X₁ ⟶ X₂` is obtained by attaching an
empty family of cells (`HomotopicalAlgebra.AttachCells.ofIsIso`): both empty coproducts are the
initial object, and the square formed by its identity and `f` is a pushout because both vertical
maps are isomorphisms. This fills the stages of a relative cell complex at which nothing is
attached, for instance when all cells are attached at a single stage.

A colimit-preserving functor carries cell attachments to cell attachments
(`HomotopicalAlgebra.AttachCells.map`), preserving the cell index type and mapping each cell
inclusion (`HomotopicalAlgebra.AttachCells.map_cell`), and reindexing cell types along arrow
isomorphisms precomposes each cell inclusion with the inverse target isomorphism
(`HomotopicalAlgebra.AttachCells.reindexCellTypes_cell`).

## References

* M. Hovey, *Model Categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 2.1.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990.
-/

public section

open CategoryTheory Limits

universe w t t' v v' u u'

namespace HomotopicalAlgebra.AttachCells

section OfIsIso

variable {C : Type u} [Category.{v} C] [HasInitial C]
  {α : Type*} {A B : α → C} (g : ∀ a, A a ⟶ B a) {X₁ X₂ : C} (f : X₁ ⟶ X₂) [IsIso f]

/-- An isomorphism is obtained by attaching no cells. -/
noncomputable def ofIsIso : AttachCells.{w} g f where
  ι := PEmpty.{w + 1}
  π := PEmpty.elim
  cofan₁ := Cofan.mk (⊥_ C) fun i ↦ i.elim
  cofan₂ := Cofan.mk (⊥_ C) fun i ↦ i.elim
  isColimit₁ := isColimitChangeEmptyCocone C initialIsInitial _ (Iso.refl _)
  isColimit₂ := isColimitChangeEmptyCocone C initialIsInitial _ (Iso.refl _)
  m := 𝟙 _
  hm i := i.elim
  g₁ := initial.to X₁
  g₂ := initial.to X₂
  -- Both vertical maps, `𝟙 (⊥_ C)` and `f`, are isomorphisms.
  isPushout := IsPushout.of_vert_isIso ⟨initial.hom_ext _ _⟩

/-- No cells are attached in `AttachCells.ofIsIso`. -/
instance : IsEmpty (ofIsIso.{w} g f).ι :=
  ⟨fun i ↦ i.elim⟩

end OfIsIso

section MapAndReindex

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {α : Type t} {A B : α → C} {g : ∀ a, A a ⟶ B a} {X₁ X₂ : C} {f : X₁ ⟶ X₂}
  (c : AttachCells.{w} g f)

/-- A functor preserving the relevant coproducts and pushout sends a cell attachment to a cell
attachment with the same cell index type and mapped basic cells. -/
noncomputable def map (F : C ⥤ D)
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

/-- The cell indices of `c.map F` identify with those of `c`. -/
def mapEquiv (F : C ⥤ D)
    [PreservesColimit (Discrete.functor fun i ↦ A (c.π i)) F]
    [PreservesColimit (Discrete.functor fun i ↦ B (c.π i)) F]
    [PreservesColimit (span c.g₁ c.m) F] :
    (c.map F).ι ≃ c.ι :=
  Equiv.refl _

/-- The basic-cell indexing map of `c.map F` agrees with that of `c` under `mapEquiv`. -/
@[simp]
lemma map_π (F : C ⥤ D)
    [PreservesColimit (Discrete.functor fun i ↦ A (c.π i)) F]
    [PreservesColimit (Discrete.functor fun i ↦ B (c.π i)) F]
    [PreservesColimit (span c.g₁ c.m) F] (i : (c.map F).ι) :
    (c.map F).π i = c.π (c.mapEquiv F i) :=
  (rfl)

private lemma map_cofan₂_inj (F : C ⥤ D)
    [PreservesColimit (Discrete.functor fun i ↦ A (c.π i)) F]
    [PreservesColimit (Discrete.functor fun i ↦ B (c.π i)) F]
    [PreservesColimit (span c.g₁ c.m) F] (i : (c.map F).ι) :
    (c.map F).cofan₂.inj i =
      eqToHom (congrArg (fun a ↦ F.obj (B a)) (c.map_π F i)) ≫
        F.map (c.cofan₂.inj (c.mapEquiv F i)) :=
  (Category.id_comp _).symm.trans
    (congrArg (· ≫ F.map (c.cofan₂.inj (c.mapEquiv F i)))
      (eqToHom_refl (F.obj (B (c.π (c.mapEquiv F i)))) rfl).symm)

private lemma map_g₂ (F : C ⥤ D)
    [PreservesColimit (Discrete.functor fun i ↦ A (c.π i)) F]
    [PreservesColimit (Discrete.functor fun i ↦ B (c.π i)) F]
    [PreservesColimit (span c.g₁ c.m) F] :
    (c.map F).g₂ = F.map c.g₂ :=
  rfl

/-- The inclusion of a cell in `c.map F` is `F.map` of the original cell inclusion. -/
@[simp, reassoc]
lemma map_cell (F : C ⥤ D)
    [PreservesColimit (Discrete.functor fun i ↦ A (c.π i)) F]
    [PreservesColimit (Discrete.functor fun i ↦ B (c.π i)) F]
    [PreservesColimit (span c.g₁ c.m) F] (i : (c.map F).ι) :
    (c.map F).cell i =
      eqToHom (congrArg (fun a ↦ F.obj (B a)) (c.map_π F i)) ≫
        F.map (c.cell (c.mapEquiv F i)) := by
  rw [AttachCells.cell, AttachCells.cell, map_cofan₂_inj, map_g₂]
  dsimp only [map]
  rw [Category.assoc, F.map_comp]

/-- The inclusion of a cell after reindexing cell types is the original cell inclusion precomposed
with the inverse target isomorphism. -/
@[simp, reassoc]
lemma reindexCellTypes_cell {α' : Type t'} {A' B' : α' → C} (g' : ∀ i', A' i' ⟶ B' i')
    (a : α → α') (ha : ∀ i, Arrow.mk (g i) ≅ Arrow.mk (g' (a i))) (i : c.ι) :
    (c.reindexCellTypes g' a ha).cell i =
      Arrow.rightFunc.map (ha (c.π i)).inv ≫ c.cell i :=
  Category.assoc _ _ _

end MapAndReindex

end HomotopicalAlgebra.AttachCells
