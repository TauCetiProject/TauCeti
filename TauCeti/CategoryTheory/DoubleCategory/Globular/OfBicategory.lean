/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import TauCeti.CategoryTheory.DoubleCategory.Bicategory
public import TauCeti.CategoryTheory.PathCategory.Basic

/-!
# The globular double category of a strict bicategory

A strict bicategory can be regarded as a double category with no vertical generating
arrows. Vertical boundaries are paths in the empty quiver, so every cell is globular.
The horizontal arrows and cells retain the original 1-cells and 2-cells. Horizontal
pasting is whiskering and vertical composition; vertical pasting is 2-cell composition.

This is the double-category presentation of a strict 2-category used for implicit
2-categories, whose horizontal arrows are free paths. Empty vertical boundaries do not
require a chosen vertical identity generator.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; Definitions 2.1 and 3.1.
-/

public section

universe w v u

namespace TauCeti.StrictDoubleCategory

open CategoryTheory
open scoped Bicategory

namespace GlobularDouble

/-- Mathlib's empty quiver, explicitly supplied on the original objects. The type annotation
keeps the two edge structures separate without unfolding the `Quiver.Empty` object synonym. -/
abbrev emptyQuiver (B : Type u) : Quiver.{u} B := Quiver.emptyQuiver B

variable (B : Type u) [Bicategory.{w, v} B]

/-- Cells in the empty-vertical presentation are original 2-cells. The empty paths force
matching endpoints without increasing the universe of cells. -/
private def Cell {a b c d : B} (p : a ⟶ b) (q : c ⟶ d)
    (l : @Quiver.Path B (emptyQuiver B) a c)
    (r : @Quiver.Path B (emptyQuiver B) b d) : Type w := by
  cases l with
  | nil =>
    cases r with
    | nil => exact p ⟶ q
    | cons _ f => exact f.elim
  | cons _ f => exact f.elim

variable {B}

private def hId {a b : B} (f : @Quiver.Path B (emptyQuiver B) a b) :
    Cell B (𝟙 a) (𝟙 b) f f := by
  cases f with
  | nil => exact 𝟙 (𝟙 a)
  | cons _ f => exact f.elim

private def hComp {a b c d e f : B} {p : a ⟶ b} {q : b ⟶ c}
    {r : d ⟶ e} {t : e ⟶ f}
    {l : @Quiver.Path B (emptyQuiver B) a d}
    {m : @Quiver.Path B (emptyQuiver B) b e}
    {n : @Quiver.Path B (emptyQuiver B) c f}
    (α : Cell B p r l m) (β : Cell B q t m n) : Cell B (p ≫ q) (r ≫ t) l n := by
  cases l with
  | cons _ f => exact f.elim
  | nil =>
    cases m with
    | cons _ f => exact f.elim
    | nil =>
      cases n with
      | cons _ f => exact f.elim
      | nil => exact α ▷ q ≫ r ◁ β

private def vComp {a b c d e f : B} {p : a ⟶ b} {q : c ⟶ d} {r : e ⟶ f}
    {l : @Quiver.Path B (emptyQuiver B) a c}
    {m : @Quiver.Path B (emptyQuiver B) b d}
    {n : @Quiver.Path B (emptyQuiver B) c e}
    {t : @Quiver.Path B (emptyQuiver B) d f}
    (α : Cell B p q l m) (β : Cell B q r n t) :
    Cell B p r (@Quiver.Path.comp B (emptyQuiver B) _ _ _ l n)
      (@Quiver.Path.comp B (emptyQuiver B) _ _ _ m t) := by
  cases l with
  | cons _ f => exact f.elim
  | nil =>
    cases m with
    | cons _ f => exact f.elim
    | nil =>
      cases n with
      | cons _ f => exact f.elim
      | nil =>
        cases t with
        | cons _ f => exact f.elim
        | nil => exact α ≫ β

variable (B) [Bicategory.Strict B]

/-- The operations in the globular double presentation of a strict bicategory. -/
private def struct : DoubleCategoryStruct.{w} B
    (StrictBicategory.category B) (pathCategory B (emptyQuiver B)) where
  Cell := Cell B
  hId := hId
  vId p := 𝟙 p
  hComp := hComp
  vComp := vComp

variable {B}

private theorem cast_eq {a b : B} {p p' q q' : a ⟶ b}
    (hp : p = p') (hq : q = q') (α : p ⟶ q) :
    DoubleCategoryStruct.Cell.cast (D := struct B) hp hq (l := @Quiver.Path.nil B (emptyQuiver B) a)
      (r := @Quiver.Path.nil B (emptyQuiver B) b) rfl rfl α =
      eqToHom hp.symm ≫ α ≫ eqToHom hq := by
  subst hp hq
  simp only [DoubleCategoryStruct.Cell.cast, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

private theorem hComp_assoc {a b c d e f g k : B}
    {p : a ⟶ b} {q : b ⟶ c} {r : c ⟶ d}
    {p' : e ⟶ f} {q' : f ⟶ g} {r' : g ⟶ k}
    {l : @Quiver.Path B (emptyQuiver B) a e}
    {m : @Quiver.Path B (emptyQuiver B) b f}
    {n : @Quiver.Path B (emptyQuiver B) c g}
    {t : @Quiver.Path B (emptyQuiver B) d k}
    (α : (struct B).Cell p p' l m) (β : (struct B).Cell q q' m n)
    (γ : (struct B).Cell r r' n t) :
    (struct B).hComp ((struct B).hComp α β) γ =
      ((struct B).hComp α ((struct B).hComp β γ)).cast
        (Bicategory.Strict.assoc p q r).symm (Bicategory.Strict.assoc p' q' r').symm rfl rfl := by
  cases l <;> cases m <;> cases n <;> cases t <;> try contradiction
  dsimp [struct, Cell] at α β γ
  dsimp [struct, hComp, edgeComp]
  -- Reduce the empty-boundary cell family before rewriting its transport.
  erw [cast_eq]
  simp [Bicategory.Strict.associator_eqToIso, Category.assoc]
  rfl

variable (B) in
/-- The double category associated to a strict bicategory, with empty vertical generators.
Its cells are the original 2-cells, with no quotient or additional coherence data. -/
def doubleCategory : StrictDoubleCategory.{w} B
    (StrictBicategory.category B) (pathCategory B (emptyQuiver B)) where
  toDoubleCategoryStruct := struct B
  hId_hComp {a b c d p q l r} α := by
    cases l <;> cases r <;> try contradiction
    dsimp [struct, Cell] at α
    dsimp [struct, hComp, hId, edgeId]
    -- Reduce the empty-boundary cell family before rewriting its transport.
    erw [cast_eq]
    simp [Bicategory.Strict.leftUnitor_eqToIso]
    rfl
  hComp_hId {a b c d p q l r} α := by
    cases l <;> cases r <;> try contradiction
    dsimp [struct, Cell] at α
    dsimp [struct, hComp, hId, edgeId]
    -- Reduce the empty-boundary cell family before rewriting its transport.
    erw [cast_eq]
    simp [Bicategory.Strict.rightUnitor_eqToIso]
    rfl
  vId_vComp {a b c d p q l r} α := by
    cases l <;> cases r <;> try contradiction
    exact Category.id_comp α
  vComp_vId {a b c d p q l r} α := by
    cases l <;> cases r <;> try contradiction
    exact Category.comp_id α
  hComp_assoc := hComp_assoc
  vComp_assoc {a b c d e f g k p q r t l m n l' m' n'} α β γ := by
    cases l <;> cases m <;> cases n <;> cases l' <;> cases m' <;> cases n' <;> try contradiction
    exact Category.assoc α β γ
  interchange {a b c d e f g k i p q r t x y l m n l' m' n'} α β γ δ := by
    cases l <;> cases m <;> cases n <;> cases l' <;> cases m' <;> cases n' <;> try contradiction
    dsimp [struct, Cell] at α β γ δ
    exact ((Functor.uncurry.obj (Bicategory.precomposing a b c)).map_comp
      (Prod.mkHom α β) (Prod.mkHom γ δ)).symm
  hId_comp f g := by
    cases f <;> cases g <;> try contradiction
    exact (Category.id_comp _).symm
  vId_comp f g := by
    dsimp [struct, hComp, edgeComp]
    simp
    rfl
  hId_id _ := rfl

variable (B) in
/-- At empty vertical boundaries, cells are precisely the original 2-cells. -/
def cellEquiv {a b : B} (p q : a ⟶ b) :
    (doubleCategory B).Cell p q (@Quiver.Path.nil B (emptyQuiver B) a)
      (@Quiver.Path.nil B (emptyQuiver B) b) ≃ (p ⟶ q) := Equiv.refl _

variable {a b c : B}

/-- Vertical identity cells are identity 2-cells. -/
@[simp]
theorem cellEquiv_vId (p : a ⟶ b) :
    cellEquiv B p p ((doubleCategory B).vId p) = 𝟙 p := (rfl)

/-- The horizontal identity cell on an empty vertical path is the identity on the identity
1-cell. -/
@[simp]
theorem cellEquiv_hId (a : B) :
    cellEquiv B (𝟙 a) (𝟙 a)
      ((doubleCategory B).hId (@Quiver.Path.nil B (emptyQuiver B) a)) = 𝟙 (𝟙 a) := (rfl)

/-- Vertical pasting is composition of the original 2-cells. -/
@[simp]
theorem cellEquiv_vComp {p q r : a ⟶ b}
    (α : (doubleCategory B).Cell p q (@Quiver.Path.nil B (emptyQuiver B) a)
      (@Quiver.Path.nil B (emptyQuiver B) b))
    (β : (doubleCategory B).Cell q r (@Quiver.Path.nil B (emptyQuiver B) a)
      (@Quiver.Path.nil B (emptyQuiver B) b)) :
    cellEquiv B p r ((doubleCategory B).vComp α β) =
      cellEquiv B p q α ≫ cellEquiv B q r β := (rfl)

/-- Horizontal pasting is horizontal composition of the original 2-cells, in diagrammatic
order. -/
@[simp]
theorem cellEquiv_hComp {p p' : a ⟶ b} {q q' : b ⟶ c}
    (α : (doubleCategory B).Cell p p' (@Quiver.Path.nil B (emptyQuiver B) a)
      (@Quiver.Path.nil B (emptyQuiver B) b))
    (β : (doubleCategory B).Cell q q' (@Quiver.Path.nil B (emptyQuiver B) b)
      (@Quiver.Path.nil B (emptyQuiver B) c)) :
    cellEquiv B (p ≫ q) (p' ≫ q') ((doubleCategory B).hComp α β) =
      cellEquiv B p p' α ▷ q ≫ p' ◁ cellEquiv B q q' β := (rfl)

/-- Changing the horizontal boundaries corresponds to conjugating by equality 2-cells. -/
theorem cellEquiv_cast {p p' q q' : a ⟶ b} (hp : p = p') (hq : q = q')
    (α : (doubleCategory B).Cell p q (@Quiver.Path.nil B (emptyQuiver B) a)
      (@Quiver.Path.nil B (emptyQuiver B) b)) :
    cellEquiv B p' q' (α.cast hp hq rfl rfl) =
      eqToHom hp.symm ≫ cellEquiv B p q α ≫ eqToHom hq :=
  cast_eq hp hq α

/-- The hom-category of the double presentation recovers the original hom-category, with
an explicit inverse on both 1-cells and 2-cells. -/
def homEquivalence (a b : B) : (doubleCategory B).HorizontalGlobular a b ≌ (a ⟶ b) where
  functor := {
    obj p := p.edge
    map α := cellEquiv B _ _ α.cell
    map_id p := cellEquiv_vId p.edge
    map_comp α β := cellEquiv_vComp α.cell β.cell }
  inverse := {
    obj p := ⟨p⟩
    map α := ⟨(cellEquiv B _ _).symm α⟩
    map_id _ := rfl
    map_comp _ _ := rfl }
  unitIso := eqToIso (by rfl)
  counitIso := Iso.refl _
  functor_unitIso_comp _ := by
    dsimp [cellEquiv, doubleCategory, struct, Cell, edgeId, pathCategory]
    exact Category.comp_id _

@[simp]
theorem homEquivalence_functor_obj (a b : B)
    (p : (doubleCategory B).HorizontalGlobular a b) :
    (homEquivalence a b).functor.obj p = p.edge := (rfl)

@[simp]
theorem homEquivalence_inverse_obj (a b : B) (p : a ⟶ b) :
    (homEquivalence a b).inverse.obj p = ⟨p⟩ := (rfl)

variable (B) in
/-- Evaluate the horizontal globular bicategory of the double presentation in the original
strict bicategory. The body is exposed so its object and 1-cell maps compute in
dependent 2-cell types. -/
@[expose]
def evaluation : StrictPseudofunctor (doubleCategory B).HorizontalBicategory B :=
  StrictPseudofunctor.mk'' {
    obj a := a.obj
    map p := p.edge
    map₂ α := cellEquiv B _ _ α.cell
    map₂_id p := cellEquiv_vId p.edge
    map₂_comp α β := cellEquiv_vComp α.cell β.cell
    map_id _ := rfl
    map_comp _ _ := rfl
    map₂_whisker_left p _ _ α := by
      rw [HorizontalBicategory.whiskerLeft_cell]
      erw [cellEquiv_hComp, cellEquiv_vId]
      simp
    map₂_whisker_right α q := by
      rw [HorizontalBicategory.whiskerRight_cell]
      erw [cellEquiv_hComp, cellEquiv_vId]
      simp }

@[simp]
theorem evaluation_obj (a : (doubleCategory B).HorizontalBicategory) :
    (evaluation B).obj a = a.obj := (rfl)

@[simp]
theorem evaluation_map {a b : (doubleCategory B).HorizontalBicategory} (p : a ⟶ b) :
    (evaluation B).map p = p.edge := (rfl)

@[simp]
theorem evaluation_map₂ {a b : (doubleCategory B).HorizontalBicategory} {p q : a ⟶ b}
    (α : p ⟶ q) :
    (evaluation B).map₂ α = cellEquiv B p.edge q.edge α.cell := (rfl)

/-- Evaluation is the explicit hom-category equivalence, so it loses no 1-cells or 2-cells. -/
theorem evaluation_mapFunctor (a b : (doubleCategory B).HorizontalBicategory) :
    (evaluation B).mapFunctor a b = (homEquivalence a.obj b.obj).functor := (rfl)

/-- The recovered horizontal globular bicategory is locally equivalent to the original one. -/
instance (a b : (doubleCategory B).HorizontalBicategory) :
    ((evaluation B).mapFunctor a b).IsEquivalence := by
  rw [evaluation_mapFunctor]
  exact (homEquivalence a.obj b.obj).isEquivalence_functor

end GlobularDouble

end TauCeti.StrictDoubleCategory
