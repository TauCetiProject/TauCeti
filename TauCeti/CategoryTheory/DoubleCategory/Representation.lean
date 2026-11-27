/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Equivalence
public import TauCeti.CategoryTheory.DoubleCategory.Implicit

/-!
# Composition of represented horizontal generators

The horizontal generators of a path double category form hom-categories: morphisms are
globular cells between singleton paths. A horizontal representation gives an explicit
equivalence between these categories and the categories of all horizontal paths, by conjugating
each globular cell with the chosen recursive path comparisons.

Horizontal pasting then descends to a composition bifunctor on generators. Its object map is
the chosen binary composite, and its morphism map pastes two globular cells and changes the
top and bottom paths by the binary comparison isomorphisms. The binary comparisons form a
natural isomorphism between path pasting and the singleton image of this bifunctor. Thus the
construction supplies the local composition operations, including interchange, from which
the bicategory structure on generators is derived.

All constructions use only horizontal representations. Applying them to the transpose gives
the corresponding vertical constructions without requiring horizontal and vertical generators
to have the same universe.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; Definitions 3.1–3.3 and Remark 3.5.
-/

public section

universe s u h v

namespace TauCeti.StrictDoubleCategory

open CategoryTheory

variable {O : Type u} {H : Quiver.{h} O} {V : Category.{v} O}
  (D : StrictDoubleCategory.{s} O (pathCategory O H) V)

/-- Horizontal generators from `a` to `b`, with globular cells between their singleton paths
as morphisms. This is Mathlib's induced category, so its inclusion is fully faithful. -/
abbrev HorizontalGenerator (a b : O) :=
  InducedCategory (D.HorizontalGlobular a b)
    (fun f : @Quiver.Hom O H a b ↦ ⟨@Quiver.Hom.toPath O H a b f⟩)

/-- Include horizontal generators into horizontal paths by taking singleton paths. -/
abbrev singletonFunctor (a b : O) : D.HorizontalGenerator a b ⥤ D.HorizontalGlobular a b :=
  inducedFunctor _

namespace HorizontalRepresentation

variable {D} (R : D.HorizontalRepresentation)

/-- Replace paths by their chosen representing generators and conjugate globular cells by
the recursive comparison isomorphisms. Its body is exposed so morphism formulas can
compute the source and target representing generators. -/
@[expose]
def repFunctor (a b : O) : D.HorizontalGlobular a b ⥤ D.HorizontalGenerator a b where
  obj p := R.rep p.edge
  map {p q} α := InducedCategory.homMk
    ((R.repIso p.edge).inv ≫ α ≫ (R.repIso q.edge).hom)
  map_id p := by
    apply InducedCategory.hom_ext
    simp
  map_comp α β := by
    apply InducedCategory.hom_ext
    simp

@[simp]
theorem repFunctor_obj {a b : O} (p : D.HorizontalGlobular a b) :
    (R.repFunctor a b).obj p = R.rep p.edge :=
  (rfl)

@[simp]
theorem repFunctor_map_hom {a b : O} {p q : D.HorizontalGlobular a b} (α : p ⟶ q) :
    ((R.repFunctor a b).map α).hom =
      (R.repIso p.edge).inv ≫ α ≫ (R.repIso q.edge).hom :=
  (rfl)

/-- The recursive comparisons are natural in arbitrary globular cells, from each path to
the singleton of its representing generator. -/
def repComparison (a b : O) :
    𝟭 (D.HorizontalGlobular a b) ≅ R.repFunctor a b ⋙ D.singletonFunctor a b :=
  NatIso.ofComponents (fun p ↦ R.repIso p.edge) (by
    intro p q α
    simp [repFunctor])

@[simp]
theorem repComparison_hom_app {a b : O} (p : D.HorizontalGlobular a b) :
    (R.repComparison a b).hom.app p = (R.repIso p.edge).hom :=
  (rfl)

@[simp]
theorem repComparison_inv_app {a b : O} (p : D.HorizontalGlobular a b) :
    (R.repComparison a b).inv.app p = (R.repIso p.edge).inv :=
  (rfl)

/-- Representing a singleton path recovers the generator, naturally in its globular cells. -/
def singletonComparison (a b : O) :
    𝟭 (D.HorizontalGenerator a b) ≅ D.singletonFunctor a b ⋙ R.repFunctor a b :=
  NatIso.ofComponents (fun f ↦ Iso.refl f) (by
    intro f g α
    apply InducedCategory.hom_ext
    dsimp [repFunctor, Quiver.Hom.toPath]
    simp only [repIso_cons_nil, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
    exact (Category.id_comp α.hom).symm)

@[simp]
theorem singletonComparison_hom_app {a b : O} (f : D.HorizontalGenerator a b) :
    (R.singletonComparison a b).hom.app f = 𝟙 f :=
  (rfl)

@[simp]
theorem singletonComparison_inv_app {a b : O} (f : D.HorizontalGenerator a b) :
    (R.singletonComparison a b).inv.app f = 𝟙 f :=
  (rfl)

/-- Singleton inclusion and recursive representation are inverse equivalences of
hom-categories. The unit and counit use the specified comparisons, without any further choice. -/
def homEquivalence (a b : O) : D.HorizontalGenerator a b ≌ D.HorizontalGlobular a b where
  functor := D.singletonFunctor a b
  inverse := R.repFunctor a b
  unitIso := R.singletonComparison a b
  counitIso := (R.repComparison a b).symm
  functor_unitIso_comp f := by
    dsimp [singletonComparison, repComparison, NatIso.ofComponents, Quiver.Hom.toPath]
    rw [R.repIso_cons_nil f]
    exact (Category.comp_id _).trans ((D.singletonFunctor a b).map_id f)

@[simp]
theorem homEquivalence_functor (a b : O) :
    (R.homEquivalence a b).functor = D.singletonFunctor a b :=
  (rfl)

@[simp]
theorem homEquivalence_inverse (a b : O) :
    (R.homEquivalence a b).inverse = R.repFunctor a b :=
  (rfl)

instance (a b : O) : (R.repFunctor a b).Full :=
  (R.homEquivalence a b).fullyFaithfulInverse.full

instance (a b : O) : (R.repFunctor a b).Faithful :=
  (R.homEquivalence a b).fullyFaithfulInverse.faithful

/-- Paste singleton-boundary globular cells and represent the resulting two-arrow paths.
This is the horizontal composition bifunctor on generating arrows. Its body is exposed so
formulas for its morphisms can compute the chosen composites in their boundary types. -/
@[expose, implicit_reducible]
def compFunctor (a b c : O) :
    D.HorizontalGenerator a b × D.HorizontalGenerator b c ⥤ D.HorizontalGenerator a c :=
  let F := (D.singletonFunctor a b).prod (D.singletonFunctor b c) ⋙
    D.hCompFunctor ⋙ R.repFunctor a c
  { obj fg := R.mul fg.1 fg.2
    map α := F.map α
    map_id fg := F.map_id fg
    map_comp α β := F.map_comp α β }

/-- Composition of generating arrows is the chosen binary composite. -/
@[simp]
theorem compFunctor_obj {a b c : O} (f : D.HorizontalGenerator a b)
    (g : D.HorizontalGenerator b c) :
    (R.compFunctor a b c).obj (f, g) = R.mul f g :=
  (rfl)

/-- The binary comparisons identify path pasting with the singleton image of represented
composition, naturally in both input globular cells. -/
def compComparison (a b c : O) :
    (D.singletonFunctor a b).prod (D.singletonFunctor b c) ⋙ D.hCompFunctor ≅
      R.compFunctor a b c ⋙ D.singletonFunctor a c :=
  NatIso.ofComponents (fun fg ↦ R.repIso (D.hCompFunctor.obj
    ((D.singletonFunctor a b).obj fg.1, (D.singletonFunctor b c).obj fg.2)).edge) (by
      intro fg fg' α
      dsimp [compFunctor, repFunctor, singletonFunctor, inducedFunctor]
      exact (Iso.hom_inv_id_assoc (R.repIso _) _).symm)

@[simp]
theorem compComparison_hom_app {a b c : O} (f : D.HorizontalGenerator a b)
    (g : D.HorizontalGenerator b c) :
    (R.compComparison a b c).hom.app (f, g) = (R.mulIso f g).hom := by
  dsimp [compComparison, Functor.prod, NatIso.ofComponents]
  have e := R.repIso_cons_cons (@Quiver.Path.nil O H a) f g
  rw [repIso_cons_nil] at e
  erw [Functor.mapIso_refl, Iso.refl_trans] at e
  exact congrArg Iso.hom e

@[simp]
theorem compComparison_inv_app {a b c : O} (f : D.HorizontalGenerator a b)
    (g : D.HorizontalGenerator b c) :
    (R.compComparison a b c).inv.app (f, g) = (R.mulIso f g).inv :=
  (Iso.inv_eq_inv _ _).mpr (R.compComparison_hom_app f g)

/-- On globular cells the composition bifunctor conjugates horizontal pasting by the chosen
binary comparisons. -/
@[simp]
theorem compFunctor_map_hom {a b c : O} {f f' : D.HorizontalGenerator a b}
    {g g' : D.HorizontalGenerator b c} (α : f ⟶ f') (β : g ⟶ g') :
    ((R.compFunctor a b c).map (Prod.mkHom α β)).hom =
      (R.mulIso f g).inv ≫ D.hCompFunctor.map (Prod.mkHom α.hom β.hom) ≫ (R.mulIso f' g').hom := by
  apply (R.mulIso f g).eq_inv_comp.mpr
  have h := ((R.compComparison a b c).hom.naturality (Prod.mkHom α β)).symm
  simp only [Functor.comp_map, Functor.prod_map, inducedFunctor_map,
    compComparison_hom_app] at h
  exact h

/-- On underlying cells, represented composition pastes first, then replaces the two
horizontal boundaries by the chosen composite generators. -/
theorem compFunctor_map_cell {a b c : O} {f f' : D.HorizontalGenerator a b}
    {g g' : D.HorizontalGenerator b c} (α : f ⟶ f') (β : g ⟶ g') :
    ((R.compFunctor a b c).map (Prod.mkHom α β)).hom.cell =
      D.changeBottom (R.mulIso f' g')
        (D.changeTop (R.mulIso f g) (D.hComp α.hom.cell β.hom.cell)) := by
  rw [changeBottom_def, changeTop_def, compFunctor_map_hom]
  erw [HorizontalGlobular.comp_cell, HorizontalGlobular.comp_cell]
  simp only [DoubleCategoryStruct.vComp_cast_top, DoubleCategoryStruct.vComp_cast_bottom,
    DoubleCategoryStruct.Cell.cast_cast, hCompFunctor_map_cell]
  erw [vComp_assoc]
  simp only [DoubleCategoryStruct.Cell.cast_cast]
  rfl

end HorizontalRepresentation

end TauCeti.StrictDoubleCategory
