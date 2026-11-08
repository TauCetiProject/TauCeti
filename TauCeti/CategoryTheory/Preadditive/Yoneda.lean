/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Morphisms out of representable functors with values in abelian groups

For a preadditive category `C`, the preadditive Yoneda embedding sends `Y : C` to the functor
`(-, Y) : Cᵒᵖ ⥤ AddCommGrpCat`. This file records how it acts on morphisms, three facts about
it, and its restriction to a full subcategory.

* The embedding is itself additive: `preadditiveYoneda.map (f + g)` is the sum of the images.
* A natural transformation out of `(-, Y)` is determined by its value on `𝟙 Y`, by the Yoneda
  lemma. No additivity of the target functor is needed.
* A morphism `(-, Y) ⟶ F` lifts along every epimorphism `(-, Y') ⟶ F` to the image of a morphism
  `Y ⟶ Y'`. This is the form in which representable functors are projective that is used to
  build presentations of finitely presented functors.
* For a property `P` of objects of `C`, restricting `(-, X)` along the inclusion of the full
  subcategory of `P` gives a functor `X ↦ (-, X)|_P`, which agrees with `(-, Y)` on objects `Y` of
  that subcategory and preserves epimorphisms when `P` consists of projective objects.

## Main declarations

* `CategoryTheory.preadditiveYoneda_map_app_apply`: the natural transformation `(-, f)` acts by
  postcomposition with `f`.
* `CategoryTheory.preadditiveYoneda_additive`: the preadditive Yoneda embedding is additive.
* `CategoryTheory.preadditiveYoneda_obj_hom_ext`: morphisms out of `(-, Y)` agreeing on `𝟙 Y`
  are equal.
* `CategoryTheory.exists_preadditiveYoneda_map_comp_eq`: lifting along an epimorphism out of a
  representable functor.
* `CategoryTheory.ObjectProperty.restrictedPreadditiveYoneda`: the functor `X ↦ (-, X)|_P`.
* `CategoryTheory.ObjectProperty.preadditiveYonedaIsoRestricted`: on the full subcategory of `P`,
  the functor `X ↦ (-, X)|_P` is the preadditive Yoneda embedding.
* `CategoryTheory.ObjectProperty.epi_map_restrictedPreadditiveYoneda`: restriction to projective
  objects preserves epimorphisms.
-/

public section

universe v u

open Opposite CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The natural transformation `(-, f) : (-, X) ⟶ (-, Y)` is postcomposition with `f`. -/
@[simp]
theorem preadditiveYoneda_map_app_apply {X Y : C} (f : X ⟶ Y) (Z : Cᵒᵖ) (g : Z.unop ⟶ X) :
    (preadditiveYoneda.map f).app Z g = g ≫ f :=
  rfl

/-- Two morphisms out of the representable functor `(-, Y)` agree as soon as they agree on the
identity of `Y`. -/
theorem preadditiveYoneda_obj_hom_ext {Y : C} {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    {α β : preadditiveYoneda.obj Y ⟶ F} (h : α.app (op Y) (𝟙 Y) = β.app (op Y) (𝟙 Y)) :
    α = β :=
  ((Functor.whiskeringRight Cᵒᵖ _ _).obj (forget AddCommGrpCat)).map_injective
    (yonedaEquiv.injective h)

/-- The preadditive Yoneda embedding `Y ↦ (-, Y)` is an additive functor. -/
instance preadditiveYoneda_additive :
    (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v}).Additive where
  map_add {_ _ f g} := by
    -- An element of `(preadditiveYoneda.obj X).obj Z` is a morphism `h : Z.unop ⟶ X` and
    -- `(-, f)` sends it to `h ≫ f` (`preadditiveYoneda_map_app_apply`), so additivity is
    -- distributivity of composition.
    ext Z (h : Z.unop ⟶ _)
    exact Preadditive.comp_add _ _ _ h f g

/-- A morphism from a representable functor `(-, Y)` to `F` lifts along any epimorphism
`(-, Y') ⟶ F`, and the lift is the image of a morphism `Y ⟶ Y'`. -/
theorem exists_preadditiveYoneda_map_comp_eq {Y Y' : C} {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (p : preadditiveYoneda.obj Y' ⟶ F) [Epi p] (α : preadditiveYoneda.obj Y ⟶ F) :
    ∃ u : Y ⟶ Y', preadditiveYoneda.map u ≫ p = α := by
  obtain ⟨u, hu⟩ :=
    (AddCommGrpCat.epi_iff_surjective (p.app (op Y))).1 inferInstance (α.app (op Y) (𝟙 Y))
  refine ⟨u, preadditiveYoneda_obj_hom_ext ?_⟩
  exact (congrArg (p.app (op Y))
    ((preadditiveYoneda_map_app_apply u (op Y) (𝟙 Y)).trans (Category.id_comp u))).trans hu

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- The functor `X ↦ (-, X)|_P`, restricting the representable functor `(-, X)` to the full
subcategory of `P`. It is exposed so that an element of `(-, X)|_P` at `Q` is a morphism
`Q.obj ⟶ X`, which is what the statements of its application lemmas are about. -/
@[expose] def restrictedPreadditiveYoneda : C ⥤ P.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{v} :=
  preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj P.ι.op

/-- The natural transformation `(-, f)|_P` is postcomposition with `f`. -/
@[simp]
theorem restrictedPreadditiveYoneda_map_app_apply {X Y : C} (f : X ⟶ Y) (Q : P.FullSubcategoryᵒᵖ)
    (g : Q.unop.obj ⟶ X) : (P.restrictedPreadditiveYoneda.map f).app Q g = g ≫ f :=
  rfl

/-- The functor `(-, X)|_P` acts on morphisms of `P` by precomposition. -/
@[simp]
theorem restrictedPreadditiveYoneda_obj_map_apply (X : C) {Q Q' : P.FullSubcategoryᵒᵖ}
    (u : Q ⟶ Q') (g : Q.unop.obj ⟶ X) :
    (P.restrictedPreadditiveYoneda.obj X).map u g = u.unop.hom ≫ g :=
  rfl

instance : P.restrictedPreadditiveYoneda.Additive :=
  inferInstanceAs (preadditiveYoneda ⋙ _).Additive

/-- On the full subcategory of `P`, the functor `X ↦ (-, X)|_P` is the preadditive Yoneda
embedding. -/
def preadditiveYonedaIsoRestricted : preadditiveYoneda ≅ P.ι ⋙ P.restrictedPreadditiveYoneda :=
  NatIso.ofComponents (fun Y ↦ NatIso.ofComponents (fun Z ↦
    (InducedCategory.homAddEquiv (F := FullSubcategory.obj)).toAddCommGrpIso))

/-- The identification of `(-, Y)` with `(-, Y.obj)|_P` sends a morphism of the full subcategory to
the underlying morphism of `C`. -/
theorem preadditiveYonedaIsoRestricted_hom_app_app_apply (Y : P.FullSubcategory)
    (Z : P.FullSubcategoryᵒᵖ) (g : Z.unop ⟶ Y) :
    ((P.preadditiveYonedaIsoRestricted.hom.app Y).app Z) g = g.hom :=
  (rfl)

/-- The identification of `(-, Y)` with `(-, Y.obj)|_P` is natural in `Y`. -/
theorem preadditiveYoneda_map_comp_preadditiveYonedaIsoRestricted_hom {X Y : P.FullSubcategory}
    (f : X ⟶ Y) : preadditiveYoneda.map f ≫ P.preadditiveYonedaIsoRestricted.hom.app Y =
      P.preadditiveYonedaIsoRestricted.hom.app X ≫ P.restrictedPreadditiveYoneda.map f.hom :=
  P.preadditiveYonedaIsoRestricted.hom.naturality f

variable {P}

/-- Restriction to projective objects preserves epimorphisms. -/
theorem epi_map_restrictedPreadditiveYoneda (hP : P ≤ isProjective C) {X Y : C} (π : X ⟶ Y)
    [Epi π] : Epi (P.restrictedPreadditiveYoneda.map π) := by
  rw [NatTrans.epi_iff_epi_app]
  intro Q
  rw [AddCommGrpCat.epi_iff_surjective]
  intro (v : Q.unop.obj ⟶ Y)
  have : Projective Q.unop.obj := hP _ Q.unop.property
  exact ⟨Projective.factorThru (P := Q.unop.obj) v π,
    Projective.factorThru_comp (P := Q.unop.obj) v π⟩

end ObjectProperty

end CategoryTheory
