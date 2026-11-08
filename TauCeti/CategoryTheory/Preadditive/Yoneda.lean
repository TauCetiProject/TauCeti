/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Representable and corepresentable functors with values in abelian groups

For a preadditive category `C`, the preadditive Yoneda embedding sends `Y : C` to the functor
`(-, Y) : Cᵒᵖ ⥤ AddCommGrpCat`. This file records how it acts on morphisms, and three facts
about it.

* The embedding is itself additive: `preadditiveYoneda.map (f + g)` is the sum of the images.
* A natural transformation out of `(-, Y)` is determined by its value on `𝟙 Y`, by the Yoneda
  lemma. No additivity of the target functor is needed.
* A morphism `(-, Y) ⟶ F` lifts along every epimorphism `(-, Y') ⟶ F` to the image of a morphism
  `Y ⟶ Y'`. This is the form in which representable functors are projective that is used to
  build presentations of finitely presented functors.

Dually, for an additive functor `G : C ⥤ Ab` corepresented by an object `P`, the bijection
`(P ⟶ X) ≃ G(X)` of the corepresentation is additive: it preserves zero, and so does its inverse,
which is moreover additive.

## Main declarations

* `CategoryTheory.preadditiveYoneda_map_app_apply`: the natural transformation `(-, f)` acts by
  postcomposition with `f`.
* `CategoryTheory.preadditiveYoneda_additive`: the preadditive Yoneda embedding is additive.
* `CategoryTheory.preadditiveYoneda_obj_hom_ext`: morphisms out of `(-, Y)` agreeing on `𝟙 Y`
  are equal.
* `CategoryTheory.exists_preadditiveYoneda_map_comp_eq`: lifting along an epimorphism out of a
  representable functor.
* `CategoryTheory.Functor.CorepresentableBy.homEquiv_zero` and
  `CategoryTheory.Functor.CorepresentableBy.homEquiv_symm_zero`: the corepresentation and its
  inverse preserve zero.
* `CategoryTheory.Functor.CorepresentableBy.homEquiv_symm_add`: the inverse of the
  corepresentation is additive.
-/

public section

universe t v u

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

namespace Functor.CorepresentableBy

variable {G : C ⥤ AddCommGrpCat.{t}} [G.Additive]
  {P : C} (R : (G ⋙ forget AddCommGrpCat).CorepresentableBy P)

/-- The corepresentation of an additive functor `G : C ⥤ Ab` sends the zero morphism to zero. -/
lemma homEquiv_zero {X : C} : R.homEquiv (0 : P ⟶ X) = (0 : G.obj X) := by
  rw [R.homEquiv_eq, Functor.comp_map, G.map_zero]
  rfl

/-- The inverse of the corepresentation of an additive functor `G : C ⥤ Ab` sends zero to the zero
morphism. -/
lemma homEquiv_symm_zero {X : C} : R.homEquiv.symm (0 : G.obj X) = 0 :=
  R.homEquiv.symm_apply_eq.2 R.homEquiv_zero.symm

/-- The inverse of the corepresentation `(P ⟶ X) ≃ G(X)` of an additive functor `G : C ⥤ Ab` is
additive. -/
lemma homEquiv_symm_add {X : C} (x y : G.obj X) :
    R.homEquiv.symm (x + y) = R.homEquiv.symm x + R.homEquiv.symm y := by
  have h (z : G.obj X) : G.map (R.homEquiv.symm z) (R.homEquiv (𝟙 P)) = z :=
    (R.homEquiv_eq _).symm.trans (R.homEquiv.apply_symm_apply z)
  rw [R.homEquiv.symm_apply_eq, R.homEquiv_eq, Functor.comp_map, G.map_add]
  exact (congrArg₂ (· + ·) (h x) (h y)).symm

end Functor.CorepresentableBy

end CategoryTheory
