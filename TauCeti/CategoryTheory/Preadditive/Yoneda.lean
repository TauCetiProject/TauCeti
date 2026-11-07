/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Morphisms out of representable functors with values in abelian groups

For a preadditive category `C`, the preadditive Yoneda embedding sends `Y : C` to the functor
`(-, Y) : Cᵒᵖ ⥤ AddCommGrpCat`. This file records how it acts on morphisms, and three facts
about it.

* The embedding is itself additive: `preadditiveYoneda.map (f + g)` is the sum of the images.
* A natural transformation out of `(-, Y)` is determined by its value on `𝟙 Y`, by the Yoneda
  lemma. No additivity of the target functor is needed.
* A morphism `(-, Y) ⟶ G` lifts along every epimorphism `F ⟶ G` out of an additive functor `F`.
  So representable functors are projective among additive functors. In particular a morphism
  `(-, Y) ⟶ F` lifts along every epimorphism `(-, Y') ⟶ F` to the image of a morphism `Y ⟶ Y'`,
  which is the form used to build presentations of finitely presented functors.

## Main declarations

* `CategoryTheory.preadditiveYoneda_map_app_apply`: the natural transformation `(-, f)` acts by
  postcomposition with `f`.
* `CategoryTheory.preadditiveYoneda_additive`: the preadditive Yoneda embedding is additive.
* `CategoryTheory.preadditiveYoneda_obj_hom_ext`: morphisms out of `(-, Y)` agreeing on `𝟙 Y`
  are equal.
* `CategoryTheory.exists_comp_eq_of_epi_of_additive`: lifting along an epimorphism out of an
  additive functor.
* `CategoryTheory.exists_preadditiveYoneda_map_comp_eq`: lifting along an epimorphism out of a
  representable functor.
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

/-- A morphism from a representable functor `(-, Y)` to `G` lifts along any epimorphism
`F ⟶ G` out of an additive functor `F`. -/
theorem exists_comp_eq_of_epi_of_additive {Y : C} {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}} [F.Additive]
    (π : F ⟶ G) [Epi π] (α : preadditiveYoneda.obj Y ⟶ G) :
    ∃ s : preadditiveYoneda.obj Y ⟶ F, s ≫ π = α := by
  obtain ⟨x, hx⟩ :=
    (AddCommGrpCat.epi_iff_surjective (π.app (op Y))).1 inferInstance (α.app (op Y) (𝟙 Y))
  -- The Yoneda morphism of `x` sends `h : Z ⟶ Y` to `F(h) x`; it respects addition because `F`
  -- is additive. Elements of `(-, Y)` at `Z` are morphisms `Z ⟶ Y`, but only up to unfolding
  -- `preadditiveYoneda`, so the components are given on `Z.unop ⟶ Y` and naturality is
  -- `F.map_comp` applied to `x`.
  let s : preadditiveYoneda.obj Y ⟶ F :=
    { app Z := AddCommGrpCat.ofHom (
        { toFun h := F.map h.op x
          map_zero' := by simp
          map_add' a b := by simp } : (Z.unop ⟶ Y) →+ F.obj Z)
      naturality Z Z' h := by
        ext (a : Z.unop ⟶ Y)
        exact ConcreteCategory.congr_hom (F.map_comp a.op h) x }
  refine ⟨s, preadditiveYoneda_obj_hom_ext ?_⟩
  exact (congrArg (π.app (op Y)) (by simp : F.map (𝟙 Y).op x = x)).trans hx

/-- A morphism from a representable functor `(-, Y)` to `F` lifts along any epimorphism
`(-, Y') ⟶ F`, and the lift is the image of a morphism `Y ⟶ Y'`. -/
theorem exists_preadditiveYoneda_map_comp_eq {Y Y' : C} {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (p : preadditiveYoneda.obj Y' ⟶ F) [Epi p] (α : preadditiveYoneda.obj Y ⟶ F) :
    ∃ u : Y ⟶ Y', preadditiveYoneda.map u ≫ p = α := by
  obtain ⟨s, hs⟩ := exists_comp_eq_of_epi_of_additive p α
  obtain ⟨u, rfl⟩ := preadditiveYoneda.map_surjective s
  exact ⟨u, hs⟩

end CategoryTheory
