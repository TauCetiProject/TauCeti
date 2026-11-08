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
* A morphism `(-, Y) ⟶ F` lifts along every epimorphism `(-, Y') ⟶ F` to the image of a morphism
  `Y ⟶ Y'`. This is the form in which representable functors are projective that is used to
  build presentations of finitely presented functors.

For an additive functor `G : C ⥤ D`, Mathlib's natural transformation
`CategoryTheory.preadditiveYonedaMap G X : (-, X) ⟶ (G -, G X)` is an epimorphism when `G` is
full, and the morphisms `f` with `(-, f)` killed by it are those killed by `G`. For the quotient
functor by an ideal `I` of `C`, its target is the quotient `(-, X) / I(-, X)`.

## Main declarations

* `CategoryTheory.preadditiveYoneda_map_app_apply`: the natural transformation `(-, f)` acts by
  postcomposition with `f`, and `CategoryTheory.preadditiveYoneda_obj_map_apply` the functor
  `(-, X)` by precomposition.
* `CategoryTheory.preadditiveYoneda_additive`: the preadditive Yoneda embedding is additive.
* `CategoryTheory.preadditiveYoneda_obj_hom_ext`: morphisms out of `(-, Y)` agreeing on `𝟙 Y`
  are equal.
* `CategoryTheory.exists_preadditiveYoneda_map_comp_eq`: lifting along an epimorphism out of a
  representable functor.
* `CategoryTheory.preadditiveYoneda_map_comp_preadditiveYonedaMap_eq_zero_iff`: the natural
  transformation `(-, X) ⟶ (G -, G X)` kills `(-, f)` exactly when `G` kills `f`.
-/

public section

universe v u u'

open Opposite CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The natural transformation `(-, f) : (-, X) ⟶ (-, Y)` is postcomposition with `f`. -/
@[simp]
theorem preadditiveYoneda_map_app_apply {X Y : C} (f : X ⟶ Y) (Z : Cᵒᵖ) (g : Z.unop ⟶ X) :
    (preadditiveYoneda.map f).app Z g = g ≫ f :=
  rfl

/-- The functor `(-, X)` acts on morphisms by precomposition. -/
@[simp]
theorem preadditiveYoneda_obj_map_apply {X : C} {Z W : Cᵒᵖ} (f : Z ⟶ W) (g : Z.unop ⟶ X) :
    (preadditiveYoneda.obj X).map f g = f.unop ≫ g :=
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

/-! ### The natural transformation `(-, X) ⟶ (G -, G X)` induced by an additive functor -/

section preadditiveYonedaMap

variable {D : Type u'} [Category.{v} D] [Preadditive D] (G : C ⥤ D) [G.Additive]

/-- The natural transformation `(-, X) ⟶ (G -, G X)` is an epimorphism when `G` is full. -/
instance epi_preadditiveYonedaMap [G.Full] (X : C) : Epi (preadditiveYonedaMap G X) := by
  have (Z : Cᵒᵖ) : Epi ((preadditiveYonedaMap G X).app Z) :=
    (AddCommGrpCat.epi_iff_surjective _).2 fun g ↦ ⟨G.preimage g, G.map_preimage g⟩
  exact NatTrans.epi_of_epi_app _

/-- The natural transformation `(-, X) ⟶ (G -, G X)` kills `(-, f)` exactly when `G` kills `f`. -/
theorem preadditiveYoneda_map_comp_preadditiveYonedaMap_eq_zero_iff {Y X : C}
    (f : Y ⟶ X) : preadditiveYoneda.map f ≫ preadditiveYonedaMap G X = 0 ↔ G.map f = 0 := by
  -- Both sides are read off on `𝟙 Y`, where `(-, f)` followed by the transformation gives
  -- `G.map (𝟙 Y ≫ f)`.
  have key : (preadditiveYoneda.map f ≫ preadditiveYonedaMap G X).app (op Y) (𝟙 Y) = G.map f :=
    (congrArg G.map (Category.id_comp f) :)
  have hzero : (0 : preadditiveYoneda.obj Y ⟶ G.op ⋙ preadditiveYoneda.obj (G.obj X)).app (op Y)
      (𝟙 Y) = 0 :=
    (rfl)
  refine ⟨fun h ↦ ?_, fun h ↦ preadditiveYoneda_obj_hom_ext ?_⟩
  · exact key.symm.trans ((congrArg (fun α ↦ α.app (op Y) (𝟙 Y)) h).trans hzero)
  · exact key.trans (h.trans hzero.symm)

end preadditiveYonedaMap

end CategoryTheory
