/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Yoneda

/-!
# Sections represented by a free Yoneda sheaf

A left adjoint from types supplies free objects in a coefficient category. The
sheafification of the free presheaf on a representable then corepresents sections
of coefficient sheaves, naturally in the site object and in the coefficient sheaf.
-/

public section

open CategoryTheory Opposite

universe v u w z

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  {L : Type v ⥤ D} {U : D ⥤ Type v} (adj : L ⊣ U)
  (J : GrothendieckTopology C) [HasWeakSheafify J D]

/-- Maps from the sheafification of the free presheaf on a representable correspond to sections
of the underlying type-valued presheaf. -/
noncomputable def freeYonedaSectionsEquiv (X : C) (M : Sheaf J D) :
    ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J D).obj X ⟶ M) ≃
      U.obj (M.obj.obj (op X)) :=
  ((sheafificationAdjunction J D).homEquiv _ _).trans
    (((adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv)

/-- The comparison is sheafification adjunction followed by the coefficient adjunction
and Yoneda evaluation. -/
lemma freeYonedaSectionsEquiv_apply (X : C) (M : Sheaf J D)
    (g : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J D).obj X ⟶ M) :
    adj.freeYonedaSectionsEquiv J X M g =
      yonedaEquiv ((adj.whiskerRight Cᵒᵖ).homEquiv _ _
        ((sheafificationAdjunction J D).homEquiv _ _ g)) := by
  unfold freeYonedaSectionsEquiv
  rfl

/-- Precomposition by the free map induced by a site arrow restricts a section along that arrow.
This is simplified before functor-map normalization and before coefficient naturality. -/
@[simp↓ 1100]
lemma freeYonedaSectionsEquiv_naturality_left {X Y : C} (f : X ⟶ Y) (M : Sheaf J D)
    (g : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J D).obj Y ⟶ M) :
    adj.freeYonedaSectionsEquiv J X M
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J D).map f ≫ g) =
      U.map (M.obj.map f.op) (adj.freeYonedaSectionsEquiv J Y M g) := by
  rw [freeYonedaSectionsEquiv_apply, freeYonedaSectionsEquiv_apply]
  dsimp only [Functor.comp_obj, Functor.comp_map] at g ⊢
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ f).symm

/-- Postcomposition by a coefficient morphism applies that morphism to the corresponding section. -/
@[simp↓]
lemma freeYonedaSectionsEquiv_naturality_right {X : C} {M N : Sheaf J D}
    (g : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J D).obj X ⟶ M)
    (f : M ⟶ N) :
    adj.freeYonedaSectionsEquiv J X N (g ≫ f) =
      U.map (f.hom.app (op X)) (adj.freeYonedaSectionsEquiv J X M g) := by
  simp only [freeYonedaSectionsEquiv_apply, Adjunction.homEquiv_naturality_right, yonedaEquiv_comp]
  -- Whiskering evaluates a natural transformation by applying `U` to its component.
  rfl


section Additive

variable [Preadditive D] {A : D ⥤ AddCommGrpCat.{v}} [A.Additive]
  (adjA : L ⊣ A ⋙ forget AddCommGrpCat)

/-- The free Yoneda equivalence is additive when the underlying-type functor comes from an
additive functor to abelian groups. The coefficient adjunction itself has a type-valued right
adjoint, so additivity is imposed on its abelian-group lift `A`. -/
noncomputable def freeYonedaSectionsAddEquiv (X : C) (M : Sheaf J D) :
    ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J D).obj X ⟶ M) ≃+
      A.obj (M.obj.obj (op X)) where
  toEquiv := adjA.freeYonedaSectionsEquiv J X M
  map_add' f g := by
    let : (presheafToSheaf J D).Additive :=
      (sheafificationAdjunction J D).left_adjoint_additive
    simp only [Equiv.toFun_as_coe]
    rw [freeYonedaSectionsEquiv_apply, freeYonedaSectionsEquiv_apply,
      freeYonedaSectionsEquiv_apply]
    simp only [Adjunction.homAddEquiv_add]
    rw [yonedaEquiv_apply, yonedaEquiv_apply, yonedaEquiv_apply]
    -- The whiskered adjunction evaluates at the unit's universal element; `A` preserves sums.
    rw [(adjA.whiskerRight Cᵒᵖ).homEquiv_unit,
      (adjA.whiskerRight Cᵒᵖ).homEquiv_unit, (adjA.whiskerRight Cᵒᵖ).homEquiv_unit]
    simp [Functor.map_add]

/-- The additive equivalence has the underlying free Yoneda equivalence. -/
lemma freeYonedaSectionsAddEquiv_apply (X : C) (M : Sheaf J D)
    (g : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J D).obj X ⟶ M) :
    adjA.freeYonedaSectionsAddEquiv J X M g = adjA.freeYonedaSectionsEquiv J X M g := by
  rfl

/-- The additive free Yoneda equivalence commutes with restriction along site morphisms. -/
@[simp↓ 1100]
lemma freeYonedaSectionsAddEquiv_naturality_left {X Y : C} (f : X ⟶ Y) (M : Sheaf J D)
    (g : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J D).obj Y ⟶ M) :
    adjA.freeYonedaSectionsAddEquiv J X M
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J D).map f ≫ g) =
      A.map (M.obj.map f.op) (adjA.freeYonedaSectionsAddEquiv J Y M g) := by
  rw [freeYonedaSectionsAddEquiv_apply, freeYonedaSectionsAddEquiv_apply]
  exact adjA.freeYonedaSectionsEquiv_naturality_left J f M g

/-- The additive free Yoneda equivalence commutes with coefficient morphisms. -/
@[simp↓]
lemma freeYonedaSectionsAddEquiv_naturality_right {X : C} {M N : Sheaf J D}
    (g : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J D).obj X ⟶ M)
    (f : M ⟶ N) :
    adjA.freeYonedaSectionsAddEquiv J X N (g ≫ f) =
      A.map (f.hom.app (op X)) (adjA.freeYonedaSectionsAddEquiv J X M g) := by
  rw [freeYonedaSectionsAddEquiv_apply, freeYonedaSectionsAddEquiv_apply]
  exact adjA.freeYonedaSectionsEquiv_naturality_right J g f

end Additive

end CategoryTheory.Adjunction
