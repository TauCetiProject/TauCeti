/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

/-- Precomposition by the free map induced by a site arrow restricts a section along that arrow. -/
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
lemma freeYonedaSectionsEquiv_naturality_right {X : C} {M N : Sheaf J D}
    (g : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J D).obj X ⟶ M)
    (f : M ⟶ N) :
    adj.freeYonedaSectionsEquiv J X N (g ≫ f) =
      U.map (f.hom.app (op X)) (adj.freeYonedaSectionsEquiv J X M g) := by
  simp only [freeYonedaSectionsEquiv_apply, Adjunction.homEquiv_naturality_right, yonedaEquiv_comp]
  rfl

end CategoryTheory.Adjunction
