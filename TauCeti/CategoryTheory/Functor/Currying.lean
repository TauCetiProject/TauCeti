/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Uncurrying and composition

For a bifunctor `H : B ⥤ C ⥤ D`, the uncurried functor `Functor.uncurry.obj H : B × C ⥤ D`
restricted along a functor `J ⥤ B × C` whose first coordinate is constant at `b` is the
restriction of `H.obj b` along the second coordinate
(`CategoryTheory.Functor.const_obj_prod'_comp_uncurry_obj`). Uncurrying also commutes with
postcomposition (`CategoryTheory.Functor.uncurryObjCompIso`), with identity components.
`bifunctorCompIsoOfIsoId` transports any bifunctor through a functor isomorphic to the identity.
The identity transport follows the whiskering construction in
[Tau Ceti PR #47483](https://github.com/TauCetiProject/TauCeti/pull/47483).
-/

public section

namespace CategoryTheory.Functor

variable {J B C D : Type*} [Category J] [Category B] [Category C] [Category D]

/-- On a constant first coordinate `b`, the uncurried functor of `H : B ⥤ C ⥤ D` restricts to
`H.obj b`. -/
lemma const_obj_prod'_comp_uncurry_obj (H : B ⥤ C ⥤ D) (b : B) (x : J ⥤ C) :
    ((Functor.const J).obj b).prod' x ⋙ Functor.uncurry.obj H = x ⋙ H.obj b :=
  Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ by simp)

variable {E : Type*} [Category E]

/-- Uncurrying commutes with postcomposition by a functor. -/
def uncurryObjCompIso (H : B ⥤ C ⥤ D) (F : D ⥤ E) :
    uncurry.obj (H ⋙ (whiskeringRight C D E).obj F) ≅ uncurry.obj H ⋙ F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by simp [Functor.map_comp])

@[simp]
lemma uncurryObjCompIso_hom_app (H : B ⥤ C ⥤ D) (F : D ⥤ E) (X : B × C) :
    (uncurryObjCompIso H F).hom.app X = 𝟙 _ := (rfl)

@[simp]
lemma uncurryObjCompIso_inv_app (H : B ⥤ C ⥤ D) (F : D ⥤ E) (X : B × C) :
    (uncurryObjCompIso H F).inv.app X = 𝟙 _ := (rfl)


variable {A : Type*} [Category* A] (T : A ⥤ A ⥤ A) {G : A ⥤ A} (e : G ≅ 𝟭 A)

/-- A functor isomorphic to the identity commutes with every bifunctor. The forward map
applies the identity comparison to each input and its inverse to the output. -/
def bifunctorCompIsoOfIsoId :
    (((whiskeringLeft₂ A).obj G).obj G).obj T ≅
      T ⋙ (whiskeringRight _ _ _).obj G := by
  let W := whiskeringLeft₂ (C₁ := A) (C₂ := A) (D₁ := A) (D₂ := A) A
  exact (((W.mapIso e).app G).app T) ≪≫
    (((W.obj (𝟭 A)).mapIso e).app T) ≪≫
    (isoWhiskerLeft T ((whiskeringRight _ _ _).mapIso e) ≪≫ rightUnitor T).symm

/-- Component formula for the comparison induced by an isomorphism to the identity. -/
@[simp]
lemma bifunctorCompIsoOfIsoId_hom_app_app (X Y : A) :
    (((T.bifunctorCompIsoOfIsoId e).hom.app X).app Y) =
      (T.map (e.hom.app X)).app (G.obj Y) ≫
        (T.obj X).map (e.hom.app Y) ≫ e.inv.app ((T.obj X).obj Y) := by
  simp [bifunctorCompIsoOfIsoId]

/-- Inverse component formula for the comparison induced by an isomorphism to the identity. -/
@[simp]
lemma bifunctorCompIsoOfIsoId_inv_app_app (X Y : A) :
    (((T.bifunctorCompIsoOfIsoId e).inv.app X).app Y) =
      e.hom.app ((T.obj X).obj Y) ≫ (T.obj X).map (e.inv.app Y) ≫
        (T.map (e.inv.app X)).app (G.obj Y) := by
  simp [bifunctorCompIsoOfIsoId]

end CategoryTheory.Functor
