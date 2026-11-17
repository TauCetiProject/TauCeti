/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Comap
public import TauCeti.CategoryTheory.Limits.FinallySmall
public import TauCeti.CategoryTheory.Sites.Point.Category
public import TauCeti.CategoryTheory.Sites.Point.Skyscraper

/-!
# Stalks of sheaf pullbacks along points with isomorphic fiber functors

Mathlib's `CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso` identifies the stalk
`(Φ.comap F hF).sheafFiber` of a pulled-back point with `F.sheafPullback A J K ⋙ Φ.sheafFiber`.
In geometric situations (for instance, geometric points of the small étale site under base change
of schemes), the composite `F ⋙ Φ.fiber` is not definitionally equal to the fiber functor of the
expected point `Ψ` on `(C, J)`, but only naturally isomorphic to it.

This file provides:
* `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app`: germ
  characterization of Mathlib's `Point.sheafFiberComapIso`;
* `CategoryTheory.GrothendieckTopology.Point.comapIsoOfFiberIso`: the point isomorphism
  `Ψ ≅ Φ.comap F hF` induced by `F ⋙ Φ.fiber ≅ Ψ.fiber`;
* `CategoryTheory.GrothendieckTopology.Point.sheafPullbackCompSheafFiberIsoOfFiberIso` and its germ
  characterizations: the stalk comparison `F.sheafPullback A J K ⋙ Φ.sheafFiber ≅ Ψ.sheafFiber`
  induced by a natural isomorphism `F ⋙ Φ.fiber ≅ Ψ.fiber`.
-/

public section

universe w v

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

section GermComap

variable {C D : Type*} [Category* C] [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (Φ : Point.{w} K) (F : C ⥤ D) [RepresentablyFlat F] (hF : CoverPreserving J K F)
  [InitiallySmall (F ⋙ Φ.fiber).Elements]

/-- Under `Point.sheafFiberComapIso`, the germ at `Φ.comap F hF` of a section of `G` over `X`
maps to the germ at `Φ` over `F.obj X` of its image under the pullback unit `G ⟶ F_* F^* G`. -/
@[simp]
lemma toPresheafFiber_sheafFiberComapIso_hom_app
    (A : Type*) [Category.{v} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    (X : C) (x : (Φ.comap F hF).fiber.obj X) (G : Sheaf J A) :
    (Φ.comap F hF).toPresheafFiber X x G.obj ≫ (Φ.sheafFiberComapIso F hF A).hom.app G =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        Φ.toPresheafFiber (F.obj X) x ((F.sheafPullback A J K).obj G).obj := by
  let H := (F.sheafPullback A J K).obj G
  let Ψ := Φ.comap F hF
  rw [sheafFiberComapIso_hom_app]
  refine (Ψ.toPresheafFiber_naturality_assoc
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom X x _).trans ?_
  refine congrArg (((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫ ·) ?_
  refine (Ψ.toPresheafFiber_naturality_assoc
    (((F.sheafPushforwardContinuous A J K).map
      (Φ.skyscraperSheafAdjunction.unit.app H)).hom) X x _).trans ?_
  -- `Point.skyscraperSheafFunctorCompSheafPushforwardContinuous` is `Iso.refl _`.
  have hsky : Ψ.toPresheafFiber X x
      (((F.sheafPushforwardContinuous A J K).obj
        (Φ.skyscraperSheafFunctor.obj (Φ.sheafFiber.obj H))).obj) ≫
      Ψ.sheafFiber.map
        ((Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous F hF A).hom.app
          (Φ.sheafFiber.obj H)) ≫
      Ψ.skyscraperSheafAdjunction.counit.app (Φ.sheafFiber.obj H) =
      Pi.π _ x :=
    (Ψ.toPresheafFiber_naturality_assoc
      (((Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous F hF A).hom.app
        (Φ.sheafFiber.obj H)).hom) X x _).trans
      ((Category.id_comp _).trans
        (Ψ.toPresheafFiber_skyscraperSheafAdjunction_counit_app (Φ.sheafFiber.obj H) X x))
  exact (congrArg (_ ≫ ·) hsky).trans
    (Φ.skyscraperSheafAdjunction_unit_app_hom_app_π H (F.obj X) x)

@[simp]
lemma toPresheafFiber_sheafFiberComapIso_hom_app_assoc
    (A : Type*) [Category.{v} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    (X : C) (x : (Φ.comap F hF).fiber.obj X) (G : Sheaf J A)
    {Z : A} (h : Φ.sheafFiber.obj ((F.sheafPullback A J K).obj G) ⟶ Z) :
    (Φ.comap F hF).toPresheafFiber X x G.obj ≫
        ((Φ.sheafFiberComapIso F hF A).hom.app G :
          _ ⟶ Φ.sheafFiber.obj ((F.sheafPullback A J K).obj G)) ≫ h =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        Φ.toPresheafFiber (F.obj X) x ((F.sheafPullback A J K).obj G).obj ≫ h :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ h) (toPresheafFiber_sheafFiberComapIso_hom_app Φ F hF A X x G)).trans
      (Category.assoc _ _ _))

end GermComap

section ComapOfFiberIso

variable {C D : Type*} [Category* C] [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (Φ : Point.{w} K) (Ψ : Point.{w} J)
  (F : C ⥤ D) [RepresentablyFlat F] (hF : CoverPreserving J K F)
  (e : F ⋙ Φ.fiber ≅ Ψ.fiber)

/-- If `F ⋙ Φ.fiber ≅ Ψ.fiber`, then `Ψ` is isomorphic in `Point.{w} J` to `Φ.comap F hF`. -/
def comapIsoOfFiberIso :
    letI := initiallySmall_elements_of_iso e
    Ψ ≅ Φ.comap F hF :=
  letI := initiallySmall_elements_of_iso e
  isoMk e

@[simp]
lemma comapIsoOfFiberIso_hom :
    letI := initiallySmall_elements_of_iso e
    (comapIsoOfFiberIso Φ Ψ F hF e).hom = ⟨e.hom⟩ :=
  letI := initiallySmall_elements_of_iso e
  isoMk_hom (Φ₁ := Ψ) (Φ₂ := Φ.comap F hF) e

@[simp]
lemma comapIsoOfFiberIso_inv :
    letI := initiallySmall_elements_of_iso e
    (comapIsoOfFiberIso Φ Ψ F hF e).inv = ⟨e.inv⟩ :=
  letI := initiallySmall_elements_of_iso e
  isoMk_inv (Φ₁ := Ψ) (Φ₂ := Φ.comap F hF) e

/-- Given a representably flat, cover-preserving, continuous functor `F : C ⥤ D` between sites
`(C, J)` and `(D, K)`, points `Φ` of `(D, K)` and `Ψ` of `(C, J)`, and a natural isomorphism
`F ⋙ Φ.fiber ≅ Ψ.fiber`, the stalk at `Φ` of `F.sheafPullback A J K` identifies naturally with the
stalk at `Ψ`. -/
noncomputable def sheafPullbackCompSheafFiberIsoOfFiberIso
    (A : Type*) [Category.{v} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    F.sheafPullback A J K ⋙ Φ.sheafFiber ≅ Ψ.sheafFiber :=
  letI := initiallySmall_elements_of_iso e
  (Φ.sheafFiberComapIso F hF A).symm ≪≫ sheafFiberIsoOfFiberIso e

lemma sheafPullbackCompSheafFiberIsoOfFiberIso_eq
    (A : Type*) [Category.{v} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    letI := initiallySmall_elements_of_iso e
    sheafPullbackCompSheafFiberIsoOfFiberIso Φ Ψ F hF e A =
      (Φ.sheafFiberComapIso F hF A).symm ≪≫ sheafFiberIsoOfFiberIso e :=
  (rfl)

lemma sheafPullbackCompSheafFiberIsoOfFiberIso_hom_app
    (A : Type*) [Category.{v} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    (G : Sheaf J A) :
    letI := initiallySmall_elements_of_iso e
    (sheafPullbackCompSheafFiberIsoOfFiberIso Φ Ψ F hF e A).hom.app G =
      (Φ.sheafFiberComapIso F hF A).inv.app G ≫
        (sheafFiberIsoOfFiberIso (Φ₁ := Φ.comap F hF) (A := A) e).hom.app G :=
  (rfl)

lemma sheafPullbackCompSheafFiberIsoOfFiberIso_inv_app
    (A : Type*) [Category.{v} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    (G : Sheaf J A) :
    letI := initiallySmall_elements_of_iso e
    (sheafPullbackCompSheafFiberIsoOfFiberIso Φ Ψ F hF e A).inv.app G =
      (sheafFiberIsoOfFiberIso (Φ₁ := Φ.comap F hF) (A := A) e).inv.app G ≫
        (Φ.sheafFiberComapIso F hF A).hom.app G :=
  (rfl)

/-- Under the inverse of `sheafPullbackCompSheafFiberIsoOfFiberIso`, the germ at `Ψ` of a section of
`G` over `X` maps to the germ at `Φ` over `F.obj X` (along `e.inv.app X y`) of its image under the
pullback unit `G ⟶ F_* F^* G`. -/
@[simp]
lemma toPresheafFiber_sheafPullbackCompSheafFiberIsoOfFiberIso_inv_app
    (A : Type*) [Category.{v} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    (X : C) (y : Ψ.fiber.obj X) (G : Sheaf J A) :
    Ψ.toPresheafFiber X y G.obj ≫
        (sheafPullbackCompSheafFiberIsoOfFiberIso Φ Ψ F hF e A).inv.app G =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        Φ.toPresheafFiber (F.obj X) (e.inv.app X y) ((F.sheafPullback A J K).obj G).obj := by
  have := initiallySmall_elements_of_iso e
  have hinv : (sheafPullbackCompSheafFiberIsoOfFiberIso Φ Ψ F hF e A).inv.app G =
      (presheafFiberIsoOfFiberIso (Φ₁ := Φ.comap F hF) (A := A) e).inv.app G.obj ≫
        (Φ.sheafFiberComapIso F hF A).hom.app G :=
    (sheafPullbackCompSheafFiberIsoOfFiberIso_inv_app Φ Ψ F hF e A G).trans
      (congrArg (· ≫ (Φ.sheafFiberComapIso F hF A).hom.app G)
        (sheafFiberIsoOfFiberIso_inv_app (Φ₁ := Φ.comap F hF) (A := A) e G))
  exact (congrArg (Ψ.toPresheafFiber X y G.obj ≫ ·) hinv).trans
    (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (Φ.sheafFiberComapIso F hF A).hom.app G)
        (toPresheafFiber_presheafFiberIsoOfFiberIso_inv_app
          (Φ₁ := Φ.comap F hF) (Φ₂ := Ψ) e X y G.obj))).trans
      (toPresheafFiber_sheafFiberComapIso_hom_app Φ F hF A X (e.inv.app X y) G))

@[simp]
lemma toPresheafFiber_sheafPullbackCompSheafFiberIsoOfFiberIso_inv_app_assoc
    (A : Type*) [Category.{v} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    (X : C) (y : Ψ.fiber.obj X) (G : Sheaf J A)
    {Z : A} (h : Φ.sheafFiber.obj ((F.sheafPullback A J K).obj G) ⟶ Z) :
    Ψ.toPresheafFiber X y G.obj ≫
        ((sheafPullbackCompSheafFiberIsoOfFiberIso Φ Ψ F hF e A).inv.app G :
          _ ⟶ Φ.sheafFiber.obj ((F.sheafPullback A J K).obj G)) ≫ h =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        Φ.toPresheafFiber (F.obj X) (e.inv.app X y) ((F.sheafPullback A J K).obj G).obj ≫ h :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ h)
      (toPresheafFiber_sheafPullbackCompSheafFiberIsoOfFiberIso_inv_app Φ Ψ F hF e A X y G)).trans
      (Category.assoc _ _ _))

/-- Under `sheafPullbackCompSheafFiberIsoOfFiberIso`, the germ at `Φ` over `F.obj X` of the pullback
of a section of `G` over `X` maps to the germ of that section at `Ψ` along `e.hom.app X x`. -/
@[reassoc]
lemma unit_toPresheafFiber_sheafPullbackCompSheafFiberIsoOfFiberIso_hom_app
    (A : Type*) [Category.{v} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    (X : C) (x : Φ.fiber.obj (F.obj X)) (G : Sheaf J A) :
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
      Φ.toPresheafFiber (F.obj X) x ((F.sheafPullback A J K).obj G).obj ≫
        (sheafPullbackCompSheafFiberIsoOfFiberIso Φ Ψ F hF e A).hom.app G =
      Ψ.toPresheafFiber X (e.hom.app X x) G.obj := by
  refine (Category.assoc _ _ _).symm.trans
    ((Iso.comp_inv_eq ((sheafPullbackCompSheafFiberIsoOfFiberIso Φ Ψ F hF e A).app G).symm).mpr ?_)
  exact ((toPresheafFiber_sheafPullbackCompSheafFiberIsoOfFiberIso_inv_app
    Φ Ψ F hF e A X (e.hom.app X x) G).trans
    (congrArg (fun z ↦ ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
      Φ.toPresheafFiber (F.obj X) z ((F.sheafPullback A J K).obj G).obj)
      (Iso.hom_inv_id_app_apply e X x))).symm

end ComapOfFiberIso

end CategoryTheory.GrothendieckTopology.Point
