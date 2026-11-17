/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Unit and counit evaluations for the skyscraper sheaf adjunction

Let `Φ` be a point of a site `(C, J)`. Mathlib constructs the adjunction
`Φ.skyscraperSheafAdjunction : Φ.sheafFiber ⊣ Φ.skyscraperSheafFunctor` via
`Φ.skyscraperPresheafHomEquiv`. This file records the componentwise germ and product-projection
formulas for its counit and unit:

* `CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction_counit_app` and
  `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_skyscraperSheafAdjunction_counit_app`:
  composing the germ `Φ.toPresheafFiber X x (Φ.skyscraperPresheaf M)` with the counit at `M`
  recovers the product projection `Pi.π _ x`;
* `CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction_unit_app_hom` and
  `CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction_unit_app_hom_app_π`:
  evaluating the unit at a sheaf `F` on `X` and projecting to the `x`-factor recovers the germ map
  `Φ.toPresheafFiber X x F.obj`.
-/

public section

universe w v' v u' u

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]

/-- The counit of `Φ.skyscraperSheafAdjunction` at `M` is adjoint under
`Φ.skyscraperPresheafHomEquiv` to the identity on `Φ.skyscraperPresheaf M`. -/
lemma skyscraperSheafAdjunction_counit_app (M : A) :
    Φ.skyscraperSheafAdjunction.counit.app M =
      Φ.skyscraperPresheafHomEquiv.symm (𝟙 (Φ.skyscraperPresheaf M)) :=
  -- `Φ.sheafFiber.obj (Φ.skyscraperSheaf M)` is definitionally `Φ.presheafFiber.obj _`.
  (Φ.skyscraperSheafAdjunction.homEquiv_symm_id M).symm.trans
    (Φ.skyscraperSheafAdjunction_homEquiv_symm_apply (𝟙 (Φ.skyscraperSheaf M)))

/-- Composing the germ map of the skyscraper presheaf at `x : Φ.fiber.obj X` with the counit of
`Φ.skyscraperSheafAdjunction` recovers the `x`-projection of the product. -/
@[simp]
lemma toPresheafFiber_skyscraperSheafAdjunction_counit_app
    (M : A) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x (Φ.skyscraperPresheaf M) ≫
        Φ.skyscraperSheafAdjunction.counit.app M =
      Pi.π (fun (_ : Φ.fiber.obj X) ↦ M) x :=
  (congrArg (Φ.toPresheafFiber X x (Φ.skyscraperPresheaf M) ≫ ·)
    (Φ.skyscraperSheafAdjunction_counit_app M)).trans
    ((Φ.toPresheafFiber_skyscraperPresheafHomEquiv_symm (𝟙 _) X x).trans (Category.id_comp _))

/-- Right-associated version of `toPresheafFiber_skyscraperSheafAdjunction_counit_app` (stated
explicitly because `Point.sheafFiber` is not reducible). -/
@[simp]
lemma toPresheafFiber_skyscraperSheafAdjunction_counit_app_assoc
    (M : A) (X : C) (x : Φ.fiber.obj X) {Z : A} (h : M ⟶ Z) :
    Φ.toPresheafFiber X x (Φ.skyscraperPresheaf M) ≫
        Φ.skyscraperSheafAdjunction.counit.app M ≫ h =
      Pi.π (fun (_ : Φ.fiber.obj X) ↦ M) x ≫ h :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ h) (Φ.toPresheafFiber_skyscraperSheafAdjunction_counit_app M X x))

/-- On underlying presheaves, the unit of `Φ.skyscraperSheafAdjunction` at `F` is adjoint under
`Φ.skyscraperPresheafHomEquiv` to the identity on `Φ.presheafFiber.obj F.obj`. -/
lemma skyscraperSheafAdjunction_unit_app_hom (F : Sheaf J A) :
    (Φ.skyscraperSheafAdjunction.unit.app F).hom =
      Φ.skyscraperPresheafHomEquiv (𝟙 (Φ.presheafFiber.obj F.obj)) :=
  -- `Φ.sheafFiber.obj F` is definitionally `Φ.presheafFiber.obj F.obj`.
  (congrArg InducedCategory.Hom.hom (Φ.skyscraperSheafAdjunction.homEquiv_id F).symm).trans
    (Φ.skyscraperSheafAdjunction_homEquiv_apply_hom (𝟙 _))

/-- Projecting the `(op X)`-component of the unit of `Φ.skyscraperSheafAdjunction` at `F` onto
`x : Φ.fiber.obj X` yields the germ map `Φ.toPresheafFiber X x F.obj`. -/
@[simp]
lemma skyscraperSheafAdjunction_unit_app_hom_app_π
    (F : Sheaf J A) (X : C) (x : Φ.fiber.obj X) :
    (Φ.skyscraperSheafAdjunction.unit.app F).hom.app (op X) ≫
        Pi.π (fun (_ : Φ.fiber.obj X) ↦ Φ.sheafFiber.obj F) x =
      Φ.toPresheafFiber X x F.obj :=
  (congrArg (fun η ↦ η.app (op X) ≫ Pi.π (fun (_ : Φ.fiber.obj X) ↦ Φ.sheafFiber.obj F) x)
    (Φ.skyscraperSheafAdjunction_unit_app_hom F)).trans
    ((Φ.skyscraperPresheafHomEquiv_app_π (𝟙 _) X x).trans (Category.comp_id _))

/-- Right-associated version of `skyscraperSheafAdjunction_unit_app_hom_app_π` (stated explicitly
because `Point.skyscraperSheafFunctor` is not reducible). -/
@[simp]
lemma skyscraperSheafAdjunction_unit_app_hom_app_π_assoc
    (F : Sheaf J A) (X : C) (x : Φ.fiber.obj X) {Z : A} (h : Φ.sheafFiber.obj F ⟶ Z) :
    (Φ.skyscraperSheafAdjunction.unit.app F).hom.app (op X) ≫
        Pi.π (fun (_ : Φ.fiber.obj X) ↦ Φ.sheafFiber.obj F) x ≫ h =
      Φ.toPresheafFiber X x F.obj ≫ h :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ h) (Φ.skyscraperSheafAdjunction_unit_app_hom_app_π F X x))

end CategoryTheory.GrothendieckTopology.Point
