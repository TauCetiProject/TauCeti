/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import TauCeti.CategoryTheory.Sites.Monoidal

/-!
# Stalks of tensor products of sheaves on germs

Let `Φ` be a point of a site `(C, J)` and `A` a monoidal category in which the tensor product
commutes with filtered colimits. Mathlib makes the fibre functor `Φ.sheafFiber` monoidal, so that
the stalk of a tensor product of sheaves `F ⊗ G` is the tensor product of the stalks
(`CategoryTheory.Functor.Monoidal.μIso Φ.sheafFiber F G`). This file describes this identification
through the canonical map `Sheaf.toTensorObj F G : F.obj ⊗ G.obj ⟶ (F ⊗ G).obj`: its stalk is an
isomorphism, it intertwines the tensor comparisons of `Φ.presheafFiber` and `Φ.sheafFiber`, and
on germs `OplaxMonoidal.δ Φ.sheafFiber F G` sends the germ of the image of a section of
`F.obj ⊗ G.obj` to the tensor product of the germs.

## Main declarations

* `CategoryTheory.GrothendieckTopology.Point.μ_comp_presheafFiber_map_toTensorObj`: the stalk of
  `Sheaf.toTensorObj F G` turns the tensor comparison `LaxMonoidal.μ Φ.presheafFiber` into
  `LaxMonoidal.μ Φ.sheafFiber`.
* `CategoryTheory.GrothendieckTopology.Point.presheafFiber_map_toTensorObj_comp_δ`: the stalk of
  `Sheaf.toTensorObj F G` followed by `OplaxMonoidal.δ Φ.sheafFiber F G` is
  `OplaxMonoidal.δ Φ.presheafFiber F.obj G.obj`.
* `CategoryTheory.GrothendieckTopology.Point.toTensorObj_app_comp_toPresheafFiber_comp_δ`: the
  action of `OplaxMonoidal.δ Φ.sheafFiber F G` on germs.
-/

public section

universe w

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.GrothendieckTopology.Point

attribute [local instance] Sheaf.monoidalCategory

section Fiber

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type*} [Category* A] [MonoidalCategory A] [HasColimitsOfSize.{w, w} A]
  [HasProducts.{w} A] [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

/-- On stalks, the comparison `Sheaf.toTensorObj F G` is an isomorphism: the unit of
sheafification is inverted by the fibre functor of a point. -/
instance isIso_presheafFiber_map_toTensorObj (F G : Sheaf J A) :
    IsIso (Φ.presheafFiber.map (Sheaf.toTensorObj F G)) := by
  rw [Sheaf.toTensorObj, Functor.map_comp]
  infer_instance

end Fiber

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type*} [Category* A] [MonoidalCategory A] [HasColimitsOfSize.{w, w} A]
  [HasProducts.{w} A] [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] [LocallySmall.{w} C]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]

/-- The stalk of `Sheaf.toTensorObj F G` intertwines the tensor comparisons of the fibre functors
on presheaves and on sheaves. -/
@[reassoc]
lemma μ_comp_presheafFiber_map_toTensorObj (F G : Sheaf J A) :
    μ Φ.presheafFiber F.obj G.obj ≫ Φ.presheafFiber.map (Sheaf.toTensorObj F G) =
      μ Φ.sheafFiber F G := by
  -- `μ Φ.sheafFiber` is by definition a component of `curriedTensorPreIsoPost`.
  refine ((Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app' (presheafToSheaf J A) J.W
    Φ.sheafFiber Φ.presheafFiber (sheafificationIso F) (sheafificationIso G)).trans ?_).symm
  simp [presheafToSheafCompSheafFiberIso, Localization.Lifting.iso, Sheaf.toTensorObj, sheafFiber]

/-- The stalk of `Sheaf.toTensorObj F G` followed by the tensor comparison of the fibre functor on
sheaves is the tensor comparison of the fibre functor on presheaves. -/
lemma presheafFiber_map_toTensorObj_comp_δ (F G : Sheaf J A) :
    Φ.presheafFiber.map (Sheaf.toTensorObj F G) ≫ δ Φ.sheafFiber F G =
      δ Φ.presheafFiber F.obj G.obj :=
  (cancel_epi (μ Φ.presheafFiber F.obj G.obj)).1 <|
    (Φ.μ_comp_presheafFiber_map_toTensorObj_assoc F G (δ Φ.sheafFiber F G)).trans
      ((Functor.Monoidal.μ_δ _ _ _).trans
        (Functor.Monoidal.μ_δ Φ.presheafFiber F.obj G.obj).symm)

/-- On germs, `OplaxMonoidal.δ Φ.sheafFiber F G` sends the germ of the image of a section of the
sectionwise tensor product to the tensor product of the germs. -/
lemma toTensorObj_app_comp_toPresheafFiber_comp_δ (F G : Sheaf J A) (X : C)
    (x : Φ.fiber.obj X) :
    (Sheaf.toTensorObj F G).app (op X) ≫ Φ.toPresheafFiber X x (F ⊗ G).obj ≫
        δ Φ.sheafFiber F G =
      Φ.toPresheafFiber X x F.obj ⊗ₘ Φ.toPresheafFiber X x G.obj := by
  rw [← Φ.toPresheafFiber_naturality_assoc (Sheaf.toTensorObj F G) X x (δ Φ.sheafFiber F G),
    presheafFiber_map_toTensorObj_comp_δ]
  exact Φ.toPresheafFiber_δ X x F.obj G.obj

-- Explicit: `@[reassoc]` leaves the `_assoc` lemma left-associated across `Point.sheafFiber`.
lemma toTensorObj_app_comp_toPresheafFiber_comp_δ_assoc (F G : Sheaf J A) (X : C)
    (x : Φ.fiber.obj X) {Z : A} (h : Φ.sheafFiber.obj F ⊗ Φ.sheafFiber.obj G ⟶ Z) :
    (Sheaf.toTensorObj F G).app (op X) ≫ Φ.toPresheafFiber X x (F ⊗ G).obj ≫
        δ Φ.sheafFiber F G ≫ h =
      (Φ.toPresheafFiber X x F.obj ⊗ₘ Φ.toPresheafFiber X x G.obj) ≫ h := by
  -- Reassociate by hand: `Category.assoc` does not rewrite across `Point.sheafFiber`.
  refine Eq.trans ?_ (congrArg (· ≫ h) (Φ.toTensorObj_app_comp_toPresheafFiber_comp_δ F G X x))
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

end CategoryTheory.GrothendieckTopology.Point
