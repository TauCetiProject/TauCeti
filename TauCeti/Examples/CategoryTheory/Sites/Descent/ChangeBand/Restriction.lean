/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.ChangeBand.Restriction

/-!
# Slice restriction of extended Hom sheaves on a large site

These importing examples check the change-of-band comparison with site objects and
fibre objects one universe above arrows and coefficients. They also compare extension
along the identity band map with the original action on local isomorphisms.
-/

public noncomputable section

open CategoryTheory Opposite Bicategory

universe u

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{u, u + 1}} [F.IsGerbe J]
  {A B : Sheaf J AddCommGrpCat.{u}} (b : F.AbelianBanding J A) (φ : A ⟶ B)
  {U V : C} (f : V ⟶ U)
  [HasWeakSheafify (J.over U) (Type u)] [(J.over U).WEqualsLocallyBijective (Type u)]
  [HasWeakSheafify (J.over V) (Type u)] [(J.over V).WEqualsLocallyBijective (Type u)]
  (x y : F.obj (.mk (op U)))

example :
    (J.overMapPullback (Type u) f).obj
        ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf ≅
      ((b.changeBandHomFunctor φ V).obj
        (op ((F.map f.op.toLoc).toFunctor.obj x),
          (F.map f.op.toLoc).toFunctor.obj y)).sheaf :=
  b.changeBandHomRestrictionIso φ f x y

example (W : C) (t : W ⟶ V)
    (p : (F.presheafHom x y).obj (op (Over.mk (t ≫ f))))
    (a : A.obj.obj (op W)) :
    ((b.changeBandHomIdIso V).hom.app
        (op ((F.map f.op.toLoc).toFunctor.obj x),
          (F.map f.op.toLoc).toFunctor.obj y)).hom.hom.app (op (Over.mk t))
        ((b.changeBandHomRestrictionIso (𝟙 A) f x y).hom.hom.app (op (Over.mk t))
          (b.changeBandHomMk (𝟙 A) p a)) =
      b.homAct ((F.overMapCompPresheafHomIso x y f).hom.app (op (Over.mk t)) p)
        (.ofAdd a) := by
  rw [b.changeBandHomRestrictionIso_hom_mk]
  exact b.changeBandHomIdIso_hom_app_mk _ _ _
