/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-!
# The concrete functor from `AddCommGrpCat` to `ModuleCat ℤ`

Mathlib's `Mathlib.Algebra.Category.Grp.ZModuleEquivalence` establishes that the forgetful functor
`forget₂ (ModuleCat ℤ) AddCommGrpCat` is an equivalence of categories. This file provides the
explicit concrete inverse functor `AddCommGrpCat.toIntModule : AddCommGrpCat.{w} ⥤ ModuleCat.{w} ℤ`
equipping each abelian group with its canonical `ℤ`-module structure, together with its
object and morphism characterization lemmas and its `IsEquivalence` instance.

## Main declarations

* `AddCommGrpCat.toIntModule`: the functor `AddCommGrpCat.{w} ⥤ ModuleCat.{w} ℤ`.
* `AddCommGrpCat.toIntModule_obj`, `AddCommGrpCat.toIntModule_map`: object and morphism
  characterizations.
* `AddCommGrpCat.toIntModuleCompForget₂Iso`: natural isomorphism
  `toIntModule ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat ≅ 𝟭 AddCommGrpCat`.
-/

public section

open CategoryTheory

universe w

namespace AddCommGrpCat

/-- The equivalence `AddCommGrpCat.{w} ⥤ ModuleCat.{w} ℤ` equipping each abelian group with its
canonical `ℤ`-module structure. -/
@[expose] def toIntModule : AddCommGrpCat.{w} ⥤ ModuleCat.{w} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap

@[simp]
theorem toIntModule_obj (A : AddCommGrpCat.{w}) :
    toIntModule.obj A = ModuleCat.of ℤ A :=
  rfl

@[simp]
theorem toIntModule_map {A B : AddCommGrpCat.{w}} (f : A ⟶ B) :
    toIntModule.map f = ModuleCat.ofHom f.hom.toIntLinearMap :=
  rfl

/-- Composing `AddCommGrpCat.toIntModule` with the forgetful functor to `AddCommGrpCat` is
naturally isomorphic to the identity functor. -/
def toIntModuleCompForget₂Iso :
    toIntModule.{w} ⋙ forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w} ≅ 𝟭 AddCommGrpCat.{w} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

@[simp]
theorem toIntModuleCompForget₂Iso_hom_app (A : AddCommGrpCat.{w}) :
    toIntModuleCompForget₂Iso.hom.app A = 𝟙 A := by
  rfl

@[simp]
theorem toIntModuleCompForget₂Iso_inv_app (A : AddCommGrpCat.{w}) :
    toIntModuleCompForget₂Iso.inv.app A = 𝟙 A := by
  rfl

instance : toIntModule.{w}.IsEquivalence :=
  have := (Functor.isEquivalence_iff_of_iso toIntModuleCompForget₂Iso.{w}.symm).1 inferInstance
  Functor.isEquivalence_of_comp_right toIntModule.{w}
    (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w})

instance : toIntModule.{w}.Additive where

end AddCommGrpCat
