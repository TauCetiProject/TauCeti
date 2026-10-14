/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs

/-!
# Pushforward of sheaves of modules on underlying presheaves

Let `F : C ⥤ D` be a continuous functor between small sites, `R` and `S` sheaves of commutative
rings on `D` and `C`, and `φ : S ⟶ F_* R` a morphism of the underlying sheaves of rings. This file
records the data underlying the pushforward `SheafOfModules.pushforward φ` of sheaves of modules
that sectionwise constructions transfer along: the morphism of presheaves of commutative rings
underlying `φ`, and the pushforward of the underlying presheaves of modules.

## Main declarations

* `SheafOfModules.commRingCatHom`: the morphism of presheaves of commutative rings underlying `φ`,
  computed on sections by `SheafOfModules.commRingCatHom_app`;
* `SheafOfModules.presheafPushforward`: the pushforward of presheaves of modules underlying the
  pushforward of sheaves of modules;
* `SheafOfModules.forget_map_pushforward_map`: on underlying presheaves, the pushforward of a
  morphism of sheaves of modules is the pushforward of the underlying morphism.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  {F : C ⥤ D} [F.IsContinuous J K] {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))

/-- The morphism of presheaves of commutative rings underlying `φ`. Its body is exposed so that
sectionwise constructions over presheaves of commutative rings, pushed forward along it, are
pushforwards along `φ.hom`. -/
@[expose]
def commRingCatHom : S.obj ⟶ F.op ⋙ R.obj where
  app U := CommRingCat.ofHom (φ.hom.app U).hom
  naturality _ _ f := by
    ext x
    exact congr($(φ.hom.naturality f).hom x)

/-- On sections over `U`, the morphism of presheaves of commutative rings underlying `φ` is the
ring map `φ.hom.app U`. -/
@[simp]
lemma commRingCatHom_app (U : Cᵒᵖ) :
    (commRingCatHom φ).app U =
      CommRingCat.ofHom (R := S.obj.obj U) (S := R.obj.obj (F.op.obj U)) (φ.hom.app U).hom :=
  rfl

/-- The pushforward of presheaves of modules underlying `SheafOfModules.pushforward φ`. It is
Mathlib's `PresheafOfModules.pushforward φ.hom`, with source and target written as presheaves of
modules over the presheaves of rings `(ringCatSheaf R).obj` and `(ringCatSheaf S).obj`, so that it
composes with `SheafOfModules.forget` and with sheafification. -/
@[expose]
def presheafPushforward :
    PresheafOfModules.{u} (ringCatSheaf R).obj ⥤ PresheafOfModules.{u} (ringCatSheaf S).obj :=
  PresheafOfModules.pushforward φ.hom

/-- On underlying presheaves of modules, the pushforward of a morphism of sheaves of modules is
the pushforward of the underlying morphism of presheaves. -/
lemma forget_map_pushforward_map {M N : _root_.SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ N) :
    (_root_.SheafOfModules.forget (ringCatSheaf S)).map
        ((_root_.SheafOfModules.pushforward φ).map f) =
      (presheafPushforward φ).map ((_root_.SheafOfModules.forget (ringCatSheaf R)).map f) :=
  (rfl)

end SheafOfModules

end

end TauCeti
