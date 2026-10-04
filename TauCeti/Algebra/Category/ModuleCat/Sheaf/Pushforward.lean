/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Left exactness of pushforward of module sheaves

Pushforward along a continuous functor of sites preserves finite limits of sheaves of modules.
In particular, restriction to an open subscheme preserves kernels. No cocontinuity or flatness
assumption is needed for this assertion.

The construction uses Mathlib's forgetful functors to presheaves of modules and abelian groups:
they preserve and reflect finite limits, and pushforward on underlying abelian presheaves is
precomposition.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u v v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Pushforward of module sheaves along a continuous functor is left exact. -/
noncomputable instance _root_.SheafOfModules.preservesFiniteLimits_pushforward
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{v} φ) := by
  -- Both composites below forget the module structure and precompose the same presheaf.
  have e : SheafOfModules.pushforward.{v} φ ⋙
      SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj ≅
      (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj F.op := Iso.refl _
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{v} φ ⋙
      SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj) :=
    preservesFiniteLimits_of_natIso e.symm
  have : ReflectsFiniteLimits
      (SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj) :=
    inferInstanceAs (ReflectsFiniteLimits
      (SheafOfModules.toSheaf.{v} S ⋙ sheafToPresheaf J AddCommGrpCat.{v}))
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj)

end TauCeti
