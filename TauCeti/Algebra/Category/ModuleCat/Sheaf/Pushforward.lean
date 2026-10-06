/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Limits of pushforward of module sheaves

Pushforward along a continuous functor of sites preserves small limits of sheaves of modules.
In particular, restriction to an open subscheme preserves kernels. No cocontinuity or flatness
assumption is needed for this assertion.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u v v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]

/-- Forgetting the module and sheaf structures after pushforward gives precomposition of
the underlying presheaf of abelian groups. The comparison is the identity on every section. -/
noncomputable def SheafOfModules.pushforwardCompToPresheaf
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    SheafOfModules.pushforward.{v} φ ⋙
      SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj ≅
      (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj F.op :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _))

/-- The pushforward comparison acts as the identity on sections. -/
@[simp]
lemma SheafOfModules.pushforwardCompToPresheaf_hom_app_app
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (M : SheafOfModules.{v} R) (X : Cᵒᵖ) :
    ((SheafOfModules.pushforwardCompToPresheaf φ).hom.app M).app X = 𝟙 _ := (rfl)

/-- The inverse pushforward comparison acts as the identity on sections. -/
@[simp]
lemma SheafOfModules.pushforwardCompToPresheaf_inv_app_app
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (M : SheafOfModules.{v} R) (X : Cᵒᵖ) :
    ((SheafOfModules.pushforwardCompToPresheaf φ).inv.app M).app X = 𝟙 _ := (rfl)

/-- Pushforward of module sheaves along a continuous functor preserves limits indexed by
categories whose objects and morphisms lie in the universe of the underlying modules. -/
noncomputable instance SheafOfModules.preservesLimitsOfSize_pushforward
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesLimitsOfSize.{v, v} (SheafOfModules.pushforward.{v} φ) := by
  have : PreservesLimitsOfSize.{v, v} (SheafOfModules.pushforward.{v} φ ⋙
      SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj) :=
    preservesLimits_of_natIso (SheafOfModules.pushforwardCompToPresheaf φ).symm
  have : ReflectsLimitsOfSize.{v, v}
      (SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj) :=
    reflectsLimits_of_reflectsIsomorphisms
  exact preservesLimits_of_reflects_of_preserves _
    (SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj)

/-- Pushforward of module sheaves along a continuous functor is left exact. -/
noncomputable instance SheafOfModules.preservesFiniteLimits_pushforward
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{v} φ) :=
  PreservesLimitsOfSize.preservesFiniteLimits.{v, v} _

end TauCeti
