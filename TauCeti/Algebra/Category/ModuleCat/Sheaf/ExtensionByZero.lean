/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExtensionByZero

/-!
# Extension by zero and injective module sheaves

On a preorder site, extension by zero from a lower interval is exact: it is
presheaf extension by zero followed by sheafification. Consequently restriction
to a lower interval preserves injective sheaves of modules. For open subsets
this is the injectivity property needed to restrict injective resolutions.

The proof uses Mathlib's sheaf-module pullback construction and uniqueness of
left adjoints to identify its canonical pullback with exact extension by zero.
-/

public section

open CategoryTheory Limits

namespace SheafOfModules

universe u v w

noncomputable section

variable {P : Type u} [Preorder P] {J : GrothendieckTopology P}
  (R : Sheaf J RingCat.{w}) (U : P)

section

variable [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Restriction to a lower interval is a right adjoint on sheaves of modules.
Its left adjoint is extension by zero. -/
instance isRightAdjoint_pushforward_over :
    (SheafOfModules.pushforward.{v} (F := Over.forget U) (𝟙 (R.over U))).IsRightAdjoint := by
  -- Name the continuous-site ring map so its presheaf projection is available
  -- to instance search, while retaining Mathlib's canonical module pullback.
  let φ : R.over U ⟶
      ((Over.forget U).sheafPushforwardContinuous RingCat (J.over U) J).obj R := 𝟙 _
  have : (PresheafOfModules.pushforward.{v} φ.hom).IsRightAdjoint :=
    inferInstanceAs (PresheafOfModules.pushforward.{v} (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R.obj))).IsRightAdjoint
  exact (SheafOfModules.PullbackConstruction.adjunction φ).isRightAdjoint

/-- The public restriction-functor presentation is also a right adjoint. Its
semireducible wrapper needs a separate instance for instance search to match. -/
instance isRightAdjoint_overFunctor : (SheafOfModules.overFunctor.{v} R U).IsRightAdjoint :=
  inferInstanceAs
    (SheafOfModules.pushforward.{v} (F := Over.forget U) (𝟙 (R.over U))).IsRightAdjoint

end

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Extension by zero from a lower interval of a preorder site preserves finite
limits and is therefore exact. -/
instance preservesFiniteLimits_pullback_over :
    PreservesFiniteLimits (SheafOfModules.pullback.{v} (F := Over.forget U) (𝟙 (R.over U))) := by
  -- Name the continuous-site ring map so its presheaf projection is available
  -- to instance search, while retaining Mathlib's canonical module pullback.
  let φ : R.over U ⟶
      ((Over.forget U).sheafPushforwardContinuous RingCat (J.over U) J).obj R := 𝟙 _
  have : (PresheafOfModules.pushforward.{v} φ.hom).IsRightAdjoint :=
    inferInstanceAs (PresheafOfModules.pushforward.{v} (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R.obj))).IsRightAdjoint
  have : PreservesFiniteLimits (PresheafOfModules.pullback.{v} φ.hom) :=
    inferInstanceAs (PreservesFiniteLimits
      (PresheafOfModules.pullback.{v} (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ R.obj))))
  exact preservesFiniteLimits_of_natIso (SheafOfModules.pullbackIso φ).symm

/-- Restricting an injective sheaf of modules to a lower interval of a preorder
site gives an injective sheaf of modules. -/
instance preservesInjectiveObjects_overFunctor :
    (SheafOfModules.overFunctor.{v} R U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (SheafOfModules.pullbackPushforwardAdjunction (F := Over.forget U) (𝟙 (R.over U)))

end

end SheafOfModules
