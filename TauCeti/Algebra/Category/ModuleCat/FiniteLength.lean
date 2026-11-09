/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteLength
public import TauCeti.Algebra.Category.ModuleCat.Quotient

/-!
# Extension-closed properties of finite-length modules

An object property holding on zero and simple modules and closed under short exact extensions
holds on every finite-length module. This packages composition-series induction in `ModuleCat`.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type v} [Ring R]

/-- An extension-closed property holding on zero and simple modules holds on every
finite-length module. -/
theorem prop_of_isFiniteLength (X : ModuleCat.{u} R) (hX : IsFiniteLength R X)
    (P : ObjectProperty (ModuleCat.{u} R))
    (hzero : ∀ M : ModuleCat.{u} R, IsZero M → P M)
    (hsimple : ∀ M : ModuleCat.{u} R, IsSimpleModule R M → P M)
    (hext : ∀ {S : ShortComplex (ModuleCat.{u} R)}, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂) :
    P X := by
  suffices key : ∀ (M : Type u) [AddCommGroup M] [Module R M], IsFiniteLength R M →
      P (ModuleCat.of R M) from key X hX
  intro M _ _ hM
  induction hM with
  | of_subsingleton => exact hzero _ (ModuleCat.isZero_of_subsingleton _)
  | @of_simple_quotient M _ _ L _ _ ih =>
    exact hext L.shortExact_quotientShortComplex ih (hsimple _ inferInstance)

end ModuleCat
