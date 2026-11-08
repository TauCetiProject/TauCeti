/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.FiniteLength
public import TauCeti.Algebra.Category.ModuleCat.Quotient
public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.CategoryTheory.ObjectProperty.Retract

/-!
# Finite-length modules

An object property holding on zero and simple modules and closed under short exact extensions
holds on every finite-length module. This packages composition-series induction in `ModuleCat`.

The finite-length modules form the object property `ModuleCat.isFiniteLength R`, closed under
subobjects (hence retracts and isomorphisms) and finite products.
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

variable (R) in
/-- The finite-length modules, as a property of objects of `ModuleCat R`. -/
def isFiniteLength : ObjectProperty (ModuleCat.{u} R) := fun M ↦ IsFiniteLength R M

@[simp]
theorem isFiniteLength_iff (M : ModuleCat.{u} R) : isFiniteLength R M ↔ IsFiniteLength R M :=
  Iff.rfl

instance : (isFiniteLength.{u} R).IsClosedUnderSubobjects where
  prop_of_mono f _ h :=
    IsFiniteLength.of_injective h ((ModuleCat.mono_iff_injective f).1 inferInstance)

instance : (isFiniteLength.{u} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    IsFiniteLength.of_subsingleton⟩

instance : (isFiniteLength.{u} R).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN ↦ by
    obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hM
    obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hN
    let e := (ModuleCat.biprodIsoProd M N).toLinearEquiv.symm
    exact isFiniteLength_iff_isNoetherian_isArtinian.2
      ⟨isNoetherian_of_linearEquiv e, isArtinian_of_linearEquiv e⟩

instance : (isFiniteLength.{u} R).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

end ModuleCat
