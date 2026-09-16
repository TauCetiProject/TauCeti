/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Basic
public import TauCeti.RingTheory.DedekindDomain.Different.Localization
public import TauCeti.RingTheory.Localization.Integral

/-!
# Reading the different exponent on an arbitrary affine model

The different exponent `d(P' ∣ P)` of a place `P'` of `F' / k'` is defined on the local model
`𝒪_P ⊆ 𝒪'_P` at `P = P'.restrict k F`.  This file shows that it may be read on *any* affine model
of `F` on which `P'` is finite: if `B` is such a model and `C` is its integral closure in `F'`,
then `d(P' ∣ P)` is the coefficient of `differentIdeal B C` at the centre of `P'` on `C`.

The local model is the localization of `B` at the centre of `P`, and `𝒪'_P` is the matching
localization of `C`, so this is the localization invariance of the coefficients of the different
ideal, `TauCeti.multiplicity_differentIdeal_eq_multiplicity_under`.

## Main results

* `TauCeti.Place.differentExponent_eq_multiplicity_center`: the different exponent is the
  coefficient of the different ideal of an affine model at the centre of the place.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.4.
-/

public section

open IsDedekindDomain Module

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra k F']
variable [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable {B : Type*} {C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F]
  [IsFractionRing B F] [CommRing C] [IsDedekindDomain C] [Algebra C F'] [IsFractionRing C F']
  [Algebra B C] [Algebra B F'] [IsScalarTower B C F'] [IsScalarTower B F F']
  [IsIntegralClosure C B F'] [Module.IsTorsionFree B C]

/-- **The different exponent can be read on an affine model**: if `P'` is finite on the integral
closure `C` in `F'` of an affine model `B` of `F`, then `d(P' ∣ P)` is the coefficient of the
different ideal of `C` over `B` at the centre of `P'`. -/
theorem differentExponent_eq_multiplicity_center (P' : Place k' F')
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    differentExponent k F P' = multiplicity (P'.center hC).asIdeal (differentIdeal B C) := by
  -- After localizing at the centre of `P` (below),
  -- `TauCeti.multiplicity_differentIdeal_eq_multiplicity_under` compares the two coefficients.
  let P : Place k F := P'.restrict k F
  have hB : ∀ b : B, algebraMap B F b ∈ P.integers :=
    algebraMap_mem_integers_restrict k F P' hC
  let _ : Module.Finite B C := IsIntegralClosure.finite B F F' C
  let p : HeightOneSpectrum B := P.center hB
  -- Localize at `p`: `𝒪_P` is the localization of `B`, and its integral closure `Cₘ` in `F'`
  -- is the matching localization of `C`.  Mathlib's `IsLocalization.integralClosure` is stated
  -- for the literal `integralClosure B F'`, whereas `C` is an arbitrary integral closure, so
  -- `TauCeti.isLocalization_algebraMapSubmonoid_of_isIntegralClosure` supplies the abstract
  -- version needed.
  let Bₘ := P.integers
  let Cₘ := integralClosure Bₘ F'
  let _ : Algebra B Bₘ := ((algebraMap B F).codRestrict Bₘ hB).toAlgebra
  let _ : IsScalarTower B Bₘ F := .of_algebraMap_eq fun _ ↦ rfl
  let eB : HeightOneSpectrum.valuationSubringAtPrime F p ≃ₐ[B] Bₘ :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr
        (congrArg ValuationSubring.toSubring
          (P.valuationSubringAtPrime_eq_integers hB)))
      fun _ ↦ rfl
  let _ : IsLocalization p.asIdeal.primeCompl Bₘ :=
    IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl eB
  let _ : IsScalarTower B Bₘ F' := .of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply B F F' x
  let _ : Algebra C Cₘ :=
    ((algebraMap C F').codRestrict Cₘ.toSubring fun c ↦
      IsIntegral.tower_top (R := B) (A := Bₘ)
        ((IsIntegralClosure.isIntegral_iff (A := C) (R := B)).mpr ⟨c, rfl⟩)).toAlgebra
  let _ : IsScalarTower C Cₘ F' := .of_algebraMap_eq fun _ ↦ rfl
  let _ : IsScalarTower B C Cₘ := .of_algebraMap_eq fun x ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply B C F' x
  let _ : IsScalarTower B Bₘ Cₘ := .of_algebraMap_eq fun x ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply B F F' x
  let _ : IsLocalization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl) Cₘ :=
    isLocalization_algebraMapSubmonoid_of_isIntegralClosure (R := B) (Rₘ := Bₘ) (S := C)
      (Sₘ := Cₘ) (L := F') (M := p.asIdeal.primeCompl)
  -- The centre of `P'` on `Cₘ` contracts to the centre on `C`, so localization preserves the
  -- coefficient.
  have hunder : (centerIntegralClosure k F P').asIdeal.under C = (P'.center hC).asIdeal := by
    ext c
    rw [Ideal.mem_under]
    simp only [centerIntegralClosure_def, mem_center_asIdeal]
    rw [← IsScalarTower.algebraMap_apply C Cₘ F']
  rw [differentExponent_def, ← hunder]
  exact multiplicity_differentIdeal_eq_multiplicity_under (R := B) (Rₘ := Bₘ) (S := C)
    (Sₘ := Cₘ) (K := F) (L := F') (M := p.asIdeal.primeCompl)
    (centerIntegralClosure k F P').ne_bot

end Place

end TauCeti

end
