/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralClosure
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

* `TauCeti.Place.map_differentIdeal_eq_differentIdeal_of_isIntegralClosure`: extending the
  different ideal of `C / B` to `integralClosure P.integers F'` gives
  `differentIdeal P.integers (integralClosure P.integers F')`.
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

section BasePlace

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F'] [Algebra k F] [Algebra F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension
attribute [local instance] isScalarTower_integersOfForallMem
  isScalarTower_integersOfForallMem_extension
  isScalarTower_integersOfForallMem_integralClosure
  isScalarTower_integralClosureOfForallMemIntegers
  isScalarTower_left_integralClosureOfForallMemIntegers

section LocalModelLocalization

variable {B : Type*} {C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F]
  [IsFractionRing B F] [CommRing C] [IsDedekindDomain C] [Algebra C F']
  [Algebra B C] [Algebra B F'] [IsScalarTower B C F'] [IsScalarTower B F F']
  [IsIntegralClosure C B F']

@[local instance]
private theorem isLocalization_baseLocalModel (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    letI := P.algebraIntegersOfForallMem hB
    IsLocalization (P.center hB).asIdeal.primeCompl P.integers := by
  let _ := P.algebraIntegersOfForallMem hB
  let eB : HeightOneSpectrum.valuationSubringAtPrime F (P.center hB) ≃ₐ[B] P.integers :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr
        (congrArg ValuationSubring.toSubring (P.valuationSubringAtPrime_eq_integers hB)))
      fun x ↦ Subtype.ext (P.coe_algebraMap_integersOfForallMem hB x).symm
  exact IsLocalization.isLocalization_of_algEquiv (P.center hB).asIdeal.primeCompl eB

@[local instance]
private theorem isLocalization_localModel (C : Type*) [CommRing C] [Algebra C F']
    [Algebra B C] [IsScalarTower B C F'] [IsIntegralClosure C B F']
    (P : Place k F) (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    letI := P.algebraIntegersOfForallMem hB
    letI := P.algebraIntegralClosureOfForallMemIntegers C F' hB
    IsLocalization (Algebra.algebraMapSubmonoid C (P.center hB).asIdeal.primeCompl)
      (integralClosure P.integers F') := by
  let _ := P.algebraIntegersOfForallMem hB
  let _ := P.algebraIntegralClosureOfForallMemIntegers C F' hB
  exact isLocalization_algebraMapSubmonoid_of_isIntegralClosure (R := B) (Rₘ := P.integers)
    (S := C) (Sₘ := integralClosure P.integers F') (L := F')
    (M := (P.center hB).asIdeal.primeCompl)

/-- **Localizing the different ideal of an integral closure to the local model at `P`.** If `C` is
the integral closure in `F'` of a Dedekind model `B` of `F` on which `P` is finite, extending
`differentIdeal B C` to `integralClosure P.integers F'` gives
`differentIdeal P.integers (integralClosure P.integers F')`. -/
theorem map_differentIdeal_eq_differentIdeal_of_isIntegralClosure
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Module.IsTorsionFree B C]
    (P : Place k F) (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    (differentIdeal B C).map
        ((algebraMap C F').codRestrict (integralClosure P.integers F')
          (algebraMap_mem_integralClosure_of_forall_mem_integers (B := B) P hB)) =
      differentIdeal P.integers (integralClosure P.integers F') := by
  have : Module.Finite B C := IsIntegralClosure.finite B F F' C
  have : IsFractionRing C F' := IsIntegralClosure.isFractionRing_of_finite_extension B F F' C
  let _ := P.algebraIntegersOfForallMem hB
  let _ := P.algebraIntegralClosureOfForallMemIntegers C F' hB
  have hmap : (algebraMap C F').codRestrict (integralClosure P.integers F')
      (algebraMap_mem_integralClosure_of_forall_mem_integers (B := B) P hB) =
        algebraMap C (integralClosure P.integers F') :=
    RingHom.ext fun c ↦ Subtype.ext
      (P.coe_algebraMap_integralClosureOfForallMemIntegers (B := B) hB c).symm
  rw [hmap]
  exact TauCeti.map_differentIdeal_eq_differentIdeal (R := B) (Rₘ := P.integers) (S := C)
    (Sₘ := integralClosure P.integers F') (K := F) (L := F')
    (M := (P.center hB).asIdeal.primeCompl)

end LocalModelLocalization

end BasePlace

section DifferentExponent

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra k F']
variable [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension
attribute [local instance] isScalarTower_integersOfForallMem
  isScalarTower_integersOfForallMem_extension
  isScalarTower_integersOfForallMem_integralClosure
  isScalarTower_integralClosureOfForallMemIntegers
  isScalarTower_left_integralClosureOfForallMemIntegers
  isLocalization_baseLocalModel isLocalization_localModel

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
  let P : Place k F := P'.restrict k F
  have hB : ∀ b : B, algebraMap B F b ∈ P.integers :=
    algebraMap_mem_integers_restrict k F P' hC
  have : Module.Finite B C := IsIntegralClosure.finite B F F' C
  let _ := P.algebraIntegersOfForallMem hB
  let _ := P.algebraIntegralClosureOfForallMemIntegers C F' hB
  have hunder : (centerIntegralClosure k F P').asIdeal.under C = (P'.center hC).asIdeal := by
    ext c
    rw [Ideal.mem_under]
    simp only [centerIntegralClosure_def, mem_center_asIdeal]
    rw [← IsScalarTower.algebraMap_apply C (integralClosure P.integers F') F']
  rw [differentExponent_def, ← hunder]
  exact multiplicity_differentIdeal_eq_multiplicity_under (R := B) (Rₘ := P.integers) (S := C)
    (Sₘ := integralClosure P.integers F') (K := F) (L := F')
    (M := (P.center hB).asIdeal.primeCompl) (centerIntegralClosure k F P').ne_bot

end DifferentExponent

end Place

end TauCeti

end
