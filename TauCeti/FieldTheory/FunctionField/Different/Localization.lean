/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Basic
public import TauCeti.RingTheory.DedekindDomain.Different.Localization

/-!
# Localizing an affine model to the local model of a place

Let `F' / F` be a finite separable field extension, `P` a place of `F / k`, `B` a Dedekind affine
model of `F` contained in `𝒪_P`, and `C` its integral closure in `F'`. The valuation ring `𝒪_P` is
the localization of `B` at the centre of `P`, and its integral closure `𝒪'_P` in `F'` is the
matching localization of `C`.

Consequently, localizing `B ⊆ C` at the centre of `P` carries the complementary module
`Submodule.traceDual B F 1` onto `Submodule.traceDual 𝒪_P F 1` and carries `differentIdeal B C`
onto `differentIdeal 𝒪_P 𝒪'_P`. For any place `P'` of `F' / k'` lying over `P` and finite on `C`,
this implies that the different exponent `d(P' ∣ P)` equals the coefficient of `differentIdeal B C`
at the centre of `P'` on `C`.

## Main results

* `TauCeti.Place.span_traceDual_one_eq_traceDual_one_integralClosure`: the complementary module of
  the local model `𝒪_P ⊆ 𝒪'_P` is the `𝒪'_P`-span of the complementary module of `B ⊆ C`.
* `TauCeti.Place.map_differentIdeal_eq_differentIdeal_integralClosure`: extending
  `differentIdeal B C` along the canonical embedding `C →+* 𝒪'_P` yields
  `differentIdeal 𝒪_P 𝒪'_P`.
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

section Localize

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable {B : Type*} {C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F]
  [IsFractionRing B F] [CommRing C] [Algebra C F'] [Algebra B C] [Algebra B F']
  [IsScalarTower B C F'] [IsScalarTower B F F'] [IsIntegralClosure C B F']

private theorem with_integralClosure_localization (F' C : Type*) [Field F'] [Algebra F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    [CommRing C] [Algebra C F'] [Algebra B C] [Algebra B F']
    [IsScalarTower B C F'] [IsScalarTower B F F'] [IsIntegralClosure C B F']
    {Q : Prop} (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers)
    [Algebra C (integralClosure P.integers F')]
    [IsScalarTower C (integralClosure P.integers F') F']
    (hQ : ∀ [Algebra B P.integers] [Module.Finite B C] [IsScalarTower B P.integers F]
        [IsScalarTower B P.integers F']
        [IsLocalization (P.center hB).asIdeal.primeCompl P.integers]
        [IsScalarTower B C (integralClosure P.integers F')]
        [IsLocalization (Algebra.algebraMapSubmonoid C (P.center hB).asIdeal.primeCompl)
          (integralClosure P.integers F')], Q) : Q :=
  let _ := integersAlgebra P hB
  have _ : Module.Finite B C := IsIntegralClosure.finite B F F' C
  have _ := isScalarTower_integers P hB
  have _ := isScalarTower_integers_extension (F' := F') P hB
  have _ : IsLocalization (P.center hB).asIdeal.primeCompl P.integers :=
    P.isLocalization_integers_center hB
  have _ : IsScalarTower B C (integralClosure P.integers F') := IsScalarTower.to₁₂₃ B C _ F'
  have _ : IsLocalization (Algebra.algebraMapSubmonoid C (P.center hB).asIdeal.primeCompl)
      (integralClosure P.integers F') :=
    isLocalization_integralClosure_center P hB
  hQ

/-- **The complementary module of the local model is spanned by the complementary module of any
affine model**: if `B` is a Dedekind affine model of `F` contained in `𝒪_P` and `C` is its
integral closure in `F'`, then `Submodule.traceDual 𝒪_P F 1` is the `𝒪'_P`-span of
`Submodule.traceDual B F 1`. -/
theorem span_traceDual_one_eq_traceDual_one_integralClosure (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    Submodule.span (integralClosure P.integers F')
        (Submodule.traceDual B F (1 : Submodule C F') : Set F') =
      Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F') := by
  let _ := integralClosureAlgebra (F' := F') (B := B) (C := C) P hB
  have := isScalarTower_integralClosure_field (F' := F') (B := B) (C := C) P hB
  refine with_integralClosure_localization F' C P hB ?_
  intro _ _ _ _ _ _ _
  exact TauCeti.span_traceDual_one_eq_traceDual_one (R := B) (Rₘ := P.integers) (S := C)
    (Sₘ := integralClosure P.integers F') (K := F) (L := F') (M := (P.center hB).asIdeal.primeCompl)

/-- **The different ideal of an affine model localizes to the different ideal of the local model**:
if `B` is a Dedekind affine model of `F` contained in `𝒪_P`, `C` is its integral closure in `F'`,
and `f : C →+* 𝒪'_P` is compatible with the inclusions into `F'`, then extending
`differentIdeal B C` along `f` yields `differentIdeal 𝒪_P 𝒪'_P`. -/
theorem map_differentIdeal_eq_differentIdeal_integralClosure (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers)
    (f : C →+* integralClosure P.integers F')
    (hf : ∀ c : C, algebraMap (integralClosure P.integers F') F' (f c) = algebraMap C F' c) :
    let _ : IsDomain C :=
      Function.Injective.isDomain (algebraMap C F') (IsIntegralClosure.algebraMap_injective C B F')
    let _ : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain B F F' C
    let _ : Module.IsTorsionFree B C :=
      let _ : Module.IsTorsionFree B F' := .trans_faithfulSMul B F F'
      IsIntegralClosure.isTorsionFree B F'
    (differentIdeal B C).map f =
      differentIdeal P.integers (integralClosure P.integers F') := by
  intro _ _ _
  have := IsIntegralClosure.isFractionRing_of_finite_extension B F F' C
  let _ : Algebra C (integralClosure P.integers F') := f.toAlgebra
  have : IsScalarTower C (integralClosure P.integers F') F' :=
    .of_algebraMap_eq fun c ↦ by rw [RingHom.algebraMap_toAlgebra, hf]
  refine with_integralClosure_localization F' C P hB ?_
  intro _ _ _ _ _ _ _
  simpa only [RingHom.algebraMap_toAlgebra] using
    TauCeti.map_differentIdeal_eq_differentIdeal (R := B) (Rₘ := P.integers) (S := C)
      (Sₘ := integralClosure P.integers F') (K := F) (L := F')
      (M := (P.center hB).asIdeal.primeCompl)

end Localize

section Exponent

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
  let P : Place k F := P'.restrict k F
  have hB : ∀ b : B, algebraMap B F b ∈ P.integers :=
    algebraMap_mem_integers_restrict k F P' hC
  let _ := integralClosureAlgebra (F' := F') (B := B) (C := C) P hB
  have := isScalarTower_integralClosure_field (F' := F') (B := B) (C := C) P hB
  refine with_integralClosure_localization F' C P hB ?_
  intro _ _ _ _ _ _ _
  -- The centre of `P'` on `Cₘ` contracts to the centre on `C`, so localization preserves the
  -- coefficient.
  have hunder : (centerIntegralClosure k F P').asIdeal.under C = (P'.center hC).asIdeal := by
    ext c
    rw [Ideal.mem_under]
    simp only [centerIntegralClosure_def, mem_center_asIdeal]
    rw [← IsScalarTower.algebraMap_apply C (integralClosure P.integers F') F']
  rw [differentExponent_def, ← hunder]
  exact multiplicity_differentIdeal_eq_multiplicity_under (R := B) (Rₘ := P.integers) (S := C)
    (Sₘ := integralClosure P.integers F') (K := F) (L := F') (M := (P.center hB).asIdeal.primeCompl)
    (centerIntegralClosure k F P').ne_bot

end Exponent

end Place

end TauCeti

end
