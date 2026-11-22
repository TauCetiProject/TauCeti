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

/-- The `B`-algebra structure on `𝒪_P` induced by `B ⊆ 𝒪_P`. -/
@[instance_reducible]
private noncomputable def integersAlgebra {k F B : Type*} [Field k] [Field F] [Algebra k F]
    [CommRing B] [Algebra B F] (P : Place k F) (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    Algebra B P.integers :=
  ((algebraMap B F).codRestrict P.integers hB).toAlgebra

private theorem isScalarTower_integers {k F B : Type*} [Field k] [Field F] [Algebra k F]
    [CommRing B] [Algebra B F] (P : Place k F) (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    letI := integersAlgebra P hB
    IsScalarTower B P.integers F :=
  letI := integersAlgebra P hB
  .of_algebraMap_eq fun b ↦ by
    rw [ValuationSubring.algebraMap_apply, RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply]

private theorem isScalarTower_integers_extension {k F F' B : Type*} [Field k] [Field F] [Field F']
    [Algebra k F] [Algebra F F'] [CommRing B] [Algebra B F] [Algebra B F']
    [IsScalarTower B F F'] (P : Place k F) (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    letI := integersAlgebra P hB
    IsScalarTower B P.integers F' :=
  letI := integersAlgebra P hB
  have := isScalarTower_integers P hB
  IsScalarTower.to₁₂₄ B P.integers F F'

/-- The canonical ring homomorphism from an affine model `C` to the local integral closure
`𝒪'_P` when the base affine model `B` lies in `𝒪_P`. -/
noncomputable def integralClosureHom {k F F' B C : Type*}
    [Field k] [Field F] [Field F'] [Algebra k F] [Algebra F F']
    [CommRing B] [Algebra B F] [CommRing C] [Algebra C F'] [Algebra B F']
    [IsScalarTower B F F'] [IsIntegralClosure C B F']
    (P : Place k F) (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    C →+* integralClosure P.integers F' :=
  letI := integersAlgebra P hB
  haveI := isScalarTower_integers_extension (F' := F') P hB
  (algebraMap C F').codRestrict (integralClosure P.integers F').toSubring fun c ↦
    Subalgebra.mem_toSubring.mpr ((mem_integralClosure_iff _ _).mpr
      (IsIntegral.tower_top (R := B) (A := P.integers)
        ((IsIntegralClosure.isIntegral_iff (A := C) (R := B)).mpr ⟨c, rfl⟩)))

/-- Coercing `TauCeti.Place.integralClosureHom` to `F'` agrees with `algebraMap C F'`. -/
@[simp]
theorem coe_integralClosureHom {k F F' B C : Type*}
    [Field k] [Field F] [Field F'] [Algebra k F] [Algebra F F']
    [CommRing B] [Algebra B F] [CommRing C] [Algebra C F'] [Algebra B F']
    [IsScalarTower B F F'] [IsIntegralClosure C B F']
    (P : Place k F) (hB : ∀ b : B, algebraMap B F b ∈ P.integers) (c : C) :
    (integralClosureHom (F' := F') P hB c : F') = algebraMap C F' c := by
  rw [integralClosureHom, RingHom.codRestrict_apply]

/-- The `C`-algebra structure on `𝒪'_P` induced by `B ⊆ 𝒪_P` when `C` is the integral closure of
`B` in `F'`. -/
@[instance_reducible]
private noncomputable def integralClosureAlgebra {k F F' B C : Type*}
    [Field k] [Field F] [Field F'] [Algebra k F] [Algebra F F']
    [CommRing B] [Algebra B F] [CommRing C] [Algebra C F'] [Algebra B F']
    [IsScalarTower B F F'] [IsIntegralClosure C B F']
    (P : Place k F) (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    Algebra C (integralClosure P.integers F') :=
  (integralClosureHom P hB).toAlgebra

private theorem isScalarTower_integralClosure_field {k F F' B C : Type*}
    [Field k] [Field F] [Field F'] [Algebra k F] [Algebra F F']
    [CommRing B] [Algebra B F] [CommRing C] [Algebra C F'] [Algebra B F']
    [IsScalarTower B F F'] [IsIntegralClosure C B F']
    (P : Place k F) (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    letI := integralClosureAlgebra (F' := F') (B := B) (C := C) P hB
    IsScalarTower C (integralClosure P.integers F') F' :=
  letI := integralClosureAlgebra (F' := F') (B := B) (C := C) P hB
  .of_algebraMap_eq fun c ↦ by
    rw [RingHom.algebraMap_toAlgebra, Subalgebra.algebraMap_apply, coe_integralClosureHom]

/-- Compatibility of `B → C → 𝒪'_P` with `B → 𝒪'_P` given compatibility into `F'`. -/
private theorem isScalarTower_integralClosure {k F F' B C : Type*}
    [Field k] [Field F] [Field F'] [Algebra k F] [Algebra F F']
    [CommRing B] [CommRing C] [Algebra C F'] [Algebra B C] [Algebra B F']
    [IsScalarTower B C F'] (P : Place k F)
    [Algebra B P.integers] [IsScalarTower B P.integers F']
    [Algebra C (integralClosure P.integers F')]
    [IsScalarTower C (integralClosure P.integers F') F'] :
    IsScalarTower B C (integralClosure P.integers F') :=
  IsScalarTower.to₁₂₃ B C (integralClosure P.integers F') F'

omit [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
/-- The local integral closure `𝒪'_P` is the localization of `C` at the complement of the centre
of `P` on `B`. -/
private theorem isLocalization_integralClosure_center (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers)
    [Algebra B P.integers] [IsScalarTower B P.integers F]
    [Algebra C (integralClosure P.integers F')]
    [IsScalarTower C (integralClosure P.integers F') F'] :
    IsLocalization (Algebra.algebraMapSubmonoid C (P.center hB).asIdeal.primeCompl)
      (integralClosure P.integers F') := by
  have : IsLocalization (P.center hB).asIdeal.primeCompl P.integers :=
    P.isLocalization_integers_center hB
  have : IsScalarTower B P.integers F' := IsScalarTower.to₁₂₄ B P.integers F F'
  exact isLocalization_algebraMapSubmonoid_of_isIntegralClosure (R := B) (Rₘ := P.integers)
    (S := C) (Sₘ := integralClosure P.integers F') (L := F') (M := (P.center hB).asIdeal.primeCompl)

/-- **The complementary module of the local model is spanned by the complementary module of any
affine model**: if `B` is a Dedekind affine model of `F` contained in `𝒪_P` and `C` is its
integral closure in `F'`, then `Submodule.traceDual 𝒪_P F 1` is the `𝒪'_P`-span of
`Submodule.traceDual B F 1`. -/
theorem span_traceDual_one_eq_traceDual_one_integralClosure (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    Submodule.span (integralClosure P.integers F')
        (Submodule.traceDual B F (1 : Submodule C F') : Set F') =
      Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F') := by
  let _ : Module.Finite B C := IsIntegralClosure.finite B F F' C
  let _ := integersAlgebra P hB
  have := isScalarTower_integers P hB
  have := isScalarTower_integers_extension (F' := F') P hB
  have : IsLocalization (P.center hB).asIdeal.primeCompl P.integers :=
    P.isLocalization_integers_center hB
  let _ := integralClosureAlgebra (F' := F') (B := B) (C := C) P hB
  have := isScalarTower_integralClosure_field (F' := F') (B := B) (C := C) P hB
  have : IsScalarTower B C (integralClosure P.integers F') := isScalarTower_integralClosure P
  have : IsLocalization (Algebra.algebraMapSubmonoid C (P.center hB).asIdeal.primeCompl)
      (integralClosure P.integers F') :=
    isLocalization_integralClosure_center P hB
  exact TauCeti.span_traceDual_one_eq_traceDual_one (R := B) (Rₘ := P.integers) (S := C)
    (Sₘ := integralClosure P.integers F') (K := F) (L := F') (M := (P.center hB).asIdeal.primeCompl)

/-- **The different ideal of an affine model localizes to the different ideal of the local model**:
if `B` is a Dedekind affine model of `F` contained in `𝒪_P`, `C` is its integral closure in `F'`,
and `f : C →+* 𝒪'_P` is compatible with the inclusions into `F'`, then extending
`differentIdeal B C` along `f` yields `differentIdeal 𝒪_P 𝒪'_P`. -/
theorem map_differentIdeal_eq_differentIdeal_integralClosure [IsDedekindDomain C]
    [Module.IsTorsionFree B C] (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers)
    (f : C →+* integralClosure P.integers F')
    (hf : ∀ c : C, algebraMap (integralClosure P.integers F') F' (f c) = algebraMap C F' c) :
    (differentIdeal B C).map f =
      differentIdeal P.integers (integralClosure P.integers F') := by
  have := IsIntegralClosure.isFractionRing_of_finite_extension B F F' C
  let _ : Module.Finite B C := IsIntegralClosure.finite B F F' C
  let _ := integersAlgebra P hB
  have := isScalarTower_integers P hB
  have := isScalarTower_integers_extension (F' := F') P hB
  have : IsLocalization (P.center hB).asIdeal.primeCompl P.integers :=
    P.isLocalization_integers_center hB
  let _ : Algebra C (integralClosure P.integers F') := f.toAlgebra
  have : IsScalarTower C (integralClosure P.integers F') F' :=
    .of_algebraMap_eq fun c ↦ by rw [RingHom.algebraMap_toAlgebra, hf]
  have : IsScalarTower B C (integralClosure P.integers F') := isScalarTower_integralClosure P
  have : IsLocalization (Algebra.algebraMapSubmonoid C (P.center hB).asIdeal.primeCompl)
      (integralClosure P.integers F') :=
    isLocalization_integralClosure_center P hB
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
  let _ : Module.Finite B C := IsIntegralClosure.finite B F F' C
  let p : HeightOneSpectrum B := P.center hB
  let Bₘ := P.integers
  let Cₘ := integralClosure Bₘ F'
  let _ := integersAlgebra P hB
  have := isScalarTower_integers P hB
  have := isScalarTower_integers_extension (F' := F') P hB
  have : IsLocalization p.asIdeal.primeCompl Bₘ := P.isLocalization_integers_center hB
  let _ := integralClosureAlgebra (F' := F') (B := B) (C := C) P hB
  have := isScalarTower_integralClosure_field (F' := F') (B := B) (C := C) P hB
  have : IsScalarTower B C Cₘ := isScalarTower_integralClosure P
  have : IsLocalization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl) Cₘ :=
    isLocalization_integralClosure_center P hB
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

end Exponent

end Place

end TauCeti

end
