/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Divisor
public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Tower
public import TauCeti.RingTheory.DedekindDomain.Different.Localization
public import TauCeti.RingTheory.DedekindDomain.Different.Tower
public import TauCeti.RingTheory.Localization.Integral

/-!
# The different in a tower of function fields

For a tower of finite separable extensions `F₀ ⊆ F₁ ⊆ F₂`, the different exponent at a place
`P₂` satisfies

`d(P₂ / P₀) = e(P₂ / P₁) d(P₁ / P₀) + d(P₂ / P₁)`.

Consequently the different divisors satisfy

`Diff(F₂ / F₀) = Con(Diff(F₁ / F₀)) + Diff(F₂ / F₁)`.

The proof reads Mathlib's transitivity theorem for different ideals coefficientwise on the local
model over `P₀`.  Its middle layer is an affine model of `F₁` rather than the local model at `P₁`
used to define `d(P₂ / P₁)`; `TauCeti.Place.differentExponent_eq_multiplicity_center` shows that
the different exponent can be read on any affine model, by localizing it at the centre of `P₁`.

This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Corollary 3.4.12.

## Main results

* `TauCeti.Place.differentExponent_eq_multiplicity_center`: the different exponent is the
  coefficient of the different ideal of an affine model at the centre of the place.
* `TauCeti.Place.differentExponent_restrict_add`: transitivity of different exponents.
* `TauCeti.Divisor.different_eq_conorm_add`: transitivity of different divisors.
-/

public section

open IsDedekindDomain Module

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

namespace Place

universe u₀ u₁ u₂ v₀ v₁ v₂

variable {k₀ : Type u₀} {k₁ : Type u₁} {k₂ : Type u₂}
variable {F₀ : Type v₀} {F₁ : Type v₁} {F₂ : Type v₂}
variable [Field k₀] [Field k₁] [Field k₂] [Field F₀] [Field F₁] [Field F₂]
variable [Algebra k₀ k₁] [Algebra k₁ k₂] [Algebra k₀ k₂]
variable [Algebra F₀ F₁] [Algebra F₁ F₂] [Algebra F₀ F₂] [IsScalarTower F₀ F₁ F₂]
variable [Algebra k₀ F₀] [Algebra k₁ F₁] [Algebra k₂ F₂]
variable [Algebra k₀ F₁] [Algebra k₁ F₂] [Algebra k₀ F₂]
variable [IsScalarTower k₀ k₁ F₁] [IsScalarTower k₁ k₂ F₂]
variable [IsScalarTower k₀ F₀ F₁] [IsScalarTower k₁ F₁ F₂]
variable [IsScalarTower k₀ k₂ F₂] [IsScalarTower k₀ F₀ F₂]
variable [FiniteDimensional F₀ F₁] [FiniteDimensional F₁ F₂]
variable [Algebra.IsSeparable F₀ F₁] [Algebra.IsSeparable F₁ F₂]

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section AffineModel

variable {B : Type*} {C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F₁]
  [IsFractionRing B F₁] [CommRing C] [IsDedekindDomain C] [Algebra C F₂] [IsFractionRing C F₂]
  [Algebra B C] [Algebra B F₂] [IsScalarTower B C F₂] [IsScalarTower B F₁ F₂]
  [IsIntegralClosure C B F₂] [Module.IsTorsionFree B C]

/-- **The different exponent can be read on an affine model**: if `P₂` is finite on the integral
closure `C` in `F₂` of an affine model `B` of `F₁`, then `d(P₂ / P₁)` is the coefficient of the
different ideal of `C` over `B` at the centre of `P₂`. -/
theorem differentExponent_eq_multiplicity_center (P₂ : Place k₂ F₂)
    (hC : ∀ c : C, algebraMap C F₂ c ∈ P₂.integers) :
    differentExponent k₁ F₁ P₂ = multiplicity (P₂.center hC).asIdeal (differentIdeal B C) := by
  -- After localizing at the centre of `P₁` (below),
  -- `TauCeti.multiplicity_differentIdeal_eq_multiplicity_under` compares the two coefficients.
  let P₁ : Place k₁ F₁ := P₂.restrict k₁ F₁
  have hB : ∀ b : B, algebraMap B F₁ b ∈ P₁.integers :=
    algebraMap_mem_integers_restrict k₁ F₁ P₂ hC
  let _ : Module.Finite B C := IsIntegralClosure.finite B F₁ F₂ C
  let p : HeightOneSpectrum B := P₁.center hB
  -- Localize at `p`: `𝒪_{P₁}` is the localization of `B`, and its integral closure `Cₘ` in `F₂`
  -- is the matching localization of `C`.  Mathlib's `IsLocalization.integralClosure` is stated
  -- for the literal `integralClosure B F₂`, whereas `C` is an arbitrary integral closure, so
  -- `IsIntegralClosure.isLocalization_of_isLocalization` supplies the abstract version needed.
  let Bₘ := P₁.integers
  let Cₘ := integralClosure Bₘ F₂
  let _ : Algebra B Bₘ := ((algebraMap B F₁).codRestrict Bₘ hB).toAlgebra
  let _ : IsScalarTower B Bₘ F₁ := .of_algebraMap_eq fun _ ↦ rfl
  let eB : HeightOneSpectrum.valuationSubringAtPrime F₁ p ≃ₐ[B] Bₘ :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr
        (congrArg ValuationSubring.toSubring
          (P₁.valuationSubringAtPrime_eq_integers hB)))
      fun _ ↦ rfl
  let _ : IsLocalization p.asIdeal.primeCompl Bₘ :=
    IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl eB
  let _ : IsScalarTower B Bₘ F₂ := .of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply B F₁ F₂ x
  let _ : Algebra C Cₘ :=
    ((algebraMap C F₂).codRestrict Cₘ.toSubring fun c ↦
      IsIntegral.tower_top (R := B) (A := Bₘ)
        ((IsIntegralClosure.isIntegral_iff (A := C) (R := B)).mpr ⟨c, rfl⟩)).toAlgebra
  let _ : IsScalarTower C Cₘ F₂ := .of_algebraMap_eq fun _ ↦ rfl
  let _ : IsScalarTower B C Cₘ := .of_algebraMap_eq fun x ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply B C F₂ x
  let _ : IsScalarTower B Bₘ Cₘ := .of_algebraMap_eq fun x ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply B F₁ F₂ x
  let _ : IsLocalization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl) Cₘ :=
    IsIntegralClosure.isLocalization_of_isLocalization (R := B) (Rₘ := Bₘ) (S := C)
      (Sₘ := Cₘ) (L := F₂) (M := p.asIdeal.primeCompl)
  -- The centre of `P₂` on `Cₘ` contracts to the centre on `C`, so localization preserves the
  -- coefficient.
  have hunder : (centerIntegralClosure k₁ F₁ P₂).asIdeal.under C = (P₂.center hC).asIdeal := by
    ext c
    rw [Ideal.mem_under]
    simp only [centerIntegralClosure_def, mem_center_asIdeal]
    rw [← IsScalarTower.algebraMap_apply C Cₘ F₂]
  rw [differentExponent_def, ← hunder]
  exact multiplicity_differentIdeal_eq_multiplicity_under (R := B) (Rₘ := Bₘ) (S := C)
    (Sₘ := Cₘ) (K := F₁) (L := F₂) (M := p.asIdeal.primeCompl)
    (centerIntegralClosure k₁ F₁ P₂).ne_bot

end AffineModel

section AffineTower

variable (A : Type*) (B : Type*) {C : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A F₀]
  [IsFractionRing A F₀] [CommRing B] [IsDedekindDomain B] [Algebra B F₁] [IsFractionRing B F₁]
  [CommRing C] [IsDedekindDomain C] [Algebra C F₂] [IsFractionRing C F₂]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  [Algebra A F₁] [Algebra A F₂] [Algebra B F₂]
  [IsScalarTower A B F₁] [IsScalarTower A F₀ F₁] [IsScalarTower A B F₂] [IsScalarTower A C F₂]
  [IsScalarTower A F₀ F₂]
  [IsScalarTower B C F₂] [IsScalarTower B F₁ F₂]
  [IsIntegralClosure B A F₁] [IsIntegralClosure C A F₂]

include A B in
/-- The tower law for different exponents, read on any tower of affine models `A ⊆ B ⊆ C` of
`F₀ ⊆ F₁ ⊆ F₂` on which `P₂` is finite: each exponent is the coefficient of a different ideal at
a centre, so the formula is `TauCeti.multiplicity_differentIdeal_tower`. -/
private theorem differentExponent_restrict_add_of_affineModel (P₂ : Place k₂ F₂)
    (hC : ∀ c : C, algebraMap C F₂ c ∈ P₂.integers) :
    haveI : FiniteDimensional F₀ F₂ := FiniteDimensional.trans F₀ F₁ F₂
    haveI : Algebra.IsSeparable F₀ F₂ := Algebra.IsSeparable.trans F₀ F₁ F₂
    differentExponent k₀ F₀ P₂ =
      ramificationIdx F₁ P₂ * differentExponent k₀ F₀ (P₂.restrict k₁ F₁) +
        differentExponent k₁ F₁ P₂ := by
  let _ : FiniteDimensional F₀ F₂ := FiniteDimensional.trans F₀ F₁ F₂
  let _ : Algebra.IsSeparable F₀ F₂ := Algebra.IsSeparable.trans F₀ F₁ F₂
  let _ : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A F₁
  let _ : IsIntegralClosure C B F₂ := IsIntegralClosure.tower_top (R := A)
  let _ : Module.Finite B C := IsIntegralClosure.finite B F₁ F₂ C
  let _ : Module.Finite A B := IsIntegralClosure.finite A F₀ F₁ B
  let _ : Module.IsTorsionFree A F₁ := .trans_faithfulSMul A F₀ F₁
  let _ : Module.IsTorsionFree A F₂ := .trans_faithfulSMul A F₀ F₂
  let _ : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A F₁
  let _ : Module.IsTorsionFree A C := IsIntegralClosure.isTorsionFree A F₂
  -- Transport separability of `F₂ / F₀` to the canonical fraction fields of `A` and `C`.
  let _ : Algebra.IsSeparable (FractionRing A) (FractionRing C) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A F₀).symm.toRingEquiv
      (FractionRing.algEquiv C F₂).symm.toRingEquiv ?_
    apply IsLocalization.ringHom_ext A⁰
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A C F₂, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  let _ : Module.IsTorsionFree B F₂ := .trans_faithfulSMul B F₁ F₂
  let _ : Module.IsTorsionFree B C := IsIntegralClosure.isTorsionFree B F₂
  let P₁ : Place k₁ F₁ := P₂.restrict k₁ F₁
  have hB : ∀ b : B, algebraMap B F₁ b ∈ P₁.integers :=
    algebraMap_mem_integers_restrict k₁ F₁ P₂ hC
  let p : HeightOneSpectrum B := P₁.center hB
  let q : HeightOneSpectrum C := P₂.center hC
  let _ : q.asIdeal.LiesOver p.asIdeal := center_liesOver (R := B) k₁ F₁ P₂ hC
  rw [differentExponent_eq_multiplicity_center (B := A) P₂ hC,
    differentExponent_eq_multiplicity_center (B := A) P₁ hB,
    differentExponent_eq_multiplicity_center (B := B) P₂ hC,
    multiplicity_differentIdeal_tower A p q,
    ramificationIdx_eq_ramificationIdx_center (R := B) k₁ F₁ P₂ hC, add_comm]

end AffineTower

/-- **Different exponents are transitive in towers** (Stichtenoth, Corollary 3.4.12): the
different exponent of `P₂` over `P₀` is the different exponent over `P₁`, plus the exponent of
`P₁` over `P₀` multiplied by `e(P₂ / P₁)`. -/
theorem differentExponent_restrict_add (P₂ : Place k₂ F₂) :
    haveI : FiniteDimensional F₀ F₂ := FiniteDimensional.trans F₀ F₁ F₂
    haveI : Algebra.IsSeparable F₀ F₂ := Algebra.IsSeparable.trans F₀ F₁ F₂
    differentExponent k₀ F₀ P₂ =
      ramificationIdx F₁ P₂ * differentExponent k₀ F₀ (P₂.restrict k₁ F₁) +
        differentExponent k₁ F₁ P₂ := by
  let _ : FiniteDimensional F₀ F₂ := FiniteDimensional.trans F₀ F₁ F₂
  let _ : Algebra.IsSeparable F₀ F₂ := Algebra.IsSeparable.trans F₀ F₁ F₂
  -- Apply the affine-tower law to the local models `B` and `C` over `𝒪_{P₀}`.
  let P₀ : Place k₀ F₀ := (P₂.restrict k₁ F₁).restrict k₀ F₀
  let B := integralClosure P₀.integers F₁
  let C := integralClosure P₀.integers F₂
  have hC : ∀ c : C, algebraMap C F₂ c ∈ P₂.integers := by
    intro c
    exact P₂.mem_integers_of_isIntegral
      (fun (a : (P₂.restrict k₀ F₀).integers) ↦
        (mem_integers_restrict_iff k₀ F₀ P₂ (a : F₀)).mp a.2) <| by
          rw [← restrict_restrict (k₀ := k₀) (F₀ := F₀) (k₁ := k₁) (F₁ := F₁) P₂]
          exact c.2
  let _ : IsScalarTower P₀.integers B F₂ := .of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply F₀ F₁ F₂ (x : F₀)
  let _ : Algebra B C := (IsIntegralClosure.lift P₀.integers C F₂).toAlgebra
  let _ : IsScalarTower B C F₂ := .of_algebraMap_eq fun x ↦
    (IsIntegralClosure.algebraMap_lift P₀.integers C F₂ x).symm
  let _ : IsScalarTower P₀.integers B C := .of_algebraMap_eq fun x ↦
    IsIntegralClosure.algebraMap_injective C P₀.integers F₂ <| by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply B C F₂,
        ← IsScalarTower.algebraMap_apply]
  exact differentExponent_restrict_add_of_affineModel P₀.integers B P₂ hC

end Place

namespace Divisor

open AlgebraicGeometry

variable {k₀ : Type u₀} {k₁ : Type u₁} {k₂ : Type u₂}
variable {F₀ : Type v₀} {F₁ : Type v₁} {F₂ : Type v₂}
variable [Field k₀] [Field k₁] [Field k₂] [Field F₀] [Field F₁] [Field F₂]
variable [Algebra k₀ k₁] [Algebra k₁ k₂] [Algebra k₀ k₂]
variable [Algebra F₀ F₁] [Algebra F₁ F₂] [Algebra F₀ F₂] [IsScalarTower F₀ F₁ F₂]
variable [Algebra k₀ F₀] [Algebra k₁ F₁] [Algebra k₂ F₂]
variable [Algebra k₀ F₁] [Algebra k₁ F₂] [Algebra k₀ F₂]
variable [IsScalarTower k₀ k₁ F₁] [IsScalarTower k₁ k₂ F₂]
variable [IsScalarTower k₀ F₀ F₁] [IsScalarTower k₁ F₁ F₂]
variable [IsScalarTower k₀ k₂ F₂] [IsScalarTower k₀ F₀ F₂]
variable [FiniteDimensional F₀ F₁] [FiniteDimensional F₁ F₂]
variable [Algebra.IsSeparable F₀ F₁] [Algebra.IsSeparable F₁ F₂]

/-- **Different divisors are transitive in towers** (Stichtenoth, Corollary 3.4.12): the
different of `F₂ / F₀` is the conorm of the different of `F₁ / F₀`, plus the different of
`F₂ / F₁`. -/
theorem different_eq_conorm_add (hF₀ : IsFunctionField k₀ F₀)
    (hF₁ : IsFunctionField k₁ F₁) :
    haveI : FiniteDimensional F₀ F₂ := FiniteDimensional.trans F₀ F₁ F₂
    haveI : Algebra.IsSeparable F₀ F₂ := Algebra.IsSeparable.trans F₀ F₁ F₂
    different k₂ F₂ hF₀ =
      conorm k₂ F₂ (different k₁ F₁ hF₀) + different k₂ F₂ hF₁ := by
  let _ : FiniteDimensional F₀ F₂ := FiniteDimensional.trans F₀ F₁ F₂
  let _ : Algebra.IsSeparable F₀ F₂ := Algebra.IsSeparable.trans F₀ F₁ F₂
  ext P₂
  simp only [coeff_different, WeilDivisor.coeff_add, coeff_conorm]
  exact_mod_cast Place.differentExponent_restrict_add P₂

end Divisor

end TauCeti

end
