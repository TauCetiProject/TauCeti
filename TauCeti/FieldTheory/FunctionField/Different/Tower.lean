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

/-!
# The different in a tower of function fields

For a tower of finite separable extensions `F₀ ⊆ F₁ ⊆ F₂`, the different exponent at a place
`P₂` satisfies

`d(P₂ / P₀) = e(P₂ / P₁) d(P₁ / P₀) + d(P₂ / P₁)`.

Consequently the different divisors satisfy

`Diff(F₂ / F₀) = Con(Diff(F₁ / F₀)) + Diff(F₂ / F₁)`.

The proof reads Mathlib's transitivity theorem for different ideals coefficientwise.  The local
model over `P₀` is then localized at `P₁`;
`TauCeti.multiplicity_differentIdeal_eq_multiplicity_under` identifies the coefficient of the
relative different with the one on the local model used to define `d(P₂ / P₁)`.

This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Corollary 3.4.12.

## Main results

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
  -- Work over the local model `𝒪_{P₀}`: `B` and `C` are its integral closures in `F₁` and `F₂`,
  -- `p` and `q` are the centres of `P₁` and `P₂` on them, and `q` lies over `p`.
  let P₁ : Place k₁ F₁ := P₂.restrict k₁ F₁
  let P₀ : Place k₀ F₀ := P₁.restrict k₀ F₀
  let B := integralClosure P₀.integers F₁
  let C := integralClosure P₀.integers F₂
  have hB : ∀ b : B, algebraMap B F₁ b ∈ P₁.integers := by
    intro b
    exact algebraMap_mem_integers_of_mem_integralClosure k₀ F₀ P₁ b
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
  let _ : IsScalarTower P₀.integers B C := .of_algebraMap_eq fun x ↦ by
    apply Subtype.ext
    calc
      (↑(algebraMap P₀.integers C x) : F₂) = algebraMap P₀.integers F₂ x :=
        (IsScalarTower.algebraMap_apply P₀.integers C F₂ x).symm
      _ = algebraMap B F₂ (algebraMap P₀.integers B x) :=
        IsScalarTower.algebraMap_apply P₀.integers B F₂ x
      _ = ↑(algebraMap B C (algebraMap P₀.integers B x)) :=
        IsScalarTower.algebraMap_apply B C F₂ (algebraMap P₀.integers B x)
  let _ : IsIntegralClosure C B F₂ := IsIntegralClosure.tower_top (R := P₀.integers)
  let _ : Module.Finite B C := IsIntegralClosure.finite B F₁ F₂ C
  let _ : Module.IsTorsionFree P₀.integers B :=
    IsIntegralClosure.isTorsionFree P₀.integers F₁
  let _ : Module.IsTorsionFree P₀.integers C :=
    IsIntegralClosure.isTorsionFree P₀.integers F₂
  let _ : Module.IsTorsionFree B F₂ := .trans_faithfulSMul B F₁ F₂
  let _ : Module.IsTorsionFree B C := IsIntegralClosure.isTorsionFree B F₂
  let p : HeightOneSpectrum B := P₁.center hB
  let q : HeightOneSpectrum C := P₂.center hC
  let _ : q.asIdeal.LiesOver p.asIdeal := by
    simpa only [p, q, P₁] using center_liesOver (R := B) k₁ F₁ P₂ hC
  -- Localize at `p`: `𝒪_{P₁}` is the localization of `B`, and its integral closure `Cₘ` in `F₂`
  -- is the matching localization of `C`.  Mathlib's `IsLocalization.integralClosure` is stated
  -- for the literal `integralClosure B F₂`, whereas `C` is the integral closure of `𝒪_{P₀}`, so
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
  let _ : IsScalarTower B Bₘ F₂ := .of_algebraMap_eq fun _ ↦ rfl
  let _ : Algebra C Cₘ :=
    (C.val.toRingHom.codRestrict Cₘ.toSubring fun c ↦
      IsIntegral.tower_top (R := B) (A := Bₘ)
        ((IsIntegralClosure.isIntegral_iff (A := C) (R := B)).mpr ⟨c, rfl⟩)).toAlgebra
  let _ : IsScalarTower C Cₘ F₂ := .of_algebraMap_eq fun _ ↦ rfl
  let _ : IsScalarTower B C Cₘ := .of_algebraMap_eq fun x ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply B C F₂ x
  let _ : IsScalarTower B Bₘ Cₘ := .of_algebraMap_eq fun x ↦ by
    apply Subtype.ext
    rfl
  let _ : IsLocalization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl) Cₘ :=
    IsIntegralClosure.isLocalization_of_isLocalization (R := B) (Rₘ := Bₘ) (S := C)
      (Sₘ := Cₘ) (L := F₂) (M := p.asIdeal.primeCompl)
  -- The centre of `P₂` on `Cₘ` contracts to `q`, so localization preserves the coefficient.
  have hq_under : (centerIntegralClosure k₁ F₁ P₂).asIdeal.under C = q.asIdeal := by
    ext c
    rw [Ideal.mem_under]
    simp only [centerIntegralClosure_def, q, mem_center_asIdeal]
    rw [← IsScalarTower.algebraMap_apply C Cₘ F₂]
  have hlocal : multiplicity q.asIdeal (differentIdeal B C) = differentExponent k₁ F₁ P₂ := by
    rw [differentExponent_def, ← hq_under]
    exact (multiplicity_differentIdeal_eq_multiplicity_under (R := B) (Rₘ := Bₘ) (S := C)
      (Sₘ := Cₘ) (K := F₁) (L := F₂) (M := p.asIdeal.primeCompl)
      (centerIntegralClosure k₁ F₁ P₂).ne_bot).symm
  -- Read the tower law for different ideals at `q`, and identify each coefficient.
  have hP₀ : P₂.restrict k₀ F₀ = P₀ :=
    (restrict_restrict (k₀ := k₀) (F₀ := F₀) (k₁ := k₁) (F₁ := F₁) P₂).symm
  have hexp₂ : differentExponent k₀ F₀ P₂ =
      multiplicity q.asIdeal (differentIdeal P₀.integers C) := by
    clear_value P₀
    subst hP₀
    rw [differentExponent_def, centerIntegralClosure_def]
  have hexp₁ : differentExponent k₀ F₀ P₁ =
      multiplicity p.asIdeal (differentIdeal P₀.integers B) := by
    rw [differentExponent_def, centerIntegralClosure_def]
  rw [hexp₂, multiplicity_differentIdeal_tower P₀.integers p q, hlocal, ← hexp₁,
    ← ramificationIdx_eq_ramificationIdx_center (R := B) k₁ F₁ P₂ hC, add_comm]

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
