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
model over `P₀` is then localized at `P₁`; `TauCeti.map_differentIdeal_eq_differentIdeal` identifies
the localized relative different with the local model used to define `d(P₂ / P₁)`.

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

private theorem differentExponent_eq_multiplicity_of_restrict_eq
    {k : Type u₀} {k' : Type u₁} {F : Type v₀} {F' : Type v₁}
    [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F]
    [Algebra k' F'] [Algebra F F'] [Algebra k F'] [IsScalarTower k k' F']
    [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (P' : Place k' F') (P : Place k F) (hP : P'.restrict k F = P)
    (hS : ∀ s : integralClosure P.integers F',
      algebraMap (integralClosure P.integers F') F' s ∈ P'.integers) :
    differentExponent k F P' =
      multiplicity (P'.center hS).asIdeal
        (differentIdeal P.integers (integralClosure P.integers F')) := by
  subst P
  rw [differentExponent_def, centerIntegralClosure_def]

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
  let _ : IsScalarTower P₀.integers B F₂ := .of_algebraMap_eq fun x ↦ by
    change algebraMap F₀ F₂ (x : F₀) = algebraMap F₁ F₂ (algebraMap F₀ F₁ (x : F₀))
    exact IsScalarTower.algebraMap_apply F₀ F₁ F₂ (x : F₀)
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
  have htower := multiplicity_differentIdeal_tower (A := P₀.integers) p q
  have hlocal : multiplicity q.asIdeal (differentIdeal P₀.integers C) =
      ramificationIdx F₁ P₂ * multiplicity p.asIdeal (differentIdeal P₀.integers B) +
        differentExponent k₁ F₁ P₂ := by
    rw [differentExponent_def, htower, add_comm]
    congr 1
    · rw [ramificationIdx_eq_ramificationIdx_center (R := B) k₁ F₁ P₂ hC]
    · let Bₘ := P₁.integers
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
      have hCmap (c : C) : algebraMap C F₂ c = (c : F₂) := by
        change algebraMap F₂ F₂ (c : F₂) = (c : F₂)
        rw [Algebra.algebraMap_self_apply]
      let _ : Algebra C Cₘ :=
        (C.val.toRingHom.codRestrict Cₘ.toSubring fun c ↦ by
          have hc : IsIntegral B (c : F₂) := by
            apply (IsIntegralClosure.isIntegral_iff (A := C) (R := B)).mpr
            exact ⟨c, hCmap c⟩
          exact IsIntegral.tower_top (R := B) (A := Bₘ) hc).toAlgebra
      let _ : IsScalarTower C Cₘ F₂ := .of_algebraMap_eq fun _ ↦ rfl
      have hCₘmap (c : Cₘ) : algebraMap Cₘ F₂ c = (c : F₂) := by
        change algebraMap F₂ F₂ (c : F₂) = (c : F₂)
        rw [Algebra.algebraMap_self_apply]
      let _ : IsScalarTower B C Cₘ := .of_algebraMap_eq fun x ↦ by
        apply Subtype.ext
        exact IsScalarTower.algebraMap_apply B C F₂ x
      let _ : IsScalarTower B Bₘ Cₘ := .of_algebraMap_eq fun x ↦ by
        apply Subtype.ext
        rfl
      let _ : IsLocalization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl) Cₘ :=
        ⟨⟨by
          rintro ⟨_, m, hm, rfl⟩
          change IsUnit (algebraMap C Cₘ (algebraMap B C m))
          rw [← IsScalarTower.algebraMap_apply B C Cₘ]
          exact (IsLocalization.map_units Bₘ ⟨m, hm⟩).map (algebraMap Bₘ Cₘ), by
          intro y
          obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
            (R := B) (Rₘ := Bₘ) p.asIdeal.primeCompl (y : F₂)
              (by
                apply (IsIntegralClosure.isIntegral_iff (A := Cₘ) (R := Bₘ)).mpr
                exact ⟨y, rfl⟩)
          obtain ⟨c, hc⟩ := (IsIntegralClosure.isIntegral_iff (A := C) (R := B)).mp hm
          refine ⟨⟨c, algebraMap B C m, m, m.2, rfl⟩, ?_⟩
          apply IsIntegralClosure.algebraMap_injective Cₘ Bₘ F₂
          rw [map_mul, hCₘmap, ← IsScalarTower.algebraMap_apply C Cₘ F₂,
            ← IsScalarTower.algebraMap_apply C Cₘ F₂,
            ← IsScalarTower.algebraMap_apply B C F₂, hc,
            Submonoid.smul_def, Algebra.smul_def, mul_comm], by
          intro x y hxy
          refine ⟨1, ?_⟩
          simp only [Submonoid.coe_one, one_mul]
          apply IsIntegralClosure.algebraMap_injective C B F₂
          have h := congrArg (algebraMap Cₘ F₂) hxy
          simpa only [IsScalarTower.algebraMap_apply C Cₘ F₂] using h⟩⟩
      let _ : Module.IsTorsionFree C Cₘ :=
        Module.isTorsionFree_iff_algebraMap_injective.mpr fun x y hxy ↦ by
          apply IsIntegralClosure.algebraMap_injective C B F₂
          have h := congrArg (algebraMap Cₘ F₂) hxy
          simpa only [IsScalarTower.algebraMap_apply C Cₘ F₂] using h
      let qₘ : HeightOneSpectrum Cₘ := centerIntegralClosure k₁ F₁ P₂
      have hq_under : qₘ.asIdeal.under C = q.asIdeal := by
        ext c
        rw [Ideal.mem_under]
        simp only [qₘ, centerIntegralClosure_def, q, mem_center_asIdeal]
        rw [← IsScalarTower.algebraMap_apply C Cₘ F₂]
      let _ : qₘ.asIdeal.LiesOver q.asIdeal := ⟨hq_under.symm⟩
      have hq_map : q.asIdeal.map (algebraMap C Cₘ) = qₘ.asIdeal := by
        rw [← hq_under]
        exact IsLocalization.map_under
          (M := Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl) Cₘ qₘ.asIdeal
      have hdiff := map_differentIdeal_eq_differentIdeal
        (R := B) (Rₘ := Bₘ) (S := C) (Sₘ := Cₘ) (K := F₁) (L := F₂)
        (M := p.asIdeal.primeCompl)
      have hlocalD : differentIdeal Bₘ Cₘ ≠ ⊥ := differentIdeal_ne_bot
      have hmapD : (differentIdeal B C).map (algebraMap C Cₘ) ≠ ⊥ :=
        hdiff ▸ hlocalD
      have hD : differentIdeal B C ≠ ⊥ := by
        intro hD
        apply hmapD
        rw [hD, Ideal.map_bot]
      have hmapq_top : q.asIdeal.map (algebraMap C Cₘ) ≠ ⊤ := by
        rw [hq_map]
        exact qₘ.isPrime.ne_top
      have hmapq_bot : q.asIdeal.map (algebraMap C Cₘ) ≠ ⊥ :=
        hq_map ▸ qₘ.ne_bot
      have hone : Ideal.ramificationIdx' q.asIdeal qₘ.asIdeal = 1 := by
        rw [← hq_map]
        exact Ideal.ramificationIdx'_map_self_eq_one hmapq_top hmapq_bot
      have hmultiplicity : multiplicity qₘ.asIdeal
          ((differentIdeal B C).map (algebraMap C Cₘ)) =
          multiplicity q.asIdeal (differentIdeal B C) :=
        multiplicity_map_eq_of_ramificationIdx'_eq_one q qₘ (differentIdeal B C) hD hone
      calc
        multiplicity q.asIdeal (differentIdeal B C) = multiplicity qₘ.asIdeal
            ((differentIdeal B C).map (algebraMap C Cₘ)) := hmultiplicity.symm
        _ = multiplicity qₘ.asIdeal (differentIdeal Bₘ Cₘ) := by rw [hdiff]
        _ = multiplicity (centerIntegralClosure k₁ F₁ P₂).asIdeal
            (differentIdeal P₁.integers (integralClosure P₁.integers F₂)) := rfl
  calc
    differentExponent k₀ F₀ P₂ = multiplicity q.asIdeal
        (differentIdeal P₀.integers C) :=
      differentExponent_eq_multiplicity_of_restrict_eq P₂ P₀
        (restrict_restrict (k₀ := k₀) (F₀ := F₀) (k₁ := k₁) (F₁ := F₁) P₂).symm hC
    _ = ramificationIdx F₁ P₂ * multiplicity p.asIdeal
          (differentIdeal P₀.integers B) + differentExponent k₁ F₁ P₂ := hlocal
    _ = ramificationIdx F₁ P₂ * differentExponent k₀ F₀ P₁ +
          differentExponent k₁ F₁ P₂ := by
      rw [differentExponent_eq_multiplicity_of_restrict_eq P₁ P₀ rfl hB]
    _ = ramificationIdx F₁ P₂ * differentExponent k₀ F₀ (P₂.restrict k₁ F₁) +
          differentExponent k₁ F₁ P₂ := rfl

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
