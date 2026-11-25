/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.KummerSplit
public import TauCeti.RingTheory.RegularLocalRing.PowerSeries

import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Normalization
import TauCeti.RingTheory.PowerSeries.Hensel
import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Examples for Kummer splitting of standard tame covers

This file exercises the main results of
`TauCeti.RingTheory.AdjoinRoot.StandardTameCover.KummerSplit` across three concrete settings:

1. **Strictly henselian base with multi-component ramification.** Over `A = (AlgebraicClosure ℚ)⟦X⟧`
   with regular divisor `f = X`, the two-component product cover
   `C = A[x]/(x^2 − X) × A[x]/(x^3 − X)` (distinct ramification indices `2` and `3`) is its own
   normalization away from `X`, and both directions of
   `TauCeti.isFiniteProductOfStandardTameCovers_iff_exists_etale_standardTameCover` apply with no
   unverified hypotheses.
2. **Mixed-characteristic dimension-two base where `¬ f ∣ (e : A)` holds without `IsUnit (e : A)`.**
   Over the two-dimensional regular local ring `A = O⟦X⟧` over a discrete valuation ring `O` in
   which `e` is nonzero and non-invertible (instantiated concretely at `O = ℤ_(3)`, `e = 3`), the
   exponent `e` is *not* a unit in `A`, yet `X` does not divide `e` in `A`. Thus the integral
   closure of `O⟦X⟧` in the fraction field of `O⟦X⟧[y]/(y^e − X)` is `O⟦X⟧`-isomorphic to
   `O⟦X⟧[y]/(y^e − X)`, showing that the hypothesis `¬ f ∣ (e : A)` is strictly weaker than
   `IsUnit (e : A)`.
3. **Failure of the unit-exponent condition in characteristic `2`.** Over `A = (ZMod 2)⟦X⟧`, the
   exponent `2` is zero (hence not a unit in `A`), so the degree-`2` root cover `A[y]/(y^2 − X)`
   fails the unit-exponent condition of `IsFiniteProductOfStandardTameCovers` along `X`.
-/

public section

open IsLocalRing PowerSeries TensorProduct

namespace TauCeti.Examples.KummerSplit

section StrictlyHenselianExample

/-- Over the strictly henselian regular local base `A = (AlgebraicClosure ℚ)⟦X⟧`, for the
two-component product cover `C = A[x]/(x^2 − X) × A[x]/(x^3 − X)` along `X`, there exist an
exponent `e ≥ 1` invertible in `A` and a finite étale `(A[x]/(x^e − X))`-algebra `T` whose base
change away from `X` is isomorphic to that of `C`, and `C` satisfies
`IsFiniteProductOfStandardTameCovers A C X`. -/
theorem test_strictlyHenselian_multiComponent :
    let A := (AlgebraicClosure ℚ)⟦X⟧
    let d : Bool → ℕ := fun b ↦ cond b 2 3
    let C := ∀ b : Bool, standardTameCover A X (d b)
    ∃ (e : ℕ) (_ : 1 ≤ e) (_ : IsUnit (e : A)) (T : Type) (_ : CommRing T)
      (_ : Algebra (standardTameCover A X e) T) (_ : Algebra.Etale (standardTameCover A X e) T)
      (_ : Module.Finite (standardTameCover A X e) T),
      Nonempty
        (Localization.Away (algebraMap A (standardTameCover A X e) X) ⊗[standardTameCover A X e] T
          ≃ₐ[Localization.Away (algebraMap A (standardTameCover A X e) X)]
          Localization.Away (algebraMap A (standardTameCover A X e) X) ⊗[A] C) ∧
      IsFiniteProductOfStandardTameCovers A C X := by
  intro A d C
  let k := AlgebraicClosure ℚ
  let Af := Localization.Away (X : A)
  let Sf := Localization.Away (algebraMap A C X)
  have : IsSepClosed (ResidueField A) :=
    IsSepClosed.of_ringEquiv (PowerSeries.residueFieldOfPowerSeries (k := k)).symm
  have hX_max : (X : A) ∈ maximalIdeal A := TauCeti.PowerSeries.X_mem_maximalIdeal
  have hX_nzd : (X : A) ∈ nonZeroDivisors A := MvPowerSeries.X_mem_nonZeroDivisors
  have hd1 (b : Bool) : 1 ≤ d b := by dsimp only [d]; cases b <;> decide
  have hdu (b : Bool) : IsUnit (d b : A) := by
    dsimp only [d]
    cases b <;>
    · rw [PowerSeries.isUnit_iff_constantCoeff, map_natCast]
      exact Ne.isUnit (by norm_num)
  have hC : IsFiniteProductOfStandardTameCovers A C X :=
    (isFiniteProductOfStandardTameCovers_iff X).mpr
      ⟨Bool, inferInstance, d, hd1, hdu, ⟨AlgEquiv.refl⟩⟩
  let fSf := Localization.awayMapₐ (Algebra.ofId A C) X
  let _ : Algebra Af Sf := fSf.toRingHom.toAlgebra
  have : IsScalarTower A Af Sf := .of_algHom fSf
  have : IsIntegralClosure C A Sf := hC.isIntegralClosure hX_nzd Sf
  have : Algebra.Etale Af Sf := hC.etale_away Af Sf
  have : Module.Finite Af Sf := (hC.away Af Sf).finite
  have hpass : Algebra.IsPushout A Af C Sf :=
    (Algebra.isPushout_of_isLocalization (.powers (X : A)) Af C Sf).symm
  have hiff := isFiniteProductOfStandardTameCovers_iff_exists_etale_standardTameCover
    hX_max hX_nzd Af Sf (C := C)
  obtain ⟨e, he1, heu, T, _, _, _, _, hT⟩ := hiff.mp hC
  let A' := standardTameCover A X e
  let A'f := Localization.Away (algebraMap A A' X)
  let fA'f := Localization.awayMapₐ (Algebra.ofId A A') X
  let _ : Algebra Af A'f := fA'f.toRingHom.toAlgebra
  have : IsScalarTower A Af A'f := .of_algHom fA'f
  obtain ⟨φ⟩ := hT A'f
  have φC : A'f ⊗[A'] T ≃ₐ[A'f] A'f ⊗[A] C :=
    φ.trans <|
      (Algebra.TensorProduct.congr AlgEquiv.refl
        (Algebra.IsPushout.equiv A Af C Sf).symm).trans <|
        Algebra.TensorProduct.cancelBaseChange A Af A'f A'f C
  exact ⟨e, he1, heu, T, inferInstance, inferInstance, inferInstance, inferInstance, ⟨φC⟩,
    hiff.mpr ⟨e, he1, heu, T, inferInstance, inferInstance, inferInstance, inferInstance, hT⟩⟩

end StrictlyHenselianExample

section MixedCharacteristicExample

/-- Over the two-dimensional regular local ring `O⟦X⟧` over a discrete valuation ring `O` in which
`e` is nonzero and non-invertible, `(e : O⟦X⟧)` is *not* a unit, yet `X` does not divide `e` in
`O⟦X⟧`, and the integral closure of `O⟦X⟧` in the fraction field of `O⟦X⟧[y]/(y^e − X)` is
`O⟦X⟧`-isomorphic to `O⟦X⟧[y]/(y^e − X)`. -/
theorem test_mixedCharacteristic_not_isUnit_exponent {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {e : ℕ} (he_ne : (e : O) ≠ 0) (he_nu : ¬ IsUnit (e : O)) :
    ¬ IsUnit (e : O⟦X⟧) ∧ ¬ (X : O⟦X⟧) ∣ (e : O⟦X⟧) ∧
      Nonempty (integralClosure O⟦X⟧ (FractionRing (standardTameCover O⟦X⟧ X e)) ≃ₐ[O⟦X⟧]
        standardTameCover O⟦X⟧ X e) := by
  let A := O⟦X⟧
  have hX_max : (X : A) ∈ maximalIdeal A := TauCeti.PowerSeries.X_mem_maximalIdeal
  have hX_nzd : (X : A) ∈ nonZeroDivisors A := MvPowerSeries.X_mem_nonZeroDivisors
  have he0 : e ≠ 0 := by rintro rfl; exact he_ne Nat.cast_zero
  have he_not_unit : ¬ IsUnit (e : A) := fun hu ↦
    he_nu (by simpa [map_natCast] using hu.map (PowerSeries.constantCoeff (R := O)))
  have hX_not_dvd : ¬ (X : A) ∣ (e : A) := by
    rintro ⟨g, hg⟩
    have h0 : (e : O) = 0 := by
      simpa [map_natCast] using congrArg (PowerSeries.constantCoeff (R := O)) hg
    exact he_ne h0
  have := standardTameCover_isRegularLocalRing hX_max hX_nzd he0
  have : Module.Free A (standardTameCover A X e) :=
    (standardTameCover_free A X e (Nat.one_le_iff_ne_zero.mpr he0)).1
  let K := FractionRing A
  let K' := FractionRing (standardTameCover A X e)
  have : FaithfulSMul A K' := FaithfulSMul.trans A (standardTameCover A X e) K'
  let _ : Algebra K K' := FractionRing.liftAlgebra A K'
  have hfin : Module.finrank K K' = e :=
    standardTameCover_finrank_fractionRing (X : A) (Nat.one_le_iff_ne_zero.mpr he0) K K'
  have eqv : integralClosure A K' ≃ₐ[A] standardTameCover A X (Module.finrank K K') :=
    integralClosureAlgEquivStandardTameCover hX_nzd hX_not_dvd (AlgHom.id K K')
  exact ⟨he_not_unit, hX_not_dvd, ⟨eqv.trans (AdjoinRoot.algEquivOfEq A _ _ (by rw [hfin]))⟩⟩

-- Non-vacuity check instantiating `O = ℤ_(3)` and `e = 3`.
example :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O),
      ¬ IsUnit ((3 : ℕ) : O⟦X⟧) ∧ ¬ (X : O⟦X⟧) ∣ ((3 : ℕ) : O⟦X⟧) ∧
        Nonempty (integralClosure O⟦X⟧ (FractionRing (standardTameCover O⟦X⟧ X 3)) ≃ₐ[O⟦X⟧]
          standardTameCover O⟦X⟧ X 3) := by
  let p : Ideal ℤ := Ideal.span {(3 : ℤ)}
  have hp : p.IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr (Nat.prime_iff_prime_int.mp Nat.prime_three)
  have hp_ne : p ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num
  let O := Localization.AtPrime p
  have : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hp_ne O
  have h3_ne : ((3 : ℕ) : O) ≠ 0 := by
    intro h0
    have hinj := IsLocalization.injective O p.primeCompl_le_nonZeroDivisors
    exact (by norm_num : (3 : ℤ) ≠ 0) (hinj (by simpa using h0))
  have h3_nu : ¬ IsUnit ((3 : ℕ) : O) := by
    intro hu
    have hmem : (algebraMap ℤ O 3) ∈ maximalIdeal O :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff O p 3).mpr (Ideal.mem_span_singleton_self 3)
    exact notMem_maximalIdeal.mpr (by simpa using hu) hmem
  exact ⟨O, inferInstance, inferInstance, inferInstance,
    test_mixedCharacteristic_not_isUnit_exponent h3_ne h3_nu⟩

end MixedCharacteristicExample

section NonUnitExponentCounterexample

/-- Over `A = (ZMod 2)⟦X⟧`, the exponent `2` is zero (hence not a unit in `A`), so the degree-`2`
root cover `A[y]/(y^2 − X)` fails the unit-exponent condition of
`IsFiniteProductOfStandardTameCovers` along `X`. -/
theorem test_charTwo_not_isFiniteProductOfStandardTameCovers :
    ¬ IsFiniteProductOfStandardTameCovers ((ZMod 2)⟦X⟧)
        (standardTameCover ((ZMod 2)⟦X⟧) X 2) X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  let A := (ZMod 2)⟦X⟧
  let C := standardTameCover A X 2
  let Af := Localization.Away (X : A)
  let Cf := Localization.Away (algebraMap A C X)
  let fCf := Localization.awayMapₐ (Algebra.ofId A C) X
  let _ : Algebra Af Cf := fCf.toRingHom.toAlgebra
  have : IsScalarTower A Af Cf := .of_algHom fCf
  have : Algebra.Etale Af Cf := h.etale_away Af Cf
  have hu2 : IsUnit ((2 : ℕ) : Af) :=
    (standardTameCover_etale_away_iff (X : A) Af Cf (e := 2) (by decide)).mp this
  have hX_nzd : (X : A) ∈ nonZeroDivisors A := MvPowerSeries.X_mem_nonZeroDivisors
  have : Nontrivial Af :=
    (IsLocalization.injective Af (Submonoid.powers_le.mpr hX_nzd)).nontrivial
  have h20 : ((2 : ℕ) : Af) = 0 := by
    rw [← map_natCast (algebraMap (ZMod 2) Af), ZMod.natCast_self 2, map_zero]
  exact not_isUnit_zero (h20 ▸ hu2)

end NonUnitExponentCounterexample

end TauCeti.Examples.KummerSplit
