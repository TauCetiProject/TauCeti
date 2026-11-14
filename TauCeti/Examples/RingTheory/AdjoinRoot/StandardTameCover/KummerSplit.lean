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
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Pi
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Normalization
import TauCeti.RingTheory.PowerSeries.Hensel
import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Examples and sharpness tests for Kummer splitting of standard tame covers

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
   exponent `e` is *not* a unit in `A`, yet `X` does not divide `e` in `A`. Thus
   `TauCeti.integralClosureAlgEquivStandardTameCover` applies at `e`, showing that the hypothesis
   `¬ f ∣ (e : A)` is strictly weaker than `IsUnit (e : A)`.
3. **Wild-ramification counterexample in characteristic `2`.** Over `A = (ZMod 2)⟦X⟧`, `X` divides
   `(2 : A) = 0`, and the wild degree-`2` root cover `A[y]/(y^2 − X)` is *not* a finite product of
   standard tame covers along `X`, demonstrating sharpness of the tameness condition.
-/

public section

open IsLocalRing PowerSeries TensorProduct

namespace TauCeti.Examples.KummerSplit

section PowerSeriesHelpers

/-- For any commutative ring `R`, taking the constant coefficient identifies `R⟦X⟧ ⧸ (X)` with
`R`. -/
private noncomputable def quotientSpanXRingEquiv (R : Type*) [CommRing R] :
    R⟦X⟧ ⧸ Ideal.span {(X : R⟦X⟧)} ≃+* R :=
  (Ideal.quotEquivOfEq (PowerSeries.ker_constantCoeff (R := R)).symm).trans
    (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)

/-- Over a regular ring `R`, the quotient `R⟦X⟧ ⧸ (X)` is regular. -/
private theorem isRegularRing_quotient_span_X (R : Type*) [CommRing R] [IsRegularRing R] :
    IsRegularRing (R⟦X⟧ ⧸ Ideal.span {(X : R⟦X⟧)}) :=
  IsRegularRing.of_ringEquiv (quotientSpanXRingEquiv R).symm

/-- Over a domain `R`, the variable `X` is a nonzerodivisor in `R⟦X⟧`. -/
private theorem X_mem_nonZeroDivisors (R : Type*) [CommRing R] [IsDomain R] :
    (X : R⟦X⟧) ∈ nonZeroDivisors R⟦X⟧ :=
  mem_nonZeroDivisors_of_ne_zero PowerSeries.X_ne_zero

/-- Over a field `k`, the residue field of `k⟦X⟧` is isomorphic to `k`. -/
private noncomputable def fieldEquivResidueFieldPowerSeries (k : Type*) [Field k] :
    k ≃+* ResidueField k⟦X⟧ :=
  RingEquiv.ofBijective ((IsLocalRing.residue k⟦X⟧).comp PowerSeries.C)
    ⟨RingHom.injective _, fun y ↦ by
      obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
      refine ⟨constantCoeff s, ?_⟩
      rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
        TauCeti.PowerSeries.maximalIdeal_eq_comap_constantCoeff, Ideal.mem_comap,
        maximalIdeal_eq_bot, Ideal.mem_bot, map_sub, constantCoeff_C, sub_self]⟩

/-- Over a separably closed field `k`, `k⟦X⟧` has separably closed residue field. -/
private theorem isSepClosed_residueField_powerSeries (k : Type*) [Field k] [IsSepClosed k] :
    IsSepClosed (ResidueField k⟦X⟧) :=
  IsSepClosed.of_ringEquiv (fieldEquivResidueFieldPowerSeries k)

end PowerSeriesHelpers

section StrictlyHenselianExample

/-- Localizing a finite product `C = ∀ i, A[x]/(x^{d i} − f)` of standard tame covers away from `f`
gives a finite étale `A_f`-algebra `S_f` pushout-equivalent to `A_f ⊗[A] C`. -/
private theorem etale_and_finite_away_of_pi {A : Type*} [CommRing A] {f : A} {ι : Type*}
    [Finite ι] {d : ι → ℕ} (hd1 : ∀ i, 1 ≤ d i) (hdu : ∀ i, IsUnit (d i : A))
    (Af Sf : Type*) [CommRing Af] [Algebra A Af] [IsLocalization.Away f Af]
    [CommRing Sf] [Algebra A Sf] [Algebra Af Sf] [IsScalarTower A Af Sf]
    [Algebra (∀ i, standardTameCover A f (d i)) Sf]
    [IsScalarTower A (∀ i, standardTameCover A f (d i)) Sf]
    [IsLocalization.Away (algebraMap A (∀ i, standardTameCover A f (d i)) f) Sf] :
    Algebra.IsPushout A Af (∀ i, standardTameCover A f (d i)) Sf ∧
      Algebra.Etale Af Sf ∧ Module.Finite Af Sf := by
  classical
  let _ := Fintype.ofFinite ι
  let C := ∀ i, standardTameCover A f (d i)
  have : IsLocalization (Algebra.algebraMapSubmonoid C (.powers f)) Sf := by
    dsimp only [Algebra.algebraMapSubmonoid]
    rw [Submonoid.map_powers]
    infer_instance
  have hpush : Algebra.IsPushout A Af C Sf :=
    (Algebra.isPushout_of_isLocalization (.powers f) Af C Sf).symm
  let eqSf : Sf ≃ₐ[Af] ∀ i, standardTameCover Af (algebraMap A Af f) (d i) :=
    (Algebra.IsPushout.equiv A Af C Sf).symm.trans <|
      (Algebra.TensorProduct.piRight A Af Af _).trans <|
        AlgEquiv.piCongrRight fun i ↦ standardTameCoverBaseChangeAlgEquiv Af f (d i)
  have (i : ι) : Algebra.Etale Af (standardTameCover Af (algebraMap A Af f) (d i)) :=
    standardTameCover_etale (IsLocalization.Away.algebraMap_isUnit f)
      (by simpa using (hdu i).map (algebraMap A Af))
  have (i : ι) : Module.Finite Af (standardTameCover Af (algebraMap A Af f) (d i)) :=
    (Polynomial.monic_X_pow_sub_C _ (Nat.ne_of_gt (hd1 i))).finite_adjoinRoot
  exact ⟨hpush, .of_equiv eqSf.symm, Module.Finite.equiv eqSf.symm.toLinearEquiv⟩

/-- Concrete multi-component cover `A[x]/(x^2 − X) × A[x]/(x^3 − X)` over the strictly henselian
local base `A = (AlgebraicClosure ℚ)⟦X⟧`, exercising both directions of
`isFiniteProductOfStandardTameCovers_iff_exists_etale_standardTameCover` together with
`IsFiniteProductOfStandardTameCovers.isIntegralClosure`. -/
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
  have : IsRegularRing (A ⧸ Ideal.span {(X : A)}) := isRegularRing_quotient_span_X k
  have : IsSepClosed (ResidueField A) := isSepClosed_residueField_powerSeries k
  have hX_max : (X : A) ∈ maximalIdeal A := TauCeti.PowerSeries.X_mem_maximalIdeal
  have hX_nzd : (X : A) ∈ nonZeroDivisors A := X_mem_nonZeroDivisors k
  have hd1 (b : Bool) : 1 ≤ d b := by dsimp only [d]; cases b <;> decide
  have hdu (b : Bool) : IsUnit (d b : A) := by
    dsimp only [d]
    cases b <;>
    · rw [PowerSeries.isUnit_iff_constantCoeff, map_natCast]
      exact Ne.isUnit (by norm_num)
  have hC : IsFiniteProductOfStandardTameCovers A C X :=
    (isFiniteProductOfStandardTameCovers_iff X).mpr
      ⟨Bool, inferInstance, d, hd1, hdu, ⟨AlgEquiv.refl⟩⟩
  let _ : Algebra Af Sf :=
    (IsLocalization.Away.lift (X : A) (by
      rw [IsScalarTower.algebraMap_apply A C Sf]
      exact IsLocalization.Away.algebraMap_isUnit (algebraMap A C X))).toAlgebra
  have : IsScalarTower A Af Sf := .of_algebraMap_eq fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_eq]
  have : IsIntegralClosure C A Sf := hC.isIntegralClosure hX_nzd Sf
  obtain ⟨_, _, _⟩ := etale_and_finite_away_of_pi (f := X) hd1 hdu Af Sf
  have hiff := isFiniteProductOfStandardTameCovers_iff_exists_etale_standardTameCover
    hX_max hX_nzd Af Sf (C := C)
  obtain ⟨e, he1, heu, T, _, _, _, _, hT⟩ := hiff.mp hC
  let A' := standardTameCover A X e
  let A'f := Localization.Away (algebraMap A A' X)
  let _ : Algebra Af A'f :=
    (IsLocalization.Away.lift (X : A) (by
      rw [IsScalarTower.algebraMap_apply A A' A'f]
      exact IsLocalization.Away.algebraMap_isUnit (algebraMap A A' X))).toAlgebra
  have : IsScalarTower A Af A'f := .of_algebraMap_eq fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_eq]
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
`O⟦X⟧`, so `integralClosureAlgEquivStandardTameCover` identifies the integral closure of `O⟦X⟧` in
the fraction field of `O⟦X⟧[y]/(y^e − X)` with `O⟦X⟧[y]/(y^e − X)`. -/
theorem test_mixedCharacteristic_not_isUnit_exponent {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {e : ℕ} (he_ne : (e : O) ≠ 0) (he_nu : ¬ IsUnit (e : O)) :
    ¬ IsUnit (e : O⟦X⟧) ∧ ¬ (X : O⟦X⟧) ∣ (e : O⟦X⟧) ∧
      Nonempty (integralClosure O⟦X⟧ (FractionRing (standardTameCover O⟦X⟧ X e)) ≃ₐ[O⟦X⟧]
        standardTameCover O⟦X⟧ X e) := by
  let A := O⟦X⟧
  have : IsRegularRing (A ⧸ Ideal.span {(X : A)}) := isRegularRing_quotient_span_X O
  have hX_max : (X : A) ∈ maximalIdeal A := TauCeti.PowerSeries.X_mem_maximalIdeal
  have hX_nzd : (X : A) ∈ nonZeroDivisors A := X_mem_nonZeroDivisors O
  have he0 : e ≠ 0 := by rintro rfl; exact he_ne Nat.cast_zero
  have he_not_unit : ¬ IsUnit (e : A) := fun hu ↦
    he_nu (by simpa [map_natCast] using hu.map (PowerSeries.constantCoeff (R := O)))
  have hX_not_dvd : ¬ (X : A) ∣ (e : A) := by
    rintro ⟨g, hg⟩
    have h0 : (e : O) = 0 := by
      simpa [map_natCast] using congrArg (PowerSeries.constantCoeff (R := O)) hg
    exact he_ne h0
  have := standardTameCover_isRegularLocalRing hX_max hX_nzd he0
  have := (Polynomial.monic_X_pow_sub_C (X : A) he0).free_adjoinRoot
  let K := FractionRing A
  let K' := FractionRing (standardTameCover A X e)
  have : FaithfulSMul A K' := FaithfulSMul.trans A (standardTameCover A X e) K'
  let _ : Algebra K K' := FractionRing.liftAlgebra A K'
  have hfin : Module.finrank K K' = e :=
    standardTameCover_finrank_fractionRing hX_max hX_nzd
  have eqv : integralClosure A K' ≃ₐ[A] standardTameCover A X (Module.finrank K K') :=
    integralClosureAlgEquivStandardTameCover hX_max hX_nzd hX_not_dvd (AlgHom.id K K')
  exact ⟨he_not_unit, hX_not_dvd,
    ⟨eqv.trans (AdjoinRoot.mapAlgEquiv AlgEquiv.refl _ _ (.of_eq (by simp [hfin])))⟩⟩

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
    exact hmem (by simpa using hu)
  exact ⟨O, inferInstance, inferInstance, inferInstance,
    test_mixedCharacteristic_not_isUnit_exponent h3_ne h3_nu⟩

end MixedCharacteristicExample

section WildCounterexample

/-- If an integral domain `C` is isomorphic to a product `∀ i : ι, B i` of nontrivial rings, the
index type `ι` is nonempty and a subsingleton. -/
private theorem nonempty_and_subsingleton_of_domain_ringEquiv_pi {C : Type*} [CommRing C]
    [IsDomain C] {ι : Type*} {B : ι → Type*} [∀ i, Ring (B i)] [∀ i, Nontrivial (B i)]
    (ψ : C ≃+* ∀ i, B i) : Nonempty ι ∧ Subsingleton ι := by
  classical
  refine ⟨by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    exact not_subsingleton C ψ.toEquiv.subsingleton, ⟨fun i j ↦ ?_⟩⟩
  by_contra hij
  let u : ∀ k, B k := Pi.single i 1
  let v : ∀ k, B k := Pi.single j 1
  have huv : u * v = 0 := funext fun k ↦ by
    dsimp only [u, v, Pi.mul_apply, Pi.zero_apply]
    by_cases hki : k = i
    · subst hki; rw [Pi.single_eq_same, Pi.single_eq_of_ne hij, mul_zero]
    · rw [Pi.single_eq_of_ne hki, zero_mul]
  have hu0 : ψ.symm u ≠ 0 := fun h0 ↦
    one_ne_zero (α := B i) (by simpa [u] using congrFun (ψ.symm.map_eq_zero_iff.mp h0) i)
  have hv0 : ψ.symm v ≠ 0 := fun h0 ↦
    one_ne_zero (α := B j) (by simpa [v] using congrFun (ψ.symm.map_eq_zero_iff.mp h0) j)
  exact mul_ne_zero hu0 hv0 (by rw [← map_mul, huv, map_zero])

/-- **Sharpness in positive characteristic:** over `A = (ZMod 2)⟦X⟧`, `(2 : A) = 0` is divisible by
`X`, and the wild degree-`2` cover `A[y]/(y^2 − X)` is *not* a finite product of standard tamely
ramified covers along `X`. -/
theorem test_wildRamification_not_isFiniteProductOfStandardTameCovers :
    ¬ IsFiniteProductOfStandardTameCovers ((ZMod 2)⟦X⟧)
        (standardTameCover ((ZMod 2)⟦X⟧) X 2) X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  let A := (ZMod 2)⟦X⟧
  let C := standardTameCover A X 2
  have : IsRegularRing (A ⧸ Ideal.span {(X : A)}) := isRegularRing_quotient_span_X (ZMod 2)
  have hX_max : (X : A) ∈ maximalIdeal A := TauCeti.PowerSeries.X_mem_maximalIdeal
  have hX_nzd : (X : A) ∈ nonZeroDivisors A := X_mem_nonZeroDivisors (ZMod 2)
  have : _root_.IsRegularLocalRing C :=
    standardTameCover_isRegularLocalRing hX_max hX_nzd (by decide)
  obtain ⟨ι, _, d, hd1, hdu, ⟨ψ⟩⟩ :=
    (isFiniteProductOfStandardTameCovers_iff (A := A) (C := C) X).mp h
  let B (i : ι) := standardTameCover A X (d i)
  have hfree (i : ι) := standardTameCover_free A X (d i) (hd1 i)
  have (i : ι) : Nontrivial (B i) := by
    by_contra hnot
    have : Subsingleton (B i) := not_nontrivial_iff_subsingleton.mp hnot
    exact Nat.not_le_of_gt (hd1 i)
      (Module.finrank_zero_of_subsingleton (R := A) (M := B i) ▸ (hfree i).2.symm.le)
  obtain ⟨⟨i₀⟩, _⟩ := nonempty_and_subsingleton_of_domain_ringEquiv_pi ψ.toRingEquiv
  have : ∀ i, Module.Free A (B i) := fun i ↦ (hfree i).1
  have : ∀ i, Module.Finite A (B i) := fun i ↦
    (Polynomial.monic_X_pow_sub_C _ (Nat.ne_of_gt (hd1 i))).finite_adjoinRoot
  let _ : Unique ι := ⟨⟨i₀⟩, fun a ↦ Subsingleton.elim a i₀⟩
  have hrank : d i₀ = 2 := by
    have hsum : Module.finrank A (∀ i, B i) = d i₀ := by
      rw [Module.finrank_pi_fintype, Fintype.sum_unique, (hfree default).2]
      exact congrArg d (Subsingleton.elim default i₀)
    rw [← hsum, ← ψ.toLinearEquiv.finrank_eq, (standardTameCover_free A X 2 (by decide)).2]
  have hu2 : IsUnit (2 : ZMod 2) := by
    have := (hdu i₀).map (PowerSeries.constantCoeff (R := ZMod 2))
    rwa [hrank, map_natCast, Nat.cast_ofNat] at this
  have h20 : (2 : ZMod 2) = 0 := by simpa using ZMod.natCast_self 2
  exact not_isUnit_zero (h20 ▸ hu2)

end WildCounterexample

end TauCeti.Examples.KummerSplit
