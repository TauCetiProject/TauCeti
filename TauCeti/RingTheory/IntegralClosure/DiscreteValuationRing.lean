/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import TauCeti.FieldTheory.FunctionField.Basic

import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.Tower
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.DiscreteValuationRing.FractionRing
import TauCeti.RingTheory.Ideal.MinimalPrime.Localization
import TauCeti.RingTheory.IntegralClosure.Pi
import TauCeti.RingTheory.IntegralClosure.QuasiFinite
import TauCeti.RingTheory.Japanese
import TauCeti.RingTheory.Kaehler.FormallyEtale
import TauCeti.RingTheory.Kaehler.SeparatingLift
import TauCeti.RingTheory.KrullDimension.DiscreteValuationRing
import TauCeti.RingTheory.Localization.Finiteness
import TauCeti.RingTheory.QuasiFinite.Quotient
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import TauCeti.RingTheory.Smooth.KrullDimension

/-!
# Finiteness of integral closures over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K`, not assumed excellent or Japanese,
let `A` be a finite-type `R`-algebra, and let `B` be a pushout of `A` along `R → K` (such as
`K ⊗[R] A` or `A[1/π]`). If `B` is locally standard smooth of relative dimension `1` over `K` — or
more generally if `B` is reduced and the residue field of every minimal prime of `B` is a
one-variable function field over `K` with one-dimensional Kähler differentials — then the integral
closure of `A` in `B` is a finite `A`-module.

The hypotheses are sharp:
* Without `Algebra.FiniteType R A`, for any discrete valuation ring `R` with uniformizer `π` and
  fraction field `K`, the subalgebra `A = R[X, X² / π², X² / π⁴, …] ⊆ K[X]` has generic fibre
  `A[1/π] = K[X]` standard smooth of relative dimension `1` over `K`, every element of `A` has
  `X`-coefficient in `R`, yet `(X / π ^ n) ^ 2 ∈ A` puts `X / π ^ n ∈ integralClosure A K[X]` for
  all `n : ℕ`, so `integralClosure A K[X]` is not finitely generated over `A`.
* Without `IsReduced B`, `A = R[X, ε] ⧸ (ε²)` is of finite type over `R` and its generic fibre
  `B = K[X, ε] ⧸ (ε²)` has unique minimal prime `(ε)` with residue field `K(X)`, yet
  `(ε / π ^ n) ^ 2 = 0` puts `ε / π ^ n ∈ integralClosure A B` for all `n : ℕ`.
* Without `Module.finrank P.ResidueField Ω[P.ResidueField⁄K] = 1` (smoothness / separable
  generation over `K`), over a non-Japanese discrete valuation ring `R` of characteristic `p > 0`
  admitting `c ∈ R` whose integral closure in `K(c ^ (1 / p))` is not finite over `R`, the algebra
  `A = R[X, Y] ⧸ (Y ^ p - c)` has regular one-dimensional generic fibre `B = K(c ^ (1 / p))[X]`,
  yet `integralClosure A B ≃ (integralClosure R K(c ^ (1 / p)))[X]` is not finite over `A`.

The proof first quotients out `R`-torsion of `A` (`RingHom.ker (algebraMap A B)`), reducing to the
torsion-free case without changing `B` or `integralClosure A B`. Then `A ⧸ 𝔪_R A` has Krull
dimension at most `1` (`TauCeti.IsDiscreteValuationRing.krullDimLE_quotient_maximalIdeal`), so
one-dimensional Noether normalization lifts to `a : A` making `A` quasi-finite over `R[X]` at every
prime above `𝔪_R` for any `x ≡ a (mod 𝔪_R A)`. Perturbing `x = a + π • b` via
`TauCeti.exists_forall_transcendental_and_isSeparable_adjoin_add_smul` makes `x` a separating
transcendence basis of every generic component field `P.ResidueField` over `K`. Since `R[X]` is an
integrally closed Noetherian domain (`IsN1`), its integral closure in each `P.ResidueField` — and
hence in `B` — is finite over `R[X]`. Zariski's main theorem transfers module finiteness to `A`
near primes over `𝔪_R`, while away from `π` the localization of `integralClosure A B` equals `B`.

## Main results

* `TauCeti.IsDiscreteValuationRing.finite_integralClosure_of_isReduced_of_isFunctionField`:
  `Module.Finite A (integralClosure A B)` when `B` is reduced and every minimal prime residue field
  of `B` is a separably generated one-variable function field over `K`.
* `finite_integralClosure_of_exists_isStandardSmoothOfRelativeDimension_one`:
  universe-polymorphic version when `B` is covered by `Localization.Away t` standard smooth of
  relative dimension `1` over `K`.
* `finite_integralClosure_of_locally_isStandardSmoothOfRelativeDimension_one`:
  specialization to `RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)` on
  `algebraMap K B`.

## References

* [Stacks Project, Lemma 55.8.3 (0C2U)](https://stacks.math.columbia.edu/tag/0C2U).
-/

public section

open Polynomial KaehlerDifferential
open scoped IntermediateField nonZeroDivisors

namespace TauCeti.IsDiscreteValuationRing

section PolynomialHelpers

attribute [local instance] Polynomial.algebra in
/-- If `K` is a fraction field of a domain `R` and `y ∈ F` is transcendental over `K`, then `K⟮y⟯`
is a fraction field of `R[X]` under `X ↦ y`. -/
private lemma isFractionRing_polynomial_adjoin {R K F : Type*} [CommRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field F] [Algebra R F] [Algebra K F]
    [IsScalarTower R K F] {y : F} (hy : Transcendental K y) :
    letI : Algebra R[X] K⟮y⟯ :=
      (Polynomial.aeval (R := R) (IntermediateField.AdjoinSimple.gen K y)).toRingHom.toAlgebra
    IsFractionRing R[X] K⟮y⟯ := by
  have : IsDomain R := (IsFractionRing.injective R K).isDomain _
  let g : K⟮y⟯ := IntermediateField.AdjoinSimple.gen K y
  have hg : Transcendental K g := by
    rwa [← transcendental_algebraMap_iff (algebraMap K⟮y⟯ F).injective,
      IntermediateField.AdjoinSimple.algebraMap_gen]
  let : Algebra K[X] K⟮y⟯ := (Polynomial.aeval (R := K) g).toRingHom.toAlgebra
  let : Algebra R[X] K⟮y⟯ := (Polynomial.aeval (R := R) g).toRingHom.toAlgebra
  have : IsScalarTower R[X] K[X] K⟮y⟯ := .of_algebraMap_eq fun p ↦ by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp [map_add, hp, hq]
    | monomial n r =>
      simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply R K K⟮y⟯]
  have : IsFractionRing K[X] K⟮y⟯ :=
    isFractionRing_polynomial_aeval hg (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top y)
  have : IsLocalization (R⁰.map Polynomial.C) K[X] := Polynomial.isLocalization R⁰ K
  have hloc : IsLocalization ((K[X])⁰.comap (algebraMap R[X] K[X])) K⟮y⟯ :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      (R⁰.map Polynomial.C) (K[X])⁰ K⟮y⟯ fun _ hu ↦ hu.mem_nonZeroDivisors
  convert hloc
  ext p
  simp [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero,
    Polynomial.map_eq_zero_iff (IsFractionRing.injective R K)]

/-- Over an integrally closed Noetherian domain `R` with fraction field `K`, if `B` is a reduced
`R`-algebra with finitely many minimal primes and `x : B` maps to a separating transcendence basis
of every minimal-prime residue field over `K`, then `integralClosure R[X] B` is finite over `R[X]`
(with `X` acting as `x`). -/
private lemma finite_integralClosure_polynomial_of_separating {R K B : Type*}
    [CommRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower R K B]
    [IsReduced B] [Finite (minimalPrimes B)] (x : B)
    (hF : ∀ P : minimalPrimes B, haveI := P.2.1.1; IsFunctionField K P.1.ResidueField)
    (hsep : ∀ P : minimalPrimes B, haveI := P.2.1.1;
      Transcendental K (algebraMap B P.1.ResidueField x) ∧
        Algebra.IsSeparable K⟮algebraMap B P.1.ResidueField x⟯ P.1.ResidueField) :
    letI : Algebra R[X] B := (Polynomial.aeval (R := R) x).toRingHom.toAlgebra
    Module.Finite R[X] (integralClosure R[X] B) := by
  have : IsDomain R := (IsFractionRing.injective R K).isDomain _
  let : Algebra R[X] B := (Polynomial.aeval (R := R) x).toRingHom.toAlgebra
  have : Ring.IsN1 R[X] := Ring.IsN1.of_isIntegrallyClosed
  let F (i : minimalPrimes B) : Type _ := letI := i.2.1.1; i.1.ResidueField
  let instField (i : minimalPrimes B) : Field (F i) := by letI := i.2.1.1; infer_instance
  let instAlgK (i : minimalPrimes B) : Algebra K (F i) := by letI := i.2.1.1; infer_instance
  let instAlgB (i : minimalPrimes B) : Algebra B (F i) := by letI := i.2.1.1; infer_instance
  let instAlgR (i : minimalPrimes B) : Algebra R (F i) := by letI := i.2.1.1; infer_instance
  have instTowerRB (i : minimalPrimes B) : IsScalarTower R B (F i) := by
    have := i.2.1.1; infer_instance
  let instAlgRX (i : minimalPrimes B) : Algebra R[X] (F i) :=
    (Polynomial.aeval (R := R) (algebraMap B (F i) x)).toRingHom.toAlgebra
  have instTowerRXB (i : minimalPrimes B) : IsScalarTower R[X] B (F i) :=
    .of_algebraMap_eq fun p ↦
      Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R B (F i)) x p
  have hfin (i : minimalPrimes B) : Module.Finite R[X] (integralClosure R[X] (F i)) := by
    have : i.1.IsPrime := i.2.1.1
    change Module.Finite R[X] (integralClosure R[X] i.1.ResidueField)
    set y := algebraMap B i.1.ResidueField x
    have : IsScalarTower R K⟮y⟯ i.1.ResidueField := .of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R K i.1.ResidueField,
        IsScalarTower.algebraMap_apply K K⟮y⟯ i.1.ResidueField,
        ← IsScalarTower.algebraMap_apply R K K⟮y⟯]
    let : Algebra R[X] K⟮y⟯ :=
      (Polynomial.aeval (R := R) (IntermediateField.AdjoinSimple.gen K y)).toRingHom.toAlgebra
    have : IsScalarTower R[X] K⟮y⟯ i.1.ResidueField := .of_algebraMap_eq fun p ↦
      Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R K⟮y⟯ i.1.ResidueField)
        (IntermediateField.AdjoinSimple.gen K y) p
    have : IsFractionRing R[X] K⟮y⟯ := isFractionRing_polynomial_adjoin (hsep i).1
    have : FiniteDimensional K⟮y⟯ i.1.ResidueField := (hF i).finiteDimensional_adjoin (hsep i).1
    have := (hsep i).2
    exact Ring.finite_integralClosure_of_isSeparable K⟮y⟯ K⟮y⟯ i.1.ResidueField
  have : Module.Finite R[X] (integralClosure R[X] (∀ i : minimalPrimes B, F i)) :=
    Module.Finite.equiv (integralClosurePiAlgEquiv R[X] F).toLinearEquiv.symm
  let ψ : B →ₐ[R[X]] ∀ i : minimalPrimes B, F i :=
    AlgHom.pi fun i ↦ IsScalarTower.toAlgHom R[X] B (F i)
  refine Module.Finite.of_injective ψ.mapIntegralClosure.toLinearMap fun u v huv ↦ Subtype.ext ?_
  rw [← sub_eq_zero, ← Ideal.mem_bot (R := B), ← Ideal.zero_eq_bot, ← nilradical_eq_zero,
    nilradical, Ideal.zero_eq_bot, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
  intro P hP
  have : P.IsPrime := hP.1.1
  have hi : algebraMap B P.ResidueField (u.1 - v.1) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrFun (congrArg Subtype.val huv) ⟨P, hP⟩
  rwa [IsScalarTower.algebraMap_apply B (B ⧸ P) P.ResidueField,
    (IsFractionRing.injective (B ⧸ P) P.ResidueField).eq_iff' (map_zero _),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hi

end PolynomialHelpers

section MinimalPrimeHelpers

/-- At a minimal prime `P` of a reduced ring `B`, the residue field `P.ResidueField` is a
localization of `B` at `P`. -/
private lemma isLocalization_atPrime_residueField_of_mem_minimalPrimes {B : Type*} [CommRing B]
    [IsReduced B] {P : Ideal B} (hP : P ∈ minimalPrimes B) :
    letI := hP.1.1
    IsLocalization.AtPrime P.ResidueField P := by
  have : P.IsPrime := hP.1.1
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime P) = ⊥ := by
    have h := IsLocalization.AtPrime.map_eq_maximalIdeal_of_mem_minimalPrimes
      (Localization.AtPrime P) (Ideal.isRadical_bot (R := B)) hP
    rwa [Ideal.map_bot, eq_comm] at h
  have hbij : Function.Bijective
      (IsScalarTower.toAlgHom B (Localization.AtPrime P) P.ResidueField) := by
    refine ⟨?_, Ideal.Quotient.mk_surjective⟩
    change Function.Injective
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime P)))
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, hmax]
  exact IsLocalization.isLocalization_of_algEquiv P.primeCompl (AlgEquiv.ofBijective _ hbij)

/-- Away from an element `r : A` such that `IsLocalization.Away r B`, the localization of
`integralClosure A B` away from `r` is generated by `1`, hence finite over `Localization.Away r`. -/
private lemma finite_localizedModule_away_integralClosure {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (r : A) [IsLocalization.Away r B] :
    Module.Finite (Localization.Away r) (LocalizedModule.Away r (integralClosure A B)) := by
  let N : Submodule A (integralClosure A B) := Submodule.span A {1}
  have hloc : Submodule.localized (.powers r) N = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
    induction x using LocalizedModule.induction_on with
    | h c t =>
      obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers r) c.1
      obtain ⟨_, k, rfl⟩ := t
      have hc : r ^ n • c ∈ N := by
        have hce : r ^ n • c = a • (1 : integralClosure A B) :=
          Subtype.ext (by simpa [Algebra.smul_def, mul_comm] using ha)
        rw [hce]
        exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton 1))
      refine ⟨_, hc, ⟨r ^ n, n, rfl⟩ * ⟨r ^ k, k, rfl⟩, ?_⟩
      rw [← IsLocalizedModule.mk_eq_mk']
      exact LocalizedModule.mk_cancel_common_left (⟨r ^ n, n, rfl⟩ : Submonoid.powers r)
        ⟨r ^ k, k, rfl⟩ c
  exact ⟨hloc ▸ Submodule.localized'_fg _ _ _ (Submodule.fg_span (Set.finite_singleton 1))⟩

/-- If every minimal-prime residue field of a finite-type `K`-algebra `B` has transcendence degree
`1` over `K`, then `B` has Krull dimension at most `1`. -/
private lemma krullDimLE_one_of_isFunctionField {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B]
    (hF : ∀ (P : Ideal B) (hP : P ∈ minimalPrimes B), haveI := hP.1.1;
      IsFunctionField K P.ResidueField) :
    Ring.KrullDimLE 1 B := by
  rw [Ring.krullDimLE_iff, ringKrullDim, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun q ↦ (PrimeSpectrum.coheight_eq_ringKrullDim_quotient q).trans_le ?_
  obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q.asIdeal)
  have : P.IsPrime := hP.1.1
  calc ringKrullDim (B ⧸ q.asIdeal)
      ≤ ringKrullDim (B ⧸ P) :=
        ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hPq)
    _ = (Algebra.trdeg K P.ResidueField).toNat :=
        ringKrullDim_eq_toNat_trdeg_of_isFractionRing K (B ⧸ P) P.ResidueField
    _ = 1 := by simp [(hF P hP).trdeg_eq_one]

/-- If `B` is a localization of `A` away from `r` and `B` is reduced, then for every minimal prime
`P` of `B` its residue field `P.ResidueField` is formally unramified over `A`. -/
private lemma formallyUnramified_residueField_of_mem_minimalPrimes {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [IsReduced B] (r : A) [IsLocalization.Away r B] {P : Ideal B}
    (hP : P ∈ minimalPrimes B) :
    letI := hP.1.1
    Algebra.FormallyUnramified A P.ResidueField := by
  have : P.IsPrime := hP.1.1
  have : IsLocalization.AtPrime P.ResidueField P :=
    isLocalization_atPrime_residueField_of_mem_minimalPrimes hP
  have : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_isLocalization (.powers r)
  have : Algebra.FormallyUnramified B P.ResidueField :=
    Algebra.FormallyUnramified.of_isLocalization P.primeCompl
  exact Algebra.FormallyUnramified.comp A B P.ResidueField

end MinimalPrimeHelpers

section TorsionFree

variable {R K A B : Type*} [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [Algebra A B] [Algebra K B]
  [IsScalarTower R A B] [IsScalarTower R K B]

include R K in
private lemma exists_separating_perturbation [IsReduced B] [Finite (minimalPrimes B)]
    {π : R} (hπ0 : π ≠ 0) [IsLocalization.Away (algebraMap R A π) B]
    (hF : ∀ (P : Ideal B) (hP : P ∈ minimalPrimes B), haveI := hP.1.1;
      IsFunctionField K P.ResidueField)
    (hΩ : ∀ (P : Ideal B) (hP : P ∈ minimalPrimes B), haveI := hP.1.1;
      Module.finrank P.ResidueField Ω[P.ResidueField⁄K] = 1)
    (a : A) :
    ∃ b : A,
      letI : Algebra R[X] B :=
        (Polynomial.aeval (R := R) (algebraMap A B (a + π • b))).toRingHom.toAlgebra
      Module.Finite R[X] (integralClosure R[X] B) := by
  let F (i : minimalPrimes B) : Type _ := letI := i.2.1.1; i.1.ResidueField
  let (i : minimalPrimes B) : Field (F i) := by letI := i.2.1.1; infer_instance
  let (i : minimalPrimes B) : Algebra K (F i) := by letI := i.2.1.1; infer_instance
  let (i : minimalPrimes B) : Algebra R (F i) := by letI := i.2.1.1; infer_instance
  let (i : minimalPrimes B) : Algebra B (F i) := by letI := i.2.1.1; infer_instance
  let (i : minimalPrimes B) : Algebra A (F i) := by letI := i.2.1.1; infer_instance
  have (i : minimalPrimes B) : IsScalarTower R K (F i) := by have := i.2.1.1; infer_instance
  have (i : minimalPrimes B) : IsScalarTower R A (F i) := by have := i.2.1.1; infer_instance
  have (i : minimalPrimes B) : IsScalarTower A B (F i) := by have := i.2.1.1; infer_instance
  have (i : minimalPrimes B) : Algebra.EssFiniteType K (F i) := by
    have := i.2.1.1; exact (hF i.1 i.2).essFiniteType
  have (i : minimalPrimes B) : Algebra.Transcendental K (F i) :=
    trdeg_ne_zero_iff.mp ((hF i.1 i.2).trdeg_eq_one ▸ one_ne_zero)
  have (i : minimalPrimes B) : Algebra.FormallyUnramified A (F i) :=
    formallyUnramified_residueField_of_mem_minimalPrimes (algebraMap R A π) i.2
  have : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr
    (IsFractionRing.injective R K)
  obtain ⟨b, hb⟩ := exists_forall_transcendental_and_isSeparable_adjoin_add_smul F
    (fun i ↦ hΩ i.1 i.2) a hπ0
  refine ⟨b, finite_integralClosure_polynomial_of_separating (K := K)
    (algebraMap A B (a + π • b)) (fun i ↦ hF i.1 i.2) fun i ↦ ?_⟩
  change Transcendental K (algebraMap B (F i) (algebraMap A B (a + π • b))) ∧
    Algebra.IsSeparable K⟮algebraMap B (F i) (algebraMap A B (a + π • b))⟯ (F i)
  rw [← IsScalarTower.algebraMap_apply A B (F i)]
  exact hb i

variable [Module.IsTorsionFree R A] [Algebra.FiniteType R A] [Algebra.IsPushout R A K B]

include R K in
private lemma finite_integralClosure_of_isTorsionFree [IsReduced B]
    (hF : ∀ (P : Ideal B) (hP : P ∈ minimalPrimes B), haveI := hP.1.1;
      IsFunctionField K P.ResidueField)
    (hΩ : ∀ (P : Ideal B) (hP : P ∈ minimalPrimes B), haveI := hP.1.1;
      Module.finrank P.ResidueField Ω[P.ResidueField⁄K] = 1) :
    Module.Finite A (integralClosure A B) := by
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away π K := hπ.isLocalizationAway_fractionRing
  have : IsLocalization.Away (algebraMap R A π) B := by
    rw [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers,
      Algebra.isLocalization_iff_isPushout (S := Submonoid.powers π) (A := K)]
    infer_instance
  have : Algebra.IsPushout R K A B := Algebra.IsPushout.symm ‹_›
  have : Algebra.FiniteType K B :=
    .of_surjective (Algebra.IsPushout.equiv R K A B).toAlgHom
      (Algebra.IsPushout.equiv R K A B).surjective
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  have : Finite (minimalPrimes B) := minimalPrimes.finite_of_isNoetherianRing B
  have : Ring.KrullDimLE 1 B := krullDimLE_one_of_isFunctionField hF
  have : Ring.KrullDimLE 1 (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    krullDimLE_quotient_maximalIdeal (K := K) (B := B) 1
  obtain ⟨a, ha⟩ := exists_forall_quasiFiniteAt_of_krullDimLE_one_quotient (A := A)
    (IsLocalRing.maximalIdeal R)
  obtain ⟨b, hfinB⟩ := exists_separating_perturbation hπ.ne_zero hF hΩ a
  set x : A := a + π • b
  let : Algebra R[X] A := (Polynomial.aeval (R := R) x).toRingHom.toAlgebra
  let : Algebra R[X] B := (Polynomial.aeval (R := R) (algebraMap A B x)).toRingHom.toAlgebra
  have : IsScalarTower R R[X] A := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, Polynomial.algebraMap_eq]
  have : IsScalarTower R[X] A B := .of_algebraMap_eq fun p ↦
    Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R A B) x p
  have : Algebra.FiniteType R[X] A := .of_restrictScalars_finiteType R R[X] A
  have : Module.Finite R[X] (integralClosure R[X] B) := hfinB
  refine .of_forall_isMaximal_exists_notMem fun q _ ↦ ?_
  by_cases hπq : algebraMap R A π ∈ q
  · have hmq : (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤ q := by
      rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      exact hπq
    have hπm : π ∈ IsLocalRing.maximalIdeal R :=
      hπ.maximalIdeal_eq ▸ Ideal.subset_span (Set.mem_singleton π)
    have hxa : x - a ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
      rw [show x - a = algebraMap R A π * b by simp [x, Algebra.smul_def]]
      exact Ideal.mul_mem_right b _ (Ideal.mem_map_of_mem _ hπm)
    have : Algebra.QuasiFiniteAt R[X] q := ha x hxa q hmq
    exact Algebra.QuasiFiniteAt.exists_notMem_finite_localizedModule_integralClosure (P := R[X]) q
  · exact ⟨algebraMap R A π, hπq, finite_localizedModule_away_integralClosure (algebraMap R A π)⟩

end TorsionFree

section General

/-- If `B` is a localization of `A` away from `r`, then `B` is also a localization of
`A ⧸ RingHom.ker (algebraMap A B)` away from the image of `r`. -/
private lemma isLocalization_away_quotient_ker {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (r : A) [IsLocalization.Away r B] :
    letI : Algebra (A ⧸ RingHom.ker (algebraMap A B)) B := (algebraMap A B).kerLift.toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (RingHom.ker (algebraMap A B)) r) B := by
  let I := RingHom.ker (algebraMap A B)
  let f' : (A ⧸ I) →+* B := (algebraMap A B).kerLift
  have hf'_inj : Function.Injective f' := RingHom.kerLift_injective (algebraMap A B)
  let _ : Algebra (A ⧸ I) B := f'.toAlgebra
  refine
    { map_units := ?_
      surj b := ?_
      exists_of_eq {_ _} hxy := ⟨1, by simp [hf'_inj hxy]⟩ }
  · rintro ⟨_, n, rfl⟩
    change IsUnit (f' (Ideal.Quotient.mk I r ^ n))
    rw [← map_pow, RingHom.kerLift_mk, map_pow]
    exact IsLocalization.Away.algebraMap_pow_isUnit (S := B) r n
  · obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers r) b
    refine ⟨⟨Ideal.Quotient.mk I a, _, n, rfl⟩, ?_⟩
    change b * f' (Ideal.Quotient.mk I r ^ n) = f' (Ideal.Quotient.mk I a)
    rw [← map_pow]
    change b * (algebraMap A B).kerLift (Ideal.Quotient.mk I (r ^ n)) =
      (algebraMap A B).kerLift (Ideal.Quotient.mk I a)
    rw [RingHom.kerLift_mk, RingHom.kerLift_mk]
    exact ha

variable {R K A B : Type*} [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  [CommRing B] [Algebra R B] [Algebra A B] [Algebra K B]
  [IsScalarTower R A B] [IsScalarTower R K B] [Algebra.IsPushout R A K B]

include R K in
/-- **Finiteness of the integral closure over a discrete valuation ring** for reduced generic
fibres with separably generated function fields. Let `R` be a discrete valuation ring with fraction
field `K`, let `A` be a finite-type `R`-algebra, and let `B` be a reduced pushout of `A` along
`R → K`. If the residue field of every minimal prime of `B` is a one-variable function field over
`K` with one-dimensional Kähler differentials, then `integralClosure A B` is a finite `A`-module. -/
@[stacks 0C2U]
theorem finite_integralClosure_of_isReduced_of_isFunctionField [IsReduced B]
    (hF : ∀ (P : Ideal B) (hP : P ∈ minimalPrimes B), haveI := hP.1.1;
      IsFunctionField K P.ResidueField)
    (hΩ : ∀ (P : Ideal B) (hP : P ∈ minimalPrimes B), haveI := hP.1.1;
      Module.finrank P.ResidueField Ω[P.ResidueField⁄K] = 1) :
    Module.Finite A (integralClosure A B) := by
  -- Quotient out `ker (A → B)` to reduce to an `R`-torsion-free base `A'` without changing `B`.
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away π K := hπ.isLocalizationAway_fractionRing
  have : IsLocalization.Away (algebraMap R A π) B := by
    rw [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers,
      Algebra.isLocalization_iff_isPushout (S := Submonoid.powers π) (A := K)]
    infer_instance
  let I := RingHom.ker (algebraMap A B)
  let A' := A ⧸ I
  let f' : A' →ₐ[R] B := Ideal.Quotient.liftₐ I (IsScalarTower.toAlgHom R A B) fun _ h ↦ h
  have hf'_inj : Function.Injective f' := RingHom.kerLift_injective (algebraMap A B)
  let : Algebra A' B := f'.toRingHom.toAlgebra
  have : IsScalarTower A A' B := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R A' B := ⟨fun r x b ↦ by
    change f' (r • x) * b = r • (f' x * b)
    rw [map_smul, smul_mul_assoc]⟩
  have : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr
    (IsFractionRing.injective R K)
  have : Module.IsTorsionFree R B := Module.IsTorsionFree.trans K
  have : Module.IsTorsionFree R A' := hf'_inj.moduleIsTorsionFree f' (map_smul f')
  have : Algebra.FiniteType R A' :=
    .of_surjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
  have : IsLocalization.Away (algebraMap R A' π) B := by
    rw [IsScalarTower.algebraMap_apply R A A']
    exact isLocalization_away_quotient_ker (algebraMap R A π)
  have : Algebra.IsPushout R A' K B := by
    rwa [← Algebra.isLocalization_iff_isPushout (S := Submonoid.powers π) (A := K),
      Algebra.algebraMapSubmonoid_powers]
  have hfinA' : Module.Finite A' (integralClosure A' B) :=
    finite_integralClosure_of_isTorsionFree (R := R) (K := K) (A := A') (B := B) hF hΩ
  have hAA' : (algebraMap A A').Finite :=
    RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have : Algebra.IsIntegral A A' :=
    have : Module.Finite A A' := hAA'
    Algebra.IsIntegral.of_finite A A'
  let g : integralClosure A' B →+* integralClosure A B :=
    { toFun x := ⟨x.1, isIntegral_trans _ x.2⟩
      map_one' := rfl, map_mul' _ _ := rfl, map_zero' := rfl, map_add' _ _ := rfl }
  have hg : g.Finite := RingHom.Finite.of_surjective g fun y ↦ ⟨⟨y.1, y.2.tower_top⟩, rfl⟩
  have hcomp : g.comp ((algebraMap A' (integralClosure A' B)).comp (algebraMap A A')) =
      algebraMap A (integralClosure A B) := by ext; rfl
  exact RingHom.finite_algebraMap.mp
    (hcomp ▸ hg.comp ((RingHom.finite_algebraMap.mpr hfinA').comp hAA'))

/-- If `B → F` factors through both `B ⧸ P` and a `B`-algebra `S`, then `P.map (algebraMap B S)`
maps to zero in `F`. -/
private lemma map_eq_zero_of_isFractionRing_quotient {B S F : Type*} [CommRing B]
    {P : Ideal B} [CommRing S] [Algebra B S] [CommRing F] [Algebra B F]
    [Algebra (B ⧸ P) F] [IsScalarTower B (B ⧸ P) F] [Algebra S F] [IsScalarTower B S F] :
    ∀ a ∈ P.map (algebraMap B S), algebraMap S F a = 0 := by
  change P.map (algebraMap B S) ≤ RingHom.ker (algebraMap S F)
  rw [Ideal.map_le_iff_le_comap]
  intro y hy
  rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply B S F,
    IsScalarTower.algebraMap_apply B (B ⧸ P) F, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr hy, map_zero]

/-- If `P` is a prime of `B` not containing `t`, `S` is a localization of `B` away from `t`, and
`F` is a fraction ring of `B ⧸ P` with a compatible `S`-algebra structure, then `F` is a fraction
ring of `S ⧸ P.map (algebraMap B S)`. -/
private lemma isFractionRing_quotient_map_away {B S F : Type*} [CommRing B] {P : Ideal B}
    [P.IsPrime] {t : B} (ht : t ∉ P) [CommRing S] [Algebra B S] [IsLocalization.Away t S]
    [Field F] [Algebra B F] [Algebra (B ⧸ P) F]
    [IsScalarTower B (B ⧸ P) F] [IsFractionRing (B ⧸ P) F] [Algebra S F] [IsScalarTower B S F] :
    letI : Algebra (S ⧸ P.map (algebraMap B S)) F :=
      (Ideal.Quotient.lift (P.map (algebraMap B S)) (algebraMap S F)
        map_eq_zero_of_isFractionRing_quotient).toAlgebra
    IsFractionRing (S ⧸ P.map (algebraMap B S)) F := by
  let g : (S ⧸ P.map (algebraMap B S)) →+* F :=
    Ideal.Quotient.lift (P.map (algebraMap B S)) (algebraMap S F)
      map_eq_zero_of_isFractionRing_quotient
  let _ : Algebra (S ⧸ P.map (algebraMap B S)) F := g.toAlgebra
  have hg_inj : Function.Injective g := (injective_iff_map_eq_zero g).mpr fun x hx ↦ by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨⟨b, _, n, rfl⟩, hb⟩ := IsLocalization.surj (.powers t) s
    have hb0 : algebraMap B F b = 0 := by
      rw [IsScalarTower.algebraMap_apply B S F, ← hb, map_mul,
        show algebraMap S F s = 0 from hx, zero_mul]
    rw [IsScalarTower.algebraMap_apply B (B ⧸ P) F, Ideal.Quotient.algebraMap_eq,
      (IsFractionRing.injective (B ⧸ P) F).eq_iff' (map_zero _),
      Ideal.Quotient.eq_zero_iff_mem] at hb0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hmem : algebraMap B S t ^ n * s ∈ P.map (algebraMap B S) := by
      rw [mul_comm, ← map_pow, show s * algebraMap B S (t ^ n) = algebraMap B S b from hb]
      exact Ideal.mem_map_of_mem _ hb0
    exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.Away.algebraMap_pow_isUnit t n)).mp hmem
  have hdisj : Disjoint (Submonoid.powers t : Set B) P :=
    (Ideal.disjoint_powers_iff_notMem t ‹P.IsPrime›.isRadical).mpr ht
  have : (P.map (algebraMap B S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers t) S P ‹P.IsPrime› hdisj
  refine
    { map_units y := IsUnit.mk0 _ (map_ne_zero_of_mem_nonZeroDivisors g hg_inj y.2)
      surj z := ?_
      exists_of_eq {_ _} h := ⟨1, by simpa using hg_inj h⟩ }
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (B ⧸ P)⁰ z
  obtain ⟨bx, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨by_, hby_⟩ := Ideal.Quotient.mk_surjective y.1
  have hby : Ideal.Quotient.mk (P.map (algebraMap B S)) (algebraMap B S by_) ∈
      (S ⧸ P.map (algebraMap B S))⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    intro hmem
    apply mem_nonZeroDivisors_iff_ne_zero.mp y.2
    rw [← hby_, Ideal.Quotient.eq_zero_iff_mem,
      ← IsLocalization.under_map_of_isPrime_disjoint (.powers t) S ‹P.IsPrime› hdisj]
    exact hmem
  have hlift (c : B) : g (Ideal.Quotient.mk _ (algebraMap B S c)) =
      algebraMap (B ⧸ P) F (Ideal.Quotient.mk P c) := by
    dsimp only [g]
    rw [Ideal.Quotient.lift_mk, ← IsScalarTower.algebraMap_apply B S F,
      IsScalarTower.algebraMap_apply B (B ⧸ P) F, Ideal.Quotient.algebraMap_eq]
  refine ⟨⟨Ideal.Quotient.mk _ (algebraMap B S bx), _, hby⟩, ?_⟩
  change z * g (Ideal.Quotient.mk _ (algebraMap B S by_)) =
    g (Ideal.Quotient.mk _ (algebraMap B S bx))
  rw [hlift, hlift, hby_]
  exact hxy

/-- On a minimal prime `P` missing `t : B`, standard smoothness of relative dimension `1` of
`Localization.Away t` over `K` implies that `P.ResidueField` has one-dimensional Kähler
differentials over `K`. -/
private lemma finrank_kaehler_of_isStandardSmoothOfRelativeDimension_one [IsReduced B]
    {P : Ideal B} (hP : P ∈ minimalPrimes B) {t : B} (ht : t ∉ P)
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K (Localization.Away t)] :
    letI := hP.1.1
    Module.finrank P.ResidueField Ω[P.ResidueField⁄K] = 1 := by
  have : P.IsPrime := hP.1.1
  let S := Localization.Away t
  have : IsLocalization.AtPrime P.ResidueField P :=
    isLocalization_atPrime_residueField_of_mem_minimalPrimes hP
  have hsub : Submonoid.powers t ≤ P.primeCompl :=
    (Submonoid.powers_le (P := P.primeCompl)).mpr ht
  let : Algebra S P.ResidueField :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S P.ResidueField (.powers t) P.primeCompl hsub
  have : IsScalarTower B S P.ResidueField :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S P.ResidueField (.powers t)
      P.primeCompl hsub
  have : IsScalarTower K S P.ResidueField := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply K B P.ResidueField,
      IsScalarTower.algebraMap_apply B S P.ResidueField,
      ← IsScalarTower.algebraMap_apply K B S]
  have : IsLocalization (P.primeCompl.map (algebraMap B S)) P.ResidueField :=
    IsLocalization.isLocalization_of_submonoid_le S P.ResidueField (.powers t) P.primeCompl hsub
  have : Algebra.FormallyEtale S P.ResidueField :=
    Algebra.FormallyEtale.of_isLocalization (P.primeCompl.map (algebraMap B S))
  have : Nontrivial S := (algebraMap S P.ResidueField).domain_nontrivial
  have : Algebra.IsStandardSmooth K S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let b := Module.Free.chooseBasis S Ω[S⁄K]
  have hcard : Cardinal.mk (Module.Free.ChooseBasisIndex S Ω[S⁄K]) = 1 :=
    b.mk_eq_rank''.trans (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1)
  have : Finite (Module.Free.ChooseBasisIndex S Ω[S⁄K]) :=
    Cardinal.lt_aleph0_iff_finite.mp (hcard ▸ Cardinal.one_lt_aleph0)
  let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex S Ω[S⁄K])
  rw [Module.finrank_eq_card_basis (kaehlerBasisOfFormallyEtale K S P.ResidueField b)]
  exact_mod_cast (Cardinal.mk_fintype _).symm.trans hcard

/-- If `D` is a finite-type `K`-domain of Krull dimension `1` and `F` is a fraction field of `D`,
then `trdeg K F = 1`. -/
private lemma trdeg_eq_one_of_isFractionRing {K : Type*} {D F : Type*} [Field K] [CommRing D]
    [Algebra K D] [Algebra.FiniteType K D] [Field F] [Algebra K F] [Algebra D F]
    [IsScalarTower K D F] [IsFractionRing D F] (hdim : ringKrullDim D = 1) :
    Algebra.trdeg K F = 1 := by
  have : IsDomain D := (IsFractionRing.injective D F).isDomain _
  have htrNat : (Algebra.trdeg K F).toNat = 1 := by
    have h := ringKrullDim_eq_toNat_trdeg_of_isFractionRing K D F
    rw [hdim] at h
    exact mod_cast h.symm
  have : FaithfulSMul D F :=
    (faithfulSMul_iff_algebraMap_injective D F).mpr (IsFractionRing.injective D F)
  have ht := lift_trdeg_add_eq K D F
  rw [trdeg_eq_zero_iff.mpr (IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic F F)), Cardinal.lift_zero, add_zero] at ht
  have hlt : Algebra.trdeg K F < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.mp
      (ht ▸ Cardinal.lift_lt_aleph0.mpr (trdeg_lt_aleph0_of_finiteType (R := K) (S := D)))
  rw [← Cardinal.cast_toNat_of_lt_aleph0 hlt, htrNat, Nat.cast_one]

/-- On a minimal prime `P` missing `t : B`, standard smoothness of relative dimension `1` of
`Localization.Away t` over `K` implies that `P.ResidueField` is a one-variable function field over
`K` with one-dimensional Kähler differentials. -/
private lemma isFunctionField_and_finrank_kaehler_of_isStandardSmoothOfRelativeDimension_one
    [IsReduced B] {P : Ideal B} (hP : P ∈ minimalPrimes B) {t : B} (ht : t ∉ P)
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K (Localization.Away t)] :
    letI := hP.1.1
    IsFunctionField K P.ResidueField ∧ Module.finrank P.ResidueField Ω[P.ResidueField⁄K] = 1 := by
  have : P.IsPrime := hP.1.1
  let S := Localization.Away t
  have : IsLocalization.AtPrime P.ResidueField P :=
    isLocalization_atPrime_residueField_of_mem_minimalPrimes hP
  have hsub : Submonoid.powers t ≤ P.primeCompl :=
    (Submonoid.powers_le (P := P.primeCompl)).mpr ht
  let : Algebra S P.ResidueField :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S P.ResidueField (.powers t) P.primeCompl hsub
  have : IsScalarTower B S P.ResidueField :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S P.ResidueField (.powers t)
      P.primeCompl hsub
  have : IsScalarTower K S P.ResidueField := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply K B P.ResidueField,
      IsScalarTower.algebraMap_apply B S P.ResidueField,
      ← IsScalarTower.algebraMap_apply K B S]
  have : IsLocalization (P.primeCompl.map (algebraMap B S)) P.ResidueField :=
    IsLocalization.isLocalization_of_submonoid_le S P.ResidueField (.powers t) P.primeCompl hsub
  have : Algebra.IsStandardSmooth K S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have : Algebra.EssFiniteType S P.ResidueField :=
    Algebra.EssFiniteType.of_isLocalization P.ResidueField (P.primeCompl.map (algebraMap B S))
  have : Algebra.EssFiniteType K P.ResidueField := Algebra.EssFiniteType.comp K S P.ResidueField
  have hdisj : Disjoint (Submonoid.powers t : Set B) P :=
    (Ideal.disjoint_powers_iff_notMem t ‹P.IsPrime›.isRadical).mpr ht
  have hPS_min : P.map (algebraMap B S) ∈ minimalPrimes S := by
    change P.map (algebraMap B S) ∈ (⊥ : Ideal S).minimalPrimes
    rw [← Ideal.map_bot (f := algebraMap B S),
      IsLocalization.minimalPrimes_map (.powers t) S ⊥, Set.mem_preimage]
    rwa [IsLocalization.under_map_of_isPrime_disjoint (.powers t) S ‹P.IsPrime› hdisj]
  have hdimS : ringKrullDim (S ⧸ P.map (algebraMap B S)) = 1 :=
    ringKrullDim_quotient_of_isStandardSmoothOfRelativeDimension K 1 hPS_min
  have : (P.map (algebraMap B S)).IsPrime := hPS_min.1.1
  let g : (S ⧸ P.map (algebraMap B S)) →ₐ[K] P.ResidueField :=
    Ideal.Quotient.liftₐ (P.map (algebraMap B S)) (IsScalarTower.toAlgHom K S P.ResidueField)
      map_eq_zero_of_isFractionRing_quotient
  let _ : Algebra (S ⧸ P.map (algebraMap B S)) P.ResidueField := g.toRingHom.toAlgebra
  have : IsScalarTower K (S ⧸ P.map (algebraMap B S)) P.ResidueField := ⟨fun c x z ↦ by
    change g (c • x) * z = c • (g x * z)
    rw [map_smul, smul_mul_assoc]⟩
  have : IsFractionRing (S ⧸ P.map (algebraMap B S)) P.ResidueField :=
    isFractionRing_quotient_map_away ht (S := S) (F := P.ResidueField)
  have htr : Algebra.trdeg K P.ResidueField = 1 :=
    trdeg_eq_one_of_isFractionRing (D := S ⧸ P.map (algebraMap B S)) hdimS
  exact ⟨(isFunctionField_iff_trdeg_eq_one (k := K) (F := P.ResidueField)).mpr htr,
    finrank_kaehler_of_isStandardSmoothOfRelativeDimension_one hP ht⟩

include R K in
/-- **Finiteness of the integral closure over a discrete valuation ring** when the generic fibre is
covered by standard-smooth localizations of relative dimension `1`. No excellence or Japanese
hypothesis on `R` and no torsion-freeness hypothesis on `A` are needed. -/
@[stacks 0C2U]
theorem finite_integralClosure_of_exists_isStandardSmoothOfRelativeDimension_one
    (hs : ∃ s : Set B, Ideal.span s = ⊤ ∧
      ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension 1 K (Localization.Away t)) :
    Module.Finite A (integralClosure A B) := by
  obtain ⟨s, hspan, hsmooth⟩ := hs
  have : IsReduced B := by
    refine ⟨fun x hx ↦ Module.eq_zero_of_isLocalized_span s hspan
      (fun r : s ↦ Localization.Away r.1)
      (fun r : s ↦ Algebra.linearMap B (Localization.Away r.1)) x fun r ↦ ?_⟩
    have := (hsmooth r.1 r.2).isStandardSmooth
    have := isReduced_of_smooth K (Localization.Away r.1)
    exact (hx.map (algebraMap B (Localization.Away r.1))).eq_zero
  have hboth : ∀ (P : Ideal B) (hP : P ∈ minimalPrimes B), haveI := hP.1.1;
      IsFunctionField K P.ResidueField ∧ Module.finrank P.ResidueField Ω[P.ResidueField⁄K] = 1 := by
    intro P hP
    have : P.IsPrime := hP.1.1
    have hnot : ¬ s ⊆ P := fun hsub ↦
      ‹P.IsPrime›.ne_top (top_unique (hspan ▸ Ideal.span_le.mpr hsub))
    obtain ⟨t, hts, htP⟩ := Set.not_subset.mp hnot
    have := hsmooth t hts
    exact isFunctionField_and_finrank_kaehler_of_isStandardSmoothOfRelativeDimension_one hP htP
  exact finite_integralClosure_of_isReduced_of_isFunctionField (R := R) (K := K)
    (fun P hP ↦ (hboth P hP).1) (fun P hP ↦ (hboth P hP).2)

end General

/-- Specialization of `finite_integralClosure_of_exists_isStandardSmoothOfRelativeDimension_one` to
`RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap K B)` when `K` and `B`
live in the same universe. -/
@[stacks 0C2U]
theorem finite_integralClosure_of_locally_isStandardSmoothOfRelativeDimension_one
    {R A : Type*} {K B : Type u} [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [CommRing B] [Algebra R B] [Algebra A B] [Algebra K B]
    [IsScalarTower R A B] [IsScalarTower R K B] [Algebra.IsPushout R A K B]
    (hB : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap K B)) :
    Module.Finite A (integralClosure A B) := by
  obtain ⟨s, hspan, hs⟩ := hB
  refine finite_integralClosure_of_exists_isStandardSmoothOfRelativeDimension_one (R := R) (K := K)
    ⟨(s : Set B), hspan, fun t ht ↦ ?_⟩
  have ht' := hs t ht
  rwa [← IsScalarTower.algebraMap_eq K B (Localization.Away t),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at ht'

end TauCeti.IsDiscreteValuationRing
