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

import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.DiscreteValuationRing.FractionRing
import TauCeti.RingTheory.Ideal.MinimalPrime.Localization
import TauCeti.RingTheory.IntegralClosure.MvPolynomial
import TauCeti.RingTheory.IntegralClosure.Pi
import TauCeti.RingTheory.IntegralClosure.QuasiFinite
import TauCeti.RingTheory.Kaehler.FormallyEtale
import TauCeti.RingTheory.Kaehler.SeparatingLift
import TauCeti.RingTheory.KrullDimension.DiscreteValuationRing
import TauCeti.RingTheory.KrullDimension.FiniteType
import TauCeti.RingTheory.Localization.Away.Quotient
import TauCeti.RingTheory.Localization.Finiteness
import TauCeti.RingTheory.Localization.Integral
import TauCeti.RingTheory.Localization.TensorProduct
import TauCeti.RingTheory.QuasiFinite.Parameter
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
  let F (i : minimalPrimes B) : Type _ := letI := i.property.1.1; i.val.ResidueField
  let (i : minimalPrimes B) : Field (F i) := by letI := i.property.1.1; infer_instance
  let (i : minimalPrimes B) : Algebra K (F i) := by letI := i.property.1.1; infer_instance
  let (i : minimalPrimes B) : Algebra R (F i) := by letI := i.property.1.1; infer_instance
  let (i : minimalPrimes B) : Algebra B (F i) := by letI := i.property.1.1; infer_instance
  let (i : minimalPrimes B) : Algebra A (F i) := by letI := i.property.1.1; infer_instance
  have (i : minimalPrimes B) : IsScalarTower R K (F i) := by have := i.property.1.1; infer_instance
  have (i : minimalPrimes B) : IsScalarTower R A (F i) := by have := i.property.1.1; infer_instance
  have (i : minimalPrimes B) : IsScalarTower A B (F i) := by have := i.property.1.1; infer_instance
  have (i : minimalPrimes B) : Algebra.EssFiniteType K (F i) := by
    have := i.property.1.1; exact (hF i.val i.property).essFiniteType
  have (i : minimalPrimes B) : Algebra.Transcendental K (F i) :=
    trdeg_ne_zero_iff.mp ((hF i.val i.property).trdeg_eq_one ▸ one_ne_zero)
  have (i : minimalPrimes B) : Algebra.FormallyUnramified A (F i) := by
    have : i.val.IsPrime := i.property.1.1
    have : IsLocalization.AtPrime (F i) i.val :=
      isLocalization_atPrime_residueField_of_mem_minimalPrimes i.property
    have : Algebra.FormallyUnramified A B :=
      Algebra.FormallyUnramified.of_isLocalization (.powers (algebraMap R A π))
    have : Algebra.FormallyUnramified B (F i) :=
      Algebra.FormallyUnramified.of_isLocalization i.val.primeCompl
    exact Algebra.FormallyUnramified.comp A B (F i)
  have : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr
    (IsFractionRing.injective R K)
  obtain ⟨b, hb⟩ := exists_forall_transcendental_and_isSeparable_adjoin_add_smul F
    (fun i ↦ hΩ i.val i.property) a hπ0
  refine ⟨b, ?_⟩
  let : Algebra R[X] B :=
    (Polynomial.aeval (R := R) (algebraMap A B (a + π • b))).toRingHom.toAlgebra
  have : Ring.IsN1 R[X] := Ring.IsN1.of_isIntegrallyClosed
  refine finite_integralClosure_of_isReduced_of_forall_minimalPrimes fun Q hQ ↦ ?_
  have : Q.IsPrime := hQ.1.1
  have : IsScalarTower R R[X] Q.ResidueField := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R[X] B Q.ResidueField, RingHom.algebraMap_toAlgebra,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.algebraMap_eq, Polynomial.aeval_C,
      ← IsScalarTower.algebraMap_apply R B Q.ResidueField]
  have hX : algebraMap R[X] Q.ResidueField Polynomial.X =
      algebraMap A Q.ResidueField (a + π • b) := by
    rw [IsScalarTower.algebraMap_apply R[X] B Q.ResidueField, RingHom.algebraMap_toAlgebra,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X,
      ← IsScalarTower.algebraMap_apply A B Q.ResidueField]
  obtain ⟨htr, hsep⟩ := hb ⟨Q, hQ⟩
  dsimp only [F] at htr hsep
  rw [← hX] at htr hsep
  have : FiniteDimensional K⟮algebraMap R[X] Q.ResidueField Polynomial.X⟯ Q.ResidueField :=
    (hF Q hQ).finiteDimensional_adjoin htr
  exact finite_integralClosure_polynomial_of_isSeparable (K := K) htr

variable [Module.IsTorsionFree R A] [Algebra.FiniteType R A] [Algebra.IsPushout R A K B]

include R K in
private lemma finite_integralClosure_of_isTorsionFree [IsReduced B]
    (hF : ∀ (P : Ideal B) (hP : P ∈ minimalPrimes B), haveI := hP.1.1;
      IsFunctionField K P.ResidueField)
    (hΩ : ∀ (P : Ideal B) (hP : P ∈ minimalPrimes B), haveI := hP.1.1;
      Module.finrank P.ResidueField Ω[P.ResidueField⁄K] = 1) :
    Module.Finite A (integralClosure A B) := by
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away (algebraMap R A π) B := hπ.isLocalizationAway_of_isPushout (K := K)
  have : Algebra.IsPushout R K A B := Algebra.IsPushout.symm ‹_›
  have : Algebra.FiniteType K B :=
    .of_surjective (Algebra.IsPushout.equiv R K A B).toAlgHom
      (Algebra.IsPushout.equiv R K A B).surjective
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  have : Finite (minimalPrimes B) := minimalPrimes.finite_of_isNoetherianRing B
  have : Ring.KrullDimLE 1 B :=
    krullDimLE_of_forall_minimalPrimes_trdeg_le K fun P hP ↦ by simp [(hF P hP).trdeg_eq_one]
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
      have hsub : x - a = algebraMap R A π * b := by simp [x, Algebra.smul_def]
      rw [hsub]
      exact Ideal.mul_mem_right b _ (Ideal.mem_map_of_mem _ hπm)
    have : Algebra.QuasiFiniteAt R[X] q := ha x hxa q hmq
    exact Algebra.QuasiFiniteAt.exists_notMem_finite_localizedModule_integralClosure (P := R[X]) q
  · exact ⟨algebraMap R A π, hπq,
      finite_localizedModule_integralClosure (Submonoid.powers (algebraMap R A π))⟩

end TorsionFree

section General

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
  have : IsLocalization.Away (algebraMap R A π) B := hπ.isLocalizationAway_of_isPushout (K := K)
  let I := RingHom.ker (algebraMap A B)
  let A' := A ⧸ I
  let f' : A' →ₐ[R] B := Ideal.Quotient.liftₐ I (IsScalarTower.toAlgHom R A B) fun _ h ↦ h
  have hf'_inj : Function.Injective f' := RingHom.kerLift_injective (algebraMap A B)
  let : Algebra A' B := f'.toRingHom.toAlgebra
  have : IsScalarTower A A' B := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R A' B := .of_algebraMap_eq fun r ↦ by
    rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, f'.commutes]
  have : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr
    (IsFractionRing.injective R K)
  have : Module.IsTorsionFree R B := Module.IsTorsionFree.trans K
  have : Module.IsTorsionFree R A' := hf'_inj.moduleIsTorsionFree f' (map_smul f')
  have : Algebra.FiniteType R A' :=
    .of_surjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
  have : IsLocalization.Away (algebraMap R A' π) B := by
    rw [IsScalarTower.algebraMap_apply R A A', Ideal.Quotient.algebraMap_eq]
    exact IsLocalization.Away.of_quotient (algebraMap R A π) I
  have : Algebra.IsPushout R A' K B :=
    (Algebra.isLocalization_away_iff_isPushout (A := K) π).mp inferInstance
  have hfinA' : Module.Finite A' (integralClosure A' B) :=
    finite_integralClosure_of_isTorsionFree (R := R) (K := K) (A := A') (B := B) hF hΩ
  have hAA' : (algebraMap A A').Finite :=
    RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have : Algebra.IsIntegral A A' :=
    have : Module.Finite A A' := hAA'
    Algebra.IsIntegral.of_finite A A'
  let g : integralClosure A' B →+* integralClosure A B :=
    { toFun x := ⟨x.val, isIntegral_trans _ x.property⟩
      map_one' := rfl, map_mul' _ _ := rfl, map_zero' := rfl, map_add' _ _ := rfl }
  have hg : g.Finite :=
    RingHom.Finite.of_surjective g fun y ↦ ⟨⟨y.val, y.property.tower_top⟩, rfl⟩
  have hcomp : g.comp ((algebraMap A' (integralClosure A' B)).comp (algebraMap A A')) =
      algebraMap A (integralClosure A B) := by ext; rfl
  exact RingHom.finite_algebraMap.mp
    (hcomp ▸ hg.comp ((RingHom.finite_algebraMap.mpr hfinA').comp hAA'))

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
  have : Algebra.IsPushout R K A B := Algebra.IsPushout.symm ‹_›
  have : Algebra.FiniteType K B :=
    .of_surjective (Algebra.IsPushout.equiv R K A B).toAlgHom
      (Algebra.IsPushout.equiv R K A B).surjective
  have : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Algebra.FormallySmooth K B := by
    rw [← Algebra.smoothLocus_eq_univ_iff, ← Set.univ_subset_iff,
      ← TopologicalSpace.Opens.coe_top, ← PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hspan]
    simp only [TopologicalSpace.Opens.coe_iSup, Set.iUnion_subset_iff,
      Algebra.basicOpen_subset_smoothLocus_iff]
    exact fun r hr ↦ have := (hsmooth r hr).isStandardSmooth; inferInstance
  have : Algebra.Smooth K B := ⟨‹_›, ‹_›⟩
  have : IsReduced B := isReduced_of_smooth K B
  have hboth : ∀ (P : Ideal B) (hP : P ∈ minimalPrimes B), haveI := hP.1.1;
      IsFunctionField K P.ResidueField ∧ Module.finrank P.ResidueField Ω[P.ResidueField⁄K] = 1 := by
    intro P hP
    have : P.IsPrime := hP.1.1
    have hnot : ¬ s ⊆ P := fun hsub ↦
      ‹P.IsPrime›.ne_top (top_unique (hspan ▸ Ideal.span_le.mpr hsub))
    obtain ⟨t, hts, htP⟩ := Set.not_subset.mp hnot
    have := hsmooth t hts
    have hsub : Submonoid.powers t ≤ P.primeCompl :=
      (Submonoid.powers_le (P := P.primeCompl)).mpr htP
    have : IsLocalization.AtPrime P.ResidueField P :=
      isLocalization_atPrime_residueField_of_mem_minimalPrimes hP
    have : Algebra.EssFiniteType B P.ResidueField :=
      Algebra.EssFiniteType.of_isLocalization P.ResidueField P.primeCompl
    have : Algebra.EssFiniteType K P.ResidueField :=
      Algebra.EssFiniteType.comp K B P.ResidueField
    have htr : Algebra.trdeg K P.ResidueField = 1 := by
      simpa using trdeg_residueField_of_isStandardSmoothOfRelativeDimension K
        (S := Localization.Away t) 1 hP (.powers t) hsub
    exact ⟨(isFunctionField_iff_trdeg_eq_one (k := K) (F := P.ResidueField)).mpr htr,
      finrank_kaehlerDifferential_residueField_of_isStandardSmoothOfRelativeDimension
        (S := Localization.Away t) hP (.powers t) hsub 1⟩
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
