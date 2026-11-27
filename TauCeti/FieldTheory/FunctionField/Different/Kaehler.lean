/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Completion
public import TauCeti.RingTheory.FittingIdeal.Basic
import TauCeti.RingTheory.DedekindDomain.Different.Kaehler
import TauCeti.RingTheory.FittingIdeal.BaseChange

/-!
# The Kähler different of a place with separable residue field

Let `F' / F` be a finite separable extension of function fields and `P'` a place of `F'` over
`P = P'.restrict k F`. The Kähler different of the valuation-ring extension `𝒪_{P'} / 𝒪_P` (and of
the completed extension `𝒪̂_{P'} / 𝒪̂_P`) is the zeroth Fitting ideal of `Ω[𝒪_{P'}⁄𝒪_P]` (or
`Ω[𝒪̂_{P'}⁄𝒪̂_P]`), the local form of the ramification ideal sheaf
`TauCeti.AlgebraicGeometry.ramificationIdealSheaf` of a finite map of curves.

When the residue extension at `P'` is separable, `𝒪_{P'}` is the localization at the centre of `P'`
of the local model `𝒪'_P`, which is locally monogenic there, and the Kähler different is
`𝔪_{P'} ^ d(P' ∣ P)`, with `d(P' ∣ P)` the exponent of the trace-dual different (and likewise on
completions `𝔪̂_{P'} ^ d(P' ∣ P)`). Only the residue extension at `P'` is assumed separable: the
constant fields are arbitrary, and other places of `F'` may be wildly ramified or have inseparable
residue extensions.

## Main results

* `TauCeti.Place.moduleFinite_kaehlerDifferential_integers`: `Ω[𝒪_{P'}⁄𝒪_P]` is finite over
  `𝒪_{P'}`.
* `TauCeti.Place.fittingIdeal_kaehlerDifferential_integers_eq_maximalIdeal_pow`:
  `Fitt₀(Ω[𝒪_{P'}⁄𝒪_P]) = 𝔪_{P'} ^ d(P' ∣ P)` when the residue extension is separable.
* `TauCeti.Place.fittingIdeal_kaehlerDifferential_completionIntegers_eq_maximalIdeal_pow`:
  `Fitt₀(Ω[𝒪̂_{P'}⁄𝒪̂_P]) = 𝔪̂_{P'} ^ d(P' ∣ P)` when the residue extension is separable.

## References

* [Stacks Project, Tag 0BVH](https://stacks.math.columbia.edu/tag/0BVH): the Kähler different.
* J.-P. Serre, *Local Fields*, Chapter III, §6, Corollary 2 of Proposition 11 and Proposition 12.
-/

public section

open IsLocalRing

namespace TauCeti.Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

private noncomputable abbrev algebraIntegralClosureIntegers (P' : Place k' F') :
    Algebra (integralClosure (P'.restrict k F).integers F') P'.integers :=
  ((algebraMap (integralClosure (P'.restrict k F).integers F') F').codRestrict
    P'.integers (algebraMap_mem_integers_of_mem_integralClosure k F P')).toAlgebra

omit [FiniteDimensional F F'] in
private theorem isScalarTower_integers_integralClosure_integers (P' : Place k' F') :
    letI := algebraIntegralClosureIntegers (k := k) (F := F) P'
    IsScalarTower (P'.restrict k F).integers (integralClosure (P'.restrict k F).integers F')
      P'.integers :=
  letI := algebraIntegralClosureIntegers (k := k) (F := F) P'
  .of_algebraMap_eq fun _ ↦ rfl

private theorem isLocalization_centerIntegralClosure_integers (P' : Place k' F') :
    letI := algebraIntegralClosureIntegers (k := k) (F := F) P'
    IsLocalization (centerIntegralClosure k F P').asIdeal.primeCompl P'.integers := by
  let _ := algebraIntegralClosureIntegers (k := k) (F := F) P'
  let q := centerIntegralClosure k F P'
  let eB : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F' q ≃ₐ[
      integralClosure (P'.restrict k F).integers F'] P'.integers :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr
        (congrArg ValuationSubring.toSubring (by
          dsimp only [q]
          rw [centerIntegralClosure_def]
          exact P'.valuationSubringAtPrime_eq_integers
            (algebraMap_mem_integers_of_mem_integralClosure k F P'))))
      fun _ ↦ rfl
  exact IsLocalization.isLocalization_of_algEquiv q.asIdeal.primeCompl eB

private theorem isSeparable_quotient_centerIntegralClosure (P' : Place k' F')
    [Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField] :
    letI : (centerIntegralClosure k F P').asIdeal.IsMaximal :=
      (centerIntegralClosure k F P').isPrime.isMaximal (centerIntegralClosure k F P').ne_bot
    letI : Field ((P'.restrict k F).integers ⧸ maximalIdeal (P'.restrict k F).integers) :=
      Ideal.Quotient.field _
    letI : Field (integralClosure (P'.restrict k F).integers F' ⧸
        (centerIntegralClosure k F P').asIdeal) :=
      Ideal.Quotient.field _
    Algebra.IsSeparable
      ((P'.restrict k F).integers ⧸ maximalIdeal (P'.restrict k F).integers)
      (integralClosure (P'.restrict k F).integers F' ⧸
        (centerIntegralClosure k F P').asIdeal) := by
  let O := (P'.restrict k F).integers
  let B := integralClosure O F'
  let q := centerIntegralClosure k F P'
  have hB := algebraMap_mem_integers_of_mem_integralClosure k F P'
  have : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  let _ : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
  let _ : Field (B ⧸ q.asIdeal) := Ideal.Quotient.field _
  let e₀ : (O ⧸ maximalIdeal O) ≃+* (P'.restrict k F).ResidueField := RingEquiv.refl _
  let e : (B ⧸ q.asIdeal) ≃+* P'.ResidueField :=
    (Ideal.quotEquivOfEq (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
      (centerIntegralClosure_def k F P'))).trans
      (P'.quotientRingEquivResidueField hB)
  have he : (algebraMap (P'.restrict k F).ResidueField P'.ResidueField).comp e₀.toRingHom =
      e.toRingHom.comp (algebraMap (O ⧸ maximalIdeal O) (B ⧸ q.asIdeal)) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ ?_)
    simp only [RingHom.comp_apply, Ideal.Quotient.algebraMap_mk_of_liesOver, e,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.trans_apply]
    change algebraMap _ _ (IsLocalRing.residue _ r) = _
    rw [IsLocalRing.ResidueField.algebraMap_residue, Ideal.quotEquivOfEq_mk,
      quotientRingEquivResidueField_mk, residueRingHom_apply]
    refine congrArg (IsLocalRing.residue P'.integers) (Subtype.ext ?_)
    change algebraMap F F' r.val =
      (algebraMap (integralClosure O F') F') ((algebraMap O B) r)
    rw [← IsScalarTower.algebraMap_apply O B F', IsScalarTower.algebraMap_apply O F F']
    rfl
  exact (Algebra.IsSeparable.iff_of_equiv_equiv e₀ e he).mpr ‹_›

private theorem differentIdeal_map_integers_eq_maximalIdeal_pow (P' : Place k' F') :
    letI := algebraIntegralClosureIntegers (k := k) (F := F) P'
    (differentIdeal (P'.restrict k F).integers
        (integralClosure (P'.restrict k F).integers F')).map
      (algebraMap (integralClosure (P'.restrict k F).integers F') P'.integers) =
      maximalIdeal P'.integers ^ differentExponent k F P' := by
  let O := (P'.restrict k F).integers
  let B := integralClosure O F'
  let q := centerIntegralClosure k F P'
  let _ := algebraIntegralClosureIntegers (k := k) (F := F) P'
  have : IsScalarTower O B P'.integers := isScalarTower_integers_integralClosure_integers P'
  have : IsLocalization q.asIdeal.primeCompl P'.integers :=
    isLocalization_centerIntegralClosure_integers P'
  have : IsLocalization.AtPrime P'.integers q.asIdeal := ‹_›
  have hB0 : differentIdeal O B ≠ ⊥ := differentIdeal_ne_bot_of_isSeparable (K := F) (L := F')
  have hInj : Function.Injective (algebraMap B P'.integers) := fun a b hab ↦
    IsIntegralClosure.algebraMap_injective B O F' (congrArg (fun x : P'.integers ↦ (x : F')) hab)
  have hmap0 : (differentIdeal O B).map (algebraMap B P'.integers) ≠ ⊥ := by
    intro h
    refine hB0 (eq_bot_iff.mpr fun x hx ↦ hInj.eq_iff.mp ?_)
    rw [map_zero]
    exact Ideal.mem_bot.mp (h ▸ Ideal.mem_map_of_mem (algebraMap B P'.integers) hx)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P'.integers
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmap0 hϖ
  have hmapq : q.asIdeal.map (algebraMap B P'.integers) = maximalIdeal P'.integers :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal P'.integers
  have hlies : (maximalIdeal P'.integers).LiesOver q.asIdeal := by
    rw [Ideal.liesOver_iff, IsLocalization.AtPrime.under_maximalIdeal P'.integers q.asIdeal]
  have hM0 : maximalIdeal P'.integers ≠ ⊥ := IsDiscreteValuationRing.not_a_field P'.integers
  have hone : q.asIdeal.ramificationIdx' (maximalIdeal P'.integers) = 1 := by
    have h : q.asIdeal.ramificationIdx' (q.asIdeal.map (algebraMap B P'.integers)) = 1 :=
      Ideal.ramificationIdx'_map_self_eq_one
        (by rw [hmapq]; exact (maximalIdeal.isMaximal P'.integers).isPrime.ne_top)
        (by rwa [hmapq])
    rwa [hmapq] at h
  have : FaithfulSMul B P'.integers :=
    (faithfulSMul_iff_algebraMap_injective B P'.integers).mpr hInj
  have heq : n = differentExponent k F P' := by
    have hmul := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hB0
      (Ideal.prime_of_isPrime q.ne_bot q.isPrime).irreducible
      (Ideal.prime_of_isPrime hM0 inferInstance).irreducible hM0
    rw [hone, Nat.cast_one, one_mul,
      (FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hM0 inferInstance)
        hmap0).emultiplicity_eq_multiplicity,
      (FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime q.ne_bot q.isPrime)
        hB0).emultiplicity_eq_multiplicity, hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
      multiplicity_pow_self_of_prime (Ideal.prime_of_isPrime hM0 inferInstance)] at hmul
    rw [differentExponent_def]
    exact_mod_cast hmul
  rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq, heq]

/-- **Finiteness of relative differentials of valuation rings**: for a finite separable extension
`F' / F` of function fields and a place `P'` over `P = P'.restrict k F`, `Ω[𝒪_{P'}⁄𝒪_P]` is a
finitely generated `𝒪_{P'}`-module, because `𝒪_{P'}` is a localization of the module-finite local
model `𝒪'_P`. -/
theorem moduleFinite_kaehlerDifferential_integers (P' : Place k' F') :
    Module.Finite P'.integers Ω[P'.integers⁄(P'.restrict k F).integers] := by
  let O := (P'.restrict k F).integers
  let B := integralClosure O F'
  let _ := algebraIntegralClosureIntegers (k := k) (F := F) P'
  have : IsScalarTower O B P'.integers := isScalarTower_integers_integralClosure_integers P'
  have : IsLocalization (centerIntegralClosure k F P').asIdeal.primeCompl P'.integers :=
    isLocalization_centerIntegralClosure_integers P'
  have : Algebra.FormallyEtale B P'.integers :=
    .of_isLocalization (centerIntegralClosure k F P').asIdeal.primeCompl
  have : Module.Finite O B := IsIntegralClosure.finite O F F' B
  exact Module.Finite.equiv
    (KaehlerDifferential.isBaseChange_of_formallyEtale O B P'.integers).equiv

/-- **The Kähler different at a place with separable residue field**: if `F' / F` is finite and
separable and the residue extension `F'_{P'} / F_P` at `P'` over `P = P'.restrict k F` is
separable, then `Fitt₀(Ω[𝒪_{P'}⁄𝒪_P]) = 𝔪_{P'} ^ d(P' ∣ P)`, the trace-dual different at `P'`. -/
theorem fittingIdeal_kaehlerDifferential_integers_eq_maximalIdeal_pow (P' : Place k' F')
    [Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField] :
    haveI := moduleFinite_kaehlerDifferential_integers (k := k) (F := F) P'
    fittingIdeal P'.integers Ω[P'.integers⁄(P'.restrict k F).integers] 0 =
      maximalIdeal P'.integers ^ differentExponent k F P' := by
  let O := (P'.restrict k F).integers
  let B := integralClosure O F'
  let q := centerIntegralClosure k F P'
  let _ := algebraIntegralClosureIntegers (k := k) (F := F) P'
  have : IsScalarTower O B P'.integers := isScalarTower_integers_integralClosure_integers P'
  have : IsLocalization q.asIdeal.primeCompl P'.integers :=
    isLocalization_centerIntegralClosure_integers P'
  have : IsLocalization.AtPrime P'.integers q.asIdeal := ‹_›
  have : Algebra.FormallyEtale B P'.integers := .of_isLocalization q.asIdeal.primeCompl
  have : Module.Finite O B := IsIntegralClosure.finite O F F' B
  have hbc : (haveI := moduleFinite_kaehlerDifferential_integers (k := k) (F := F) P'
      fittingIdeal P'.integers Ω[P'.integers⁄O] 0) =
      (fittingIdeal B Ω[B⁄O] 0).map (algebraMap B P'.integers) :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale O B P'.integers).fittingIdeal_eq_map 0
  have : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  let _ : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
  let _ : Field (B ⧸ q.asIdeal) := Ideal.Quotient.field _
  have : Algebra.IsSeparable (O ⧸ maximalIdeal O) (B ⧸ q.asIdeal) :=
    isSeparable_quotient_centerIntegralClosure P'
  rw [hbc, TauCeti.fittingIdeal_kaehlerDifferential_map_eq_differentIdeal_map
      F F' (p := maximalIdeal O) q.asIdeal P'.integers,
    differentIdeal_map_integers_eq_maximalIdeal_pow P']

/-- **The Kähler different at a place with separable residue field.** If the residue extension at
`P'` over `P = P'.restrict k F` is separable, the zeroth Fitting ideal of the differentials of the
completed valuation ring `𝒪̂_{P'}` over `𝒪̂_P` is `𝔪̂_{P'} ^ d(P' ∣ P)`, the trace-dual different
of `P'`. -/
theorem fittingIdeal_kaehlerDifferential_completionIntegers_eq_maximalIdeal_pow (P' : Place k' F')
    [Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField] :
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    haveI := (P'.restrict k F).moduleFinite_completionIntegers P' rfl
    fittingIdeal P'.completionPlace.integers
        Ω[P'.completionPlace.integers⁄(P'.restrict k F).completionPlace.integers] 0 =
      maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).moduleFinite_completionIntegers P' rfl
  have := (P'.restrict k F).isSeparable_completion P' rfl
  have := (P'.isSeparable_residueField_completion_iff (k := k) (F := F)).mpr ‹_›
  rw [IsDiscreteValuationRing.fittingIdeal_kaehlerDifferential_eq_differentIdeal
      (P'.restrict k F).Completion P'.Completion,
    (P'.restrict k F).differentIdeal_completionIntegers_eq_maximalIdeal_pow P' rfl]

end TauCeti.Place
