/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.RingTheory.Ideal.MinimalPrime.Finite
public import TauCeti.RingTheory.Spectrum.Prime.Topology

import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

/-!
# Affine opens in factorial affine schemes

A proper nonempty affine open in the spectrum of a UFD lies in the basic open of a prime
element. Consequently, over a Noetherian UFD its reduced complement has a nonzero principal
vanishing ideal. These facts describe the local boundary equations used for Cartier divisors.
-/

public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- An affine open in an integral factorial affine scheme is the whole scheme if it is
contained in no basic open defined by a prime element. -/
theorem Scheme.eq_top_of_isAffineOpen_of_not_le_basicOpen {X : Scheme.{u}} [IsAffine X]
    [IsIntegral X] [UniqueFactorizationMonoid Γ(X, ⊤)] {U : X.Opens} (hW : IsAffineOpen U)
    [Nonempty U] (h : ∀ π : Γ(X, ⊤), Prime π → ¬U ≤ X.basicOpen π) : U = ⊤ := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨(Nonempty.some ‹Nonempty U›).1, trivial⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  let ρ := X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op
  -- A reduced fraction representing a section over `U` has no prime factor in its
  -- denominator: such a factor would force `U` into its basic open.
  have hρ : Function.Bijective ρ := by
    refine ⟨map_injective_of_isIntegral X _, fun s ↦ ?_⟩
    obtain ⟨a, b, hab, hs⟩ :=
      IsFractionRing.exists_reduced_fraction Γ(X, ⊤) (X.germToFunctionField U s)
    by_cases hb : IsUnit (b : Γ(X, ⊤))
    · refine ⟨a * ↑hb.unit⁻¹, X.germToFunctionField_injective U ?_⟩
      rw [← hs, X.presheaf.germ_res_apply, eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
      calc algebraMap Γ(X, ⊤) X.functionField a
          = algebraMap Γ(X, ⊤) X.functionField (a * ↑hb.unit⁻¹ * b) := by
            rw [mul_assoc, hb.val_inv_mul, mul_one]
        _ = _ := map_mul _ _ _
    · exfalso
      obtain ⟨π, hπirr, hπb⟩ :=
        WfDvdMonoid.exists_irreducible_factor hb (nonZeroDivisors.ne_zero b.2)
      have hπ := hπirr.prime
      obtain ⟨y, hyW, hyπ⟩ := Set.not_subset.mp (h π hπ)
      let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, trivial⟩ : (⊤ : X.Opens))
      have := (isAffineOpen_top X).isLocalization_stalk ⟨y, trivial⟩
      obtain ⟨⟨c, t⟩, hcd⟩ := IsLocalization.mk'_surjective
        ((isAffineOpen_top X).primeIdealOf ⟨y, trivial⟩).asIdeal.primeCompl
        (X.presheaf.germ U y hyW s)
      have heq (a : Γ(X, ⊤)) :
          algebraMap Γ(X, ⊤) (X.presheaf.stalk y) a = X.presheaf.germ ⊤ y trivial a :=
        congrArg (fun f : Γ(X, ⊤) →+* X.presheaf.stalk y ↦ f a)
          (X.presheaf.stalk_open_algebraMap (U := ⊤) ⟨y, trivial⟩)
      -- The section algebra on the function field is induced by `germToFunctionField`.
      have e' (a : Γ(X, ⊤)) :
          X.germToFunctionField ⊤ a = algebraMap Γ(X, ⊤) X.functionField a := rfl
      have hπd : ¬π ∣ (t : Γ(X, ⊤)) := by
        refine fun hπd ↦ hyπ ((X.mem_basicOpen π y trivial).mpr (isUnit_of_dvd_unit
          (map_dvd (X.presheaf.germ ⊤ y trivial).hom hπd) ?_))
        rw [← heq]
        exact IsLocalization.map_units _ t
      have h1 := congrArg (algebraMap (X.presheaf.stalk y) X.functionField)
        (IsLocalization.mk'_spec (X.presheaf.stalk y) c t)
      dsimp only at hcd
      have hgerm (a : Γ(X, ⊤)) :
          algebraMap (X.presheaf.stalk y) X.functionField
            (X.presheaf.germ ⊤ y trivial a) = X.germToFunctionField ⊤ a :=
        X.algebraMap_germ_eq_germToFunctionField (U := ⊤) (x := y) trivial a
      rw [hcd, heq, heq, map_mul,
        X.algebraMap_germ_eq_germToFunctionField hyW s, hgerm, hgerm,
        ← hs, e', e'] at h1
      have h2 : a * t = b * c := IsFractionRing.injective Γ(X, ⊤) X.functionField (by
        rw [map_mul, map_mul, ← IsLocalization.mk'_spec X.functionField a b, ← h1]
        ring)
      obtain hπa | hπd' := hπ.dvd_or_dvd (h2 ▸ hπb.mul_right c)
      · exact hπ.not_isUnit (hab hπa hπb)
      · exact hπd hπd'
  -- A bijective restriction is an isomorphism, hence its spectrum covers all of `X`.
  have : IsIso ρ := (ConcreteCategory.isIso_iff_bijective ρ).mpr hρ
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨z, hz⟩ : x ∈ Set.range (isAffineOpen_top X).fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    trivial
  obtain ⟨z', rfl⟩ := (ConcreteCategory.bijective_of_isIso (Spec.map ρ).base).2 z
  rw [← SetLike.mem_coe, ← hW.range_fromSpec, ← hz]
  exact ⟨z', by rw [← Scheme.Hom.comp_apply, IsAffineOpen.map_fromSpec]⟩

/-- A nonempty proper affine open in the spectrum of a UFD lies in a prime basic open. -/
theorem IsAffineOpen.exists_prime_le_basicOpen (R : CommRingCat.{u}) [IsDomain R]
    [UniqueFactorizationMonoid R] {U : (Spec R).Opens} (hW : IsAffineOpen U)
    (hne : (U : Set (Spec R)).Nonempty) (hW' : U ≠ ⊤) :
    ∃ π : R, Prime π ∧ U ≤ PrimeSpectrum.basicOpen π := by
  by_contra! H
  have : Nonempty U := hne.to_subtype
  have : UniqueFactorizationMonoid Γ(Spec R, ⊤) :=
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv.symm.uniqueFactorizationMonoid
      inferInstance
  refine hW' (Scheme.eq_top_of_isAffineOpen_of_not_le_basicOpen hW fun π hπ hle ↦
    H ((Scheme.ΓSpecIso R).hom π) ?_ ?_)
  · exact (MulEquiv.prime_iff
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv).mpr hπ
  · rwa [← basicOpen_eq_of_affine, Iso.hom_inv_id_apply]

private theorem exists_prime_eq_span_of_mem_minimalPrimes (R : CommRingCat.{u}) [IsDomain R]
    [UniqueFactorizationMonoid R] {U : (Spec R).Opens} (hW : IsAffineOpen U)
    (hne : (U : Set (Spec R)).Nonempty) {p : Ideal R}
    (hq : p ∈ (PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ).minimalPrimes) :
    ∃ π : R, Prime π ∧ p = Ideal.span {π} := by
  set ideal := PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ
  have hqp : p.IsPrime := hq.1.1
  have hmem (q : PrimeSpectrum R) : ideal ≤ q.asIdeal ↔ q ∉ (U : Set (Spec R)) := by
    have hz := PrimeSpectrum.zeroLocus_vanishingIdeal_compl_of_isOpen U.isOpen
    exact (PrimeSpectrum.mem_zeroLocus q ideal).symm.trans (Set.ext_iff.mp hz q)
  have hbot (q : PrimeSpectrum R) (hP : q.asIdeal = ⊥) : q ∈ (U : Set (Spec R)) :=
    PrimeSpectrum.mem_of_isOpen_of_asIdeal_eq_bot U.isOpen hne hP
  have hq0 : p ≠ ⊥ := fun h ↦ (hmem ⟨p, hqp⟩).mp hq.1.2 (hbot _ h)
  obtain ⟨π, hπq, hπ⟩ := hqp.exists_mem_prime_of_ne_bot hq0
  refine ⟨π, hπ, ?_⟩
  let B' := CommRingCat.of (Localization.AtPrime p)
  let ringMap : R ⟶ B' := CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hmax : (IsLocalRing.closedPoint B').asIdeal.under R = p :=
    Localization.AtPrime.under_maximalIdeal
  obtain ⟨π', hπ', hle⟩ := IsAffineOpen.exists_prime_le_basicOpen B'
    (hW.preimage (Spec.map ringMap))
    ⟨⟨⊥, Ideal.isPrime_bot⟩, hbot _ (Ideal.comap_bot_of_injective _ hinj)⟩
    fun h ↦ (hmem (Spec.map ringMap (IsLocalRing.closedPoint B'))).mp
      (le_of_le_of_eq hq.1.2 hmax.symm)
      (h.symm ▸ trivial : IsLocalRing.closedPoint B' ∈ Spec.map ringMap ⁻¹ᵁ U)
  let q : PrimeSpectrum B' := ⟨_, (Ideal.span_singleton_prime hπ'.ne_zero).mpr hπ'⟩
  have hP' : q ∉ Spec.map ringMap ⁻¹ᵁ U := fun h ↦ hle h (Ideal.mem_span_singleton_self π')
  have hqP' : p ≤ q.asIdeal.under R := by
    refine hq.2 ⟨(Spec.map ringMap q).isPrime, (hmem (Spec.map ringMap q)).mpr hP'⟩ ?_
    exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal q.2.ne_top)).trans hmax.le
  have hdisj : Disjoint (p.primeCompl : Set R) (Ideal.span {π}) := by
    refine Set.disjoint_left.mpr fun x hx hx' ↦ hx ?_
    exact (Ideal.span_singleton_le_iff_mem p).mpr hπq hx'
  have hspan : (Ideal.span {π}).map (algebraMap R (Localization.AtPrime p)) =
      Ideal.span {algebraMap R _ π} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hprime : Prime (algebraMap R (Localization.AtPrime p) π) := by
    refine (Ideal.span_singleton_prime ((map_ne_zero_iff _ hinj).mpr hπ.ne_zero)).mp ?_
    rw [← hspan]
    exact IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl _ _
      ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ) hdisj
  have hdvd : π' ∣ algebraMap R _ π := Ideal.mem_span_singleton.mp (hqP' hπq)
  have hP'eq : q.asIdeal = Ideal.span {algebraMap R _ π} :=
    Ideal.span_singleton_eq_span_singleton.mpr (hπ'.associated_of_dvd hprime hdvd)
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem p).mpr hπq)
  rwa [hP'eq, ← hspan, IsLocalization.under_map_of_isPrime_disjoint p.primeCompl _
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ) hdisj] at hqP'

/-- In the spectrum of a Noetherian UFD, the reduced complement of a nonempty affine open
is defined by a nonzero principal ideal. -/
theorem IsAffineOpen.exists_vanishingIdeal_compl_eq_span_singleton
    (R : CommRingCat.{u}) [IsDomain R]
    [IsNoetherianRing R] [UniqueFactorizationMonoid R] {U : (Spec R).Opens}
    (hW : IsAffineOpen U) (hne : (U : Set (Spec R)).Nonempty) :
    ∃ a : R, a ≠ 0 ∧
      PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ = Ideal.span {a} :=
  (PrimeSpectrum.isRadical_vanishingIdeal _).exists_ne_zero_eq_span_singleton
    fun _ hq ↦ exists_prime_eq_span_of_mem_minimalPrimes R hW hne hq

end AlgebraicGeometry
