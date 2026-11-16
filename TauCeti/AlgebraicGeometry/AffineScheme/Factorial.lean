/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.RingTheory.Ideal.MinimalPrime.Finite
public import TauCeti.RingTheory.Spectrum.Prime.Topology

import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import TauCeti.RingTheory.Localization.NumDen
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

/-!
# Affine opens in spectra of unique factorization domains

A proper nonempty affine open in the spectrum of a UFD lies in the basic open of a prime
element. The reduced complement of any nonempty affine open has a nonzero principal vanishing
ideal. Over a domain the same holds after any localization at nonzerodivisors that is a UFD.
These facts describe the local boundary equations used for Cartier divisors.
-/

public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- Restriction from an integral affine scheme with factorial global sections to a nonempty
open is bijective if that open lies in no prime basic open. The open need not be affine. -/
theorem Scheme.presheaf_map_leTop_bijective_of_not_le_basicOpen {X : Scheme.{u}} [IsAffine X]
    [IsIntegral X] [UniqueFactorizationMonoid Γ(X, ⊤)] {U : X.Opens} [Nonempty U]
    (h : ∀ π : Γ(X, ⊤), Prime π → ¬U ≤ X.basicOpen π) :
    Function.Bijective (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨(Nonempty.some ‹Nonempty U›).1, trivial⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  refine ⟨map_injective_of_isIntegral X _, fun s ↦ ?_⟩
  let r := X.germToFunctionField U s
  suffices hr : IsLocalization.IsInteger Γ(X, ⊤) r by
    obtain ⟨a, ha⟩ := hr
    refine ⟨a, X.germToFunctionField_injective U ?_⟩
    rw [X.presheaf.germ_res_apply]
    simpa only [RingHom.algebraMap_toAlgebra] using ha
  apply IsFractionRing.isInteger_of_isUnit_den
  by_contra hb
  obtain ⟨π, hπirr, hπden⟩ := WfDvdMonoid.exists_irreducible_factor hb
    (nonZeroDivisors.ne_zero (IsFractionRing.den Γ(X, ⊤) r).2)
  obtain ⟨y, hyU, hyπ⟩ := Set.not_subset.mp (h π hπirr.prime)
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, trivial⟩ : (⊤ : X.Opens))
  have := (isAffineOpen_top X).isLocalization_stalk ⟨y, trivial⟩
  have := functionField_isScalarTower X ⊤ ⟨y, trivial⟩
  obtain ⟨⟨c, t⟩, hct⟩ := IsLocalization.surj
    ((isAffineOpen_top X).primeIdealOf ⟨y, trivial⟩).asIdeal.primeCompl
    (X.presheaf.germ U y hyU s)
  have hr : IsLocalization.IsInteger Γ(X, ⊤) (algebraMap Γ(X, ⊤) X.functionField t * r) := by
    refine ⟨c, ?_⟩
    have hct' := congrArg (algebraMap (X.presheaf.stalk y) X.functionField) hct
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply,
      X.algebraMap_germ_eq_germToFunctionField hyU s, mul_comm] using hct'.symm
  have hden := IsFractionRing.den_dvd_iff_isInteger_mul.mpr hr
  apply hyπ
  apply (X.mem_basicOpen π y trivial).mpr
  apply isUnit_of_dvd_unit (map_dvd (X.presheaf.germ ⊤ y trivial).hom (hπden.trans hden))
  have heq := X.presheaf.stalk_open_algebraMap (U := ⊤) ⟨y, trivial⟩
  rw [← heq]
  exact IsLocalization.map_units _ t

/-- An affine open in an integral affine scheme with factorial global sections is the whole
scheme if it is contained in no basic open defined by a prime element. -/
theorem IsAffineOpen.eq_top_of_not_le_basicOpen {X : Scheme.{u}} [IsAffine X]
    [IsIntegral X] [UniqueFactorizationMonoid Γ(X, ⊤)] {U : X.Opens} (hW : IsAffineOpen U)
    [Nonempty U] (h : ∀ π : Γ(X, ⊤), Prime π → ¬U ≤ X.basicOpen π) : U = ⊤ := by
  let ρ := X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op
  have hρ : Function.Bijective ρ := X.presheaf_map_leTop_bijective_of_not_le_basicOpen h
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
theorem IsAffineOpen.exists_prime_le_basicOpen {R : CommRingCat.{u}} [IsDomain R]
    [UniqueFactorizationMonoid R] {U : (Spec R).Opens} (hW : IsAffineOpen U)
    (hne : (U : Set (Spec R)).Nonempty) (hW' : U ≠ ⊤) :
    ∃ π : R, Prime π ∧ U ≤ PrimeSpectrum.basicOpen π := by
  by_contra! H
  have : Nonempty U := hne.to_subtype
  have : UniqueFactorizationMonoid Γ(Spec R, ⊤) :=
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv.symm.uniqueFactorizationMonoid
      inferInstance
  refine hW' (hW.eq_top_of_not_le_basicOpen fun π hπ hle ↦
    H ((Scheme.ΓSpecIso R).hom π) ?_ ?_)
  · exact (MulEquiv.prime_iff
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv).mpr hπ
  · rwa [← basicOpen_eq_of_affine, Iso.hom_inv_id_apply]

private theorem exists_prime_localization_of_mem_minimalPrimes
    {R : CommRingCat.{u}} [IsDomain R] [UniqueFactorizationMonoid R]
    {U : (Spec R).Opens} (hW : IsAffineOpen U) (hne : (U : Set (Spec R)).Nonempty)
    {p : Ideal R} [p.IsPrime]
    (hq : p ∈ (PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ).minimalPrimes) :
    ∃ π' : Localization.AtPrime p, Prime π' ∧ p ≠ ⊥ ∧
      p ≤ (Ideal.span {π'}).under R := by
  set ideal := PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ
  have hqp : p.IsPrime := hq.1.1
  have hmem (q : PrimeSpectrum R) : ideal ≤ q.asIdeal ↔ q ∉ (U : Set (Spec R)) := by
    have hz := (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (U : Set (Spec R))ᶜ).trans
      U.isOpen.isClosed_compl.closure_eq
    exact (PrimeSpectrum.mem_zeroLocus q ideal).symm.trans (Set.ext_iff.mp hz q)
  have hbot (q : PrimeSpectrum R) (hP : q.asIdeal = ⊥) : q ∈ (U : Set (Spec R)) :=
    PrimeSpectrum.mem_of_isOpen_of_asIdeal_eq_bot U.isOpen hne hP
  let B' := CommRingCat.of (Localization.AtPrime p)
  let ringMap : R ⟶ B' := CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hmax : (IsLocalRing.closedPoint B').asIdeal.under R = p :=
    Localization.AtPrime.under_maximalIdeal
  obtain ⟨π', hπ', hle⟩ := IsAffineOpen.exists_prime_le_basicOpen
    (hW.preimage (Spec.map ringMap))
    ⟨⟨⊥, Ideal.isPrime_bot⟩, by
      change PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p))
        ⟨⊥, Ideal.isPrime_bot⟩ ∈ (U : Set (Spec R))
      exact hbot _ (Ideal.comap_bot_of_injective _ hinj)⟩
    fun h ↦ (hmem (Spec.map ringMap (IsLocalRing.closedPoint B'))).mp
      (le_of_le_of_eq hq.1.2 hmax.symm)
      (h.symm ▸ trivial : IsLocalRing.closedPoint B' ∈ Spec.map ringMap ⁻¹ᵁ U)
  let q : PrimeSpectrum B' := ⟨_, (Ideal.span_singleton_prime hπ'.ne_zero).mpr hπ'⟩
  have hP' : q ∉ Spec.map ringMap ⁻¹ᵁ U := by
    intro h
    exact (PrimeSpectrum.mem_basicOpen π' q).mp (hle h) (Ideal.mem_span_singleton_self π')
  refine ⟨π', hπ', ?_, ?_⟩
  · exact fun hp ↦ (hmem ⟨p, hqp⟩).mp hq.1.2 (hbot _ hp)
  · refine hq.2 ⟨(Spec.map ringMap q).isPrime, (hmem (Spec.map ringMap q)).mpr hP'⟩ ?_
    exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal q.2.ne_top)).trans hmax.le

/-- Every minimal prime of the reduced complement of a nonempty affine open in the spectrum
of a UFD is generated by a prime element. No Noetherianity assumption is required. -/
theorem IsAffineOpen.exists_prime_eq_span_of_mem_minimalPrimes
    {R : CommRingCat.{u}} [IsDomain R] [UniqueFactorizationMonoid R]
    {U : (Spec R).Opens} (hW : IsAffineOpen U) (hne : (U : Set (Spec R)).Nonempty)
    {p : Ideal R} (hq : p ∈ (PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ).minimalPrimes) :
    ∃ π : R, Prime π ∧ p = Ideal.span {π} := by
  have : p.IsPrime := hq.1.1
  obtain ⟨π', hπ', hq0, hqP'⟩ := exists_prime_localization_of_mem_minimalPrimes hW hne hq
  obtain ⟨π, hπq, hπ⟩ := (hq.1.1).exists_mem_prime_of_ne_bot hq0
  refine ⟨π, hπ, ?_⟩
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
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
  have hP'eq : Ideal.span {π'} = Ideal.span {algebraMap R _ π} :=
    Ideal.span_singleton_eq_span_singleton.mpr (hπ'.associated_of_dvd hprime hdvd)
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem p).mpr hπq)
  rwa [hP'eq, ← hspan, IsLocalization.under_map_of_isPrime_disjoint p.primeCompl _
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ) hdisj] at hqP'

/-- In the spectrum of a UFD, the reduced complement of a nonempty affine open is defined
by a nonzero principal ideal. No Noetherianity assumption is required. -/
theorem IsAffineOpen.exists_vanishingIdeal_compl_eq_span_singleton
    {R : CommRingCat.{u}} [IsDomain R] [UniqueFactorizationMonoid R] {U : (Spec R).Opens}
    (hW : IsAffineOpen U) (hne : (U : Set (Spec R)).Nonempty) :
    ∃ a : R, a ≠ 0 ∧ PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ = Ideal.span {a} := by
  exact (PrimeSpectrum.isRadical_vanishingIdeal _).exists_ne_zero_eq_span_singleton
    (Ideal.finite_minimalPrimes_of_forall_eq_span_singleton _
      fun _ hq ↦ hW.exists_prime_eq_span_of_mem_minimalPrimes hne hq)
    fun _ hq ↦ hW.exists_prime_eq_span_of_mem_minimalPrimes hne hq

/-- For a nonempty affine open in the spectrum of a domain, the reduced complement ideal has
a nonzero principal generator after any localization at nonzerodivisors that is a UFD. -/
theorem IsAffineOpen.exists_ne_zero_map_vanishingIdeal_compl_eq_span_singleton
    {R : CommRingCat.{u}} [IsDomain R]
    {U : (Spec R).Opens} (hW : IsAffineOpen U) (hne : (U : Set (Spec R)).Nonempty)
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) (S : Type u) [CommRing S]
    [Algebra R S] [IsLocalization M S] [UniqueFactorizationMonoid S] :
    ∃ a : S, a ≠ 0 ∧
      (PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ).map
        (algebraMap R S) = Ideal.span {a} := by
  have : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  let ringMap : R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S hM
  obtain ⟨a, hf0, hf⟩ :=
    (hW.preimage (Spec.map ringMap)).exists_vanishingIdeal_compl_eq_span_singleton
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by
        change PrimeSpectrum.comap (algebraMap R S) ⟨⊥, Ideal.isPrime_bot⟩ ∈
          (U : Set (Spec R))
        exact PrimeSpectrum.mem_of_isOpen_of_asIdeal_eq_bot U.isOpen hne
          (Ideal.comap_bot_of_injective _ hinj)⟩
  have hf' : (PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ).map
      (algebraMap R S) = Ideal.span {a} := by
    have hz := (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (U : Set (Spec R))ᶜ).trans
      U.isOpen.isClosed_compl.closure_eq
    have hpre : (Spec.map ringMap ⁻¹ᵁ U : Set (Spec (.of S)))ᶜ =
        PrimeSpectrum.comap (algebraMap R S) ⁻¹'
          PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ) := by
      rw [hz, (Spec.map ringMap).coe_preimage, ← Set.preimage_compl]
      ext x
      simp only [Set.mem_preimage, Spec.map_apply, ringMap,
        CommRingCat.hom_ofHom]
      rfl
    calc
      _ = ((PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ).map
          (algebraMap R S)).radical :=
        (congrArg (Ideal.map (algebraMap R S))
          (PrimeSpectrum.isRadical_vanishingIdeal _).radical.symm).trans
            (IsLocalization.map_radical M S
              (PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ))
      _ = PrimeSpectrum.vanishingIdeal
          (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
            PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ)) := by
        rw [PrimeSpectrum.preimage_comap_zeroLocus, ← PrimeSpectrum.zeroLocus_span,
          ← Ideal.map, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
      _ = _ := (congrArg PrimeSpectrum.vanishingIdeal hpre.symm).trans hf
  exact ⟨a, hf0, hf'⟩

end AlgebraicGeometry
