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
ideal. The same holds in any factorial domain localization where the inverse image of the open is
nonempty.
These facts describe the local boundary equations used for Cartier divisors.
-/

public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- Restriction from an affine open with factorial sections in an integral scheme to a nonempty
smaller open is bijective if the smaller open lies in no prime basic open. The smaller open need
not be affine. -/
theorem IsAffineOpen.presheaf_map_bijective_of_not_le_basicOpen {X : Scheme.{u}}
    [IsIntegral X] {U V : X.Opens} (hV : IsAffineOpen V) (hUV : U ≤ V)
    [UniqueFactorizationMonoid Γ(X, V)] [Nonempty U]
    (h : ∀ π : Γ(X, V), Prime π → ¬U ≤ X.basicOpen π) :
    Function.Bijective (X.presheaf.map (homOfLE hUV : U ⟶ V).op) := by
  have : Nonempty V := ⟨⟨(Nonempty.some ‹Nonempty U›).val,
    hUV (Nonempty.some ‹Nonempty U›).property⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  refine ⟨map_injective_of_isIntegral X _, fun s ↦ ?_⟩
  let r := X.germToFunctionField U s
  suffices hr : IsLocalization.IsInteger Γ(X, V) r by
    obtain ⟨a, ha⟩ := hr
    refine ⟨a, X.germToFunctionField_injective U ?_⟩
    rw [X.presheaf.germ_res_apply]
    simpa only [RingHom.algebraMap_toAlgebra] using ha
  -- A nonunit reduced denominator has a prime factor. At a point of U outside its basic open,
  -- the section's germ would make that prime factor a unit, giving a contradiction.
  apply IsFractionRing.isInteger_of_isUnit_den
  by_contra hb
  obtain ⟨π, hπirr, hπden⟩ := WfDvdMonoid.exists_irreducible_factor hb
    (nonZeroDivisors.ne_zero (IsFractionRing.den Γ(X, V) r).property)
  obtain ⟨y, hyU, hyπ⟩ := Set.not_subset.mp (h π hπirr.prime)
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hUV hyU⟩ : V)
  have := hV.isLocalization_stalk ⟨y, hUV hyU⟩
  have := functionField_isScalarTower X V ⟨y, hUV hyU⟩
  obtain ⟨⟨c, t⟩, hct⟩ := IsLocalization.surj
    (hV.primeIdealOf ⟨y, hUV hyU⟩).asIdeal.primeCompl
    (X.presheaf.germ U y hyU s)
  have hr : IsLocalization.IsInteger Γ(X, V) (algebraMap Γ(X, V) X.functionField t * r) := by
    refine ⟨c, ?_⟩
    have hct' := congrArg (algebraMap (X.presheaf.stalk y) X.functionField) hct
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply,
      X.algebraMap_germ_eq_germToFunctionField hyU s, mul_comm] using hct'.symm
  have hden := IsFractionRing.den_dvd_iff_isInteger_mul.mpr hr
  apply hyπ
  apply (X.mem_basicOpen π y (hUV hyU)).mpr
  apply isUnit_of_dvd_unit (map_dvd (X.presheaf.germ V y (hUV hyU)).hom (hπden.trans hden))
  rw [← X.presheaf.stalk_open_algebraMap (U := V) ⟨y, hUV hyU⟩]
  exact IsLocalization.map_units _ t

/-- A nonempty affine open inside an affine open with factorial sections in an integral scheme
is the whole larger open if it is contained in no prime basic open of the larger open. -/
theorem IsAffineOpen.eq_of_le_of_not_le_basicOpen {X : Scheme.{u}}
    [IsIntegral X] {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)
    [UniqueFactorizationMonoid Γ(X, V)] [Nonempty U]
    (h : ∀ π : Γ(X, V), Prime π → ¬U ≤ X.basicOpen π) : U = V := by
  let ρ := X.presheaf.map (homOfLE hUV : U ⟶ V).op
  have hρ : Function.Bijective ρ := hV.presheaf_map_bijective_of_not_le_basicOpen hUV h
  -- The bijective restriction induces a spectrum isomorphism and hence covers V.
  have : IsIso ρ := (ConcreteCategory.isIso_iff_bijective ρ).mpr hρ
  refine le_antisymm hUV fun x hxV ↦ ?_
  obtain ⟨z, hz⟩ : x ∈ Set.range hV.fromSpec := hV.range_fromSpec ▸ hxV
  obtain ⟨z', rfl⟩ := (ConcreteCategory.bijective_of_isIso (Spec.map ρ).base).2 z
  rw [← SetLike.mem_coe, ← hU.range_fromSpec, ← hz]
  exact ⟨z', by rw [← Scheme.Hom.comp_apply, IsAffineOpen.map_fromSpec]⟩

/-- A nonempty proper affine open in the spectrum of a UFD lies in a prime basic open. -/
theorem IsAffineOpen.exists_prime_le_basicOpen {R : CommRingCat.{u}}
    [UniqueFactorizationMonoid R] {U : (Spec R).Opens} (hW : IsAffineOpen U)
    (hne : (U : Set (Spec R)).Nonempty) (hW' : U ≠ ⊤) :
    ∃ π : R, Prime π ∧ U ≤ PrimeSpectrum.basicOpen π := by
  have : Nontrivial R := hne.choose.nontrivial
  have : IsDomain R := {}
  by_contra! H
  have : Nonempty U := hne.to_subtype
  have : UniqueFactorizationMonoid Γ(Spec R, ⊤) :=
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv.symm.uniqueFactorizationMonoid
      inferInstance
  refine hW' (hW.eq_of_le_of_not_le_basicOpen (isAffineOpen_top _) le_top fun π hπ hle ↦
    H ((Scheme.ΓSpecIso R).hom π) ?_ ?_)
  · exact (MulEquiv.prime_iff
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv).mpr hπ
  · rwa [← basicOpen_eq_of_affine, Iso.hom_inv_id_apply]

private theorem exists_prime_localization_of_mem_minimalPrimes
    {R : CommRingCat.{u}} [UniqueFactorizationMonoid R]
    {U : (Spec R).Opens} (hW : IsAffineOpen U) (hne : (U : Set (Spec R)).Nonempty)
    {p : Ideal R} [p.IsPrime]
    (hq : p ∈ (PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ).minimalPrimes) :
    ∃ π' : Localization.AtPrime p, Prime π' ∧ p ≠ ⊥ ∧
      p ≤ (Ideal.span {π'}).under R := by
  have : Nontrivial R := hne.choose.nontrivial
  have : IsDomain R := {}
  set ideal := PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ
  have hqp : p.IsPrime := hq.1.1
  have hmem (q : PrimeSpectrum R) : ideal ≤ q.asIdeal ↔ q ∉ (U : Set (Spec R)) := by
    have hz := (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (U : Set (Spec R))ᶜ).trans
      U.isOpen.isClosed_compl.closure_eq
    exact (PrimeSpectrum.mem_zeroLocus q ideal).symm.trans (Set.ext_iff.mp hz q)
  have hbot (q : PrimeSpectrum R) (hP : q.asIdeal = ⊥) : q ∈ (U : Set (Spec R)) := by
    have hq : q = genericPoint (Spec R) := by
      apply PrimeSpectrum.ext
      simpa [genericPoint_eq_bot_of_affine] using hP
    rw [hq]
    exact ((genericPoint_spec (Spec R)).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  let ringMap : R ⟶ CommRingCat.of (Localization.AtPrime p) :=
    CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))
  have hasIdeal (x : PrimeSpectrum (Localization.AtPrime p)) :
      (Spec.map ringMap x).asIdeal = x.asIdeal.under R := by
    -- `ringMap` is the localization algebra map, so spectral contraction is `Ideal.under`.
    rfl
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hmax : (IsLocalRing.closedPoint (Localization.AtPrime p)).asIdeal.under R = p :=
    Localization.AtPrime.under_maximalIdeal
  have hclosed : Spec.map ringMap (IsLocalRing.closedPoint (Localization.AtPrime p)) ∉ U := by
    apply (hmem _).mp
    rw [hasIdeal, hmax]
    exact hq.1.2
  obtain ⟨π', hπ', hle⟩ := IsAffineOpen.exists_prime_le_basicOpen
    (hW.preimage (Spec.map ringMap))
    ((RingHom.denseRange_comap_of_injective _ hinj).exists_mem_open U.isOpen hne)
    fun h ↦ hclosed (by
      apply (Spec.map ringMap).mem_preimage.mp
      rw [h]
      trivial)
  let q : PrimeSpectrum (Localization.AtPrime p) :=
    ⟨_, (Ideal.span_singleton_prime hπ'.ne_zero).mpr hπ'⟩
  have hP' : q ∉ Spec.map ringMap ⁻¹ᵁ U := by
    intro h
    exact (PrimeSpectrum.mem_basicOpen π' q).mp (hle h) (Ideal.mem_span_singleton_self π')
  refine ⟨π', hπ', ?_, ?_⟩
  · exact fun hp ↦ (hmem ⟨p, hqp⟩).mp hq.1.2 (hbot _ hp)
  · have hqU : Spec.map ringMap q ∉ (U : Set (Spec R)) :=
      fun h ↦ hP' ((Spec.map ringMap).mem_preimage.mpr h)
    have hleq : (Spec.map ringMap q).asIdeal ≤ p := by
      rw [hasIdeal]
      exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal q.isPrime.ne_top)).trans hmax.le
    exact hq.2 ⟨(Spec.map ringMap q).isPrime, (hmem _).mpr hqU⟩ hleq

/-- Every minimal prime of the reduced complement of a nonempty affine open in the spectrum
of a UFD is generated by a prime element. No Noetherianity assumption is required. -/
theorem IsAffineOpen.exists_prime_eq_span_of_mem_minimalPrimes
    {R : CommRingCat.{u}} [UniqueFactorizationMonoid R]
    {U : (Spec R).Opens} (hW : IsAffineOpen U) (hne : (U : Set (Spec R)).Nonempty)
    {p : Ideal R} (hq : p ∈ (PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ).minimalPrimes) :
    ∃ π : R, Prime π ∧ p = Ideal.span {π} := by
  have : Nontrivial R := hne.choose.nontrivial
  have : IsDomain R := {}
  have : p.IsPrime := hq.1.1
  obtain ⟨π', hπ', hq0, hqP'⟩ := exists_prime_localization_of_mem_minimalPrimes hW hne hq
  obtain ⟨π, hπq, hπ⟩ := (hq.1.1).exists_mem_prime_of_ne_bot hq0
  refine ⟨π, hπ, ?_⟩
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hπp : Ideal.span {π} ≤ p := (Ideal.span_singleton_le_iff_mem p).mpr hπq
  have : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  have hspan : (Ideal.span {π}).map (algebraMap R (Localization.AtPrime p)) =
      Ideal.span {algebraMap R _ π} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hprime : Prime (algebraMap R (Localization.AtPrime p) π) := by
    refine (Ideal.span_singleton_prime ((map_ne_zero_iff _ hinj).mpr hπ.ne_zero)).mp ?_
    rw [← hspan]
    exact Ideal.isPrime_map_of_isLocalizationAtPrime p hπp
  have hdvd : π' ∣ algebraMap R _ π := Ideal.mem_span_singleton.mp (hqP' hπq)
  have hP'eq : Ideal.span {π'} = Ideal.span {algebraMap R _ π} :=
    Ideal.span_singleton_eq_span_singleton.mpr (hπ'.associated_of_dvd hprime hdvd)
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem p).mpr hπq)
  rwa [hP'eq, ← hspan, Ideal.under_map_of_isLocalizationAtPrime p hπp] at hqP'

/-- In the spectrum of a UFD, the reduced complement of a nonempty affine open is defined
by a nonzero principal ideal. No Noetherianity assumption is required. -/
theorem IsAffineOpen.exists_vanishingIdeal_compl_eq_span_singleton
    {R : CommRingCat.{u}} [UniqueFactorizationMonoid R] {U : (Spec R).Opens}
    (hW : IsAffineOpen U) (hne : (U : Set (Spec R)).Nonempty) :
    ∃ a : R, a ≠ 0 ∧ PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ = Ideal.span {a} := by
  have : Nontrivial R := hne.choose.nontrivial
  have : IsDomain R := {}
  exact (PrimeSpectrum.isRadical_vanishingIdeal _).exists_ne_zero_eq_span_singleton
    (Ideal.finite_minimalPrimes_of_forall_eq_span_singleton _
      fun _ hq ↦ hW.exists_prime_eq_span_of_mem_minimalPrimes hne hq)
    fun _ hq ↦ hW.exists_prime_eq_span_of_mem_minimalPrimes hne hq

/-- If an affine open in a spectrum has nonempty preimage in a factorial domain localization,
the reduced complement ideal becomes principal with a nonzero generator in that localization. -/
theorem IsAffineOpen.exists_ne_zero_map_vanishingIdeal_compl_eq_span_singleton
    {R : CommRingCat.{u}} {U : (Spec R).Opens} (hW : IsAffineOpen U)
    (M : Submonoid R) (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
    [UniqueFactorizationMonoid S]
    (hne : (Spec.map (CommRingCat.ofHom (algebraMap R S)) ⁻¹ᵁ U :
      Set (Spec (.of S))).Nonempty) :
    ∃ a : S, a ≠ 0 ∧
      (PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ).map
        (algebraMap R S) = Ideal.span {a} := by
  have : Nontrivial S := hne.choose.nontrivial
  have : IsDomain S := {}
  let ringMap : R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  obtain ⟨a, hf0, hf⟩ :=
    (hW.preimage (Spec.map ringMap)).exists_vanishingIdeal_compl_eq_span_singleton hne
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
