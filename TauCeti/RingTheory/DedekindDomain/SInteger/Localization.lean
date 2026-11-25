/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic

/-!
# Rings of `S`-integers as localizations

Let `R` be a Dedekind domain with fraction field `K` and `S` an arbitrary set of height-one primes
of `R`. This file decides exactly when the ring of `S`-integers `S.integer K` is a localization of
`R`, and at which submonoids.

The candidate denominators form Mathlib's `Localization.submonoid S`, the nonzero elements of `R`
lying in no prime outside `S`. `Localization.mem_submonoid_iff_isUnit` identifies it with the
elements of `R` that become units in `S.integer K`, so it is the inverse image of the units of
the existing subalgebra (`Localization.submonoid_eq_comap_isUnitSubmonoid`); its basic laws are
`Localization.zero_notMem_submonoid`, `Localization.submonoid_mono`,
`Localization.submonoid_empty` and `Localization.submonoid_univ`.

The main result is the localization criterion `IsDedekindDomain.integer_isLocalization_iff`: for
a submonoid `M` of `R`,
`IsLocalization M (S.integer K) ↔ M ≤ Localization.submonoid S ∧ ∀ v ∈ S, ∃ m ∈ M, m ∈ v`.
It needs no hypothesis on the class group, and it identifies any two valid denominator
presentations over `R` through Mathlib's `IsLocalization.algEquiv`. The criterion does not
always have a solution: for `S = {v}` with the class of `v` of infinite order, no nonzero element
of `R` has `v` as its only prime factor, so the `{v}`-integers are no localization of `R` at all
(see the module docstring of `TauCeti/RingTheory/DedekindDomain/SInteger/Basic.lean`).

When the class group is torsion, Mathlib's instance `IsDedekindDomain.isLocalizationSInteger`
shows that the full candidate monoid works for every `S`. The criterion then shows that each
prime of `S` contains a candidate denominator (`exists_mem_submonoid_mem_asIdeal`), and for
finite `S` the product of such denominators is a single element `s` with `S.integer K = R[1/s]`
(`exists_integer_isLocalization_away`). Without the torsion hypothesis, finite `S` admits such
a single denominator exactly when each of its primes contains a candidate denominator
(`exists_integer_isLocalization_away_iff`). No prime of `S` need be principal: in `ℤ[√-5]` the
prime `p = (2, 1 + √-5)` is not principal, but `p ^ 2 = (2)` and inverting `2` gives the
`{p}`-integers.

Inverting a single nonzero element `r` always gives the `S`-integers for the set `S` of primes
containing `r` (`integer_isLocalization_away_setOf_mem`). Elementwise, some `r ^ n * x` lies in
`R` exactly when `x` is an `S`-integer, that is, integral at every prime not containing `r`
(`exists_pow_mul_mem_range_iff_mem_integer`). When `R` is the integral closure of `A` in `K`,
the same holds with `r ^ n * x` integral over `A` (`exists_isIntegral_pow_mul_iff_mem_integer`);
this describes the elements of a number field that are integral away from a rational prime `l`,
as `ℤ[1/l]`-multiples of algebraic integers.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I, Section 3,
  pp. 21–22, and Exercise I.3.8, p. 29.
-/

public section

open IsDedekindDomain

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R]

namespace Localization

section Base

variable (S : Set (HeightOneSpectrum R))

/-- No candidate denominator is zero. -/
lemma zero_notMem_submonoid [Nontrivial R] : (0 : R) ∉ Localization.submonoid S :=
  fun h ↦ zero_notMem_nonZeroDivisors (Localization.submonoid_le_nonZeroDivisors S h)

/-- The candidate denominator monoid grows with the set of primes allowed in the support. -/
lemma submonoid_mono {S S' : Set (HeightOneSpectrum R)} (h : S ⊆ S') :
    Localization.submonoid S ≤ Localization.submonoid S' :=
  inf_le_inf_right _ (Ideal.sInfPrimeCompl_anti (Set.image_mono (Set.compl_subset_compl.2 h)) _)

/-- With no prime allowed in the support, the candidate denominators are the units of `R`. -/
@[simp]
lemma submonoid_empty :
    Localization.submonoid (∅ : Set (HeightOneSpectrum R)) = IsUnit.submonoid R := by
  ext r
  simp only [Localization.mem_submonoid_iff, Set.mem_empty_iff_false, not_false_eq_true,
    forall_const, IsUnit.mem_submonoid_iff]
  refine ⟨fun ⟨h, hr⟩ ↦ ?_, fun hu ↦ ⟨fun v hv ↦ v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
    hv hu), hu.mem_nonZeroDivisors⟩⟩
  by_contra hu
  obtain ⟨P, hP, hrP⟩ := exists_max_ideal_of_mem_nonunits hu
  have : Nontrivial R := ⟨⟨r, 1, fun h ↦ hu (by rw [h]; exact isUnit_one)⟩⟩
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  exact h ⟨P, hP.isPrime, fun hP0 ↦ hr0 (by simpa [hP0] using hrP)⟩ hrP

/-- With every prime allowed in the support, the candidate denominators are all nonzero
elements of `R`. -/
@[simp]
lemma submonoid_univ :
    Localization.submonoid (Set.univ : Set (HeightOneSpectrum R)) = R⁰ := by
  ext r
  simp [Localization.mem_submonoid_iff]

end Base

variable [IsDedekindDomain R]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (S : Set (HeightOneSpectrum R))

/-- An element of `R` is a candidate denominator for the `S`-integers exactly when it becomes a
unit in `S.integer K`. -/
theorem mem_submonoid_iff_isUnit {r : R} :
    r ∈ Localization.submonoid S ↔ IsUnit (algebraMap R (S.integer K) r) := by
  rw [Localization.mem_submonoid_iff]
  constructor
  · rintro ⟨hS, hr⟩
    have h0 : algebraMap R K r ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr
    have hinv : (algebraMap R K r)⁻¹ ∈ S.integer K := fun v hv ↦ by
      rw [map_inv₀, (v.valuation_eq_one_iff_notMem (K := K)).2 (hS v hv), inv_one]
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  · intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : algebraMap R K r * b = 1 := by simpa using congrArg Subtype.val hb
    refine ⟨fun v hv hrv ↦ ?_, mem_nonZeroDivisors_of_ne_zero fun hr ↦ by simp [hr] at hb'⟩
    have h1 : v.valuation K (algebraMap R K r) = 1 :=
      eq_one_of_one_le_mul_left (v.valuation_le_one r) (Set.integer_valuation_le_one S K b hv)
        (by rw [← map_mul, hb', map_one])
    exact (v.valuation_eq_one_iff_notMem (K := K)).1 h1 hrv

/-- The candidate denominator monoid is the inverse image in `R` of the units of the ring of
`S`-integers. -/
theorem submonoid_eq_comap_isUnitSubmonoid :
    Localization.submonoid S =
      (IsUnit.submonoid (S.integer K)).comap (algebraMap R (S.integer K)) := by
  ext r
  rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, mem_submonoid_iff_isUnit K]

end Localization

namespace IsDedekindDomain

variable [IsDedekindDomain R]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (S : Set (HeightOneSpectrum R))

/-- **Localization criterion for `S`-integers.** For an arbitrary set `S` of height-one primes,
the ring of `S`-integers is the localization of `R` at a submonoid `M` exactly when every element
of `M` is a candidate denominator (it lies in no prime outside `S`) and every prime of `S`
contains an element of `M`. -/
theorem integer_isLocalization_iff (M : Submonoid R) :
    IsLocalization M (S.integer K) ↔
      M ≤ Localization.submonoid S ∧ ∀ v ∈ S, ∃ m ∈ M, m ∈ v.asIdeal := by
  constructor
  · intro hM
    refine ⟨fun m hm ↦ (Localization.mem_submonoid_iff_isUnit K S).2
      (IsLocalization.map_units (S.integer K) ⟨m, hm⟩), fun v hv ↦ ?_⟩
    -- A prime disjoint from `M` would stay prime in the localization, but primes of `S` extend
    -- to the unit ideal of `S.integer K`.
    by_contra! hdisj
    have hprime := IsLocalization.isPrime_of_isPrime_disjoint M (S.integer K) v.asIdeal
      v.isPrime (Set.disjoint_left.2 fun m hmM hmv ↦ hdisj m hmM hmv)
    exact hprime.ne_top (integer_map_asIdeal_eq_top K S hv)
  · rintro ⟨hMS, hSM⟩
    refine
      { map_units := fun m ↦ (Localization.mem_submonoid_iff_isUnit K S).1 (hMS m.property)
        surj := fun z ↦ ?_
        exists_of_eq := fun h ↦
          ⟨1, by simpa using FaithfulSMul.algebraMap_injective R (S.integer K) h⟩ }
    -- The denominator ideal of `z` meets `M`: a prime containing it and avoiding `M` would be
    -- a prime of `S` (because `z` is integral outside `S`) avoiding `M`.
    obtain ⟨m, hmM, hmD⟩ : ∃ m ∈ M, m ∈ Algebra.denIdeal K (z : K) := by
      by_contra! hcon
      obtain ⟨P, hP, hDP, hPM⟩ := Ideal.exists_le_prime_disjoint _ M
        (Set.disjoint_left.2 fun m hmD hmM ↦ hcon m hmM hmD)
      obtain ⟨v, hv, rfl⟩ := exists_mem_asIdeal_eq_of_denIdeal_le K S z.property hDP
      obtain ⟨m, hmM, hmP⟩ := hSM v hv
      exact Set.disjoint_left.1 hPM hmP hmM
    obtain ⟨s, hs⟩ := (Algebra.mem_denIdeal_iff K).1 hmD
    exact ⟨(s, ⟨m, hmM⟩), Subtype.ext (by simpa [mul_comm] using hs)⟩

/-- When the class group is torsion, every prime of `S` contains a candidate denominator for the
`S`-integers: some nonzero element of `v` lies in no prime outside `S`. For `S = {v}` this is an
element whose only prime factor is `v`, for instance a generator of a principal power of `v`. -/
theorem exists_mem_submonoid_mem_asIdeal [Fact (IsMulTorsion (ClassGroup R))]
    {v : HeightOneSpectrum R} (hv : v ∈ S) :
    ∃ m ∈ Localization.submonoid S, m ∈ v.asIdeal :=
  ((integer_isLocalization_iff (FractionRing R) S _).1
    (isLocalizationSInteger R S (FractionRing R))).2 v hv

/-- For finite `S`, the ring of `S`-integers is obtained from `R` by inverting a single candidate
denominator `s` exactly when every prime of `S` contains a candidate denominator. For instance,
the product of one candidate denominator from each prime of `S` works as `s`. -/
theorem exists_integer_isLocalization_away_iff [Finite S] :
    (∃ s ∈ Localization.submonoid S, IsLocalization.Away s (S.integer K)) ↔
      ∀ v ∈ S, ∃ m ∈ Localization.submonoid S, m ∈ v.asIdeal := by
  refine ⟨fun ⟨s, hs, hloc⟩ v hv ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨m, hm, hmv⟩ := ((integer_isLocalization_iff K S _).1 hloc).2 v hv
    exact ⟨m, Submonoid.powers_le.2 hs hm, hmv⟩
  choose m hmS hmv using fun v : S ↦ h v v.property
  have := Fintype.ofFinite S
  have hs : ∏ v, m v ∈ Localization.submonoid S := prod_mem fun v _ ↦ hmS v
  refine ⟨∏ v, m v, hs, (integer_isLocalization_iff K S _).2
    ⟨Submonoid.powers_le.2 hs, fun v hv ↦ ⟨_, Submonoid.mem_powers _, ?_⟩⟩⟩
  exact Ideal.IsPrime.prod_mem_iff.2 ⟨⟨v, hv⟩, Finset.mem_univ _, hmv ⟨v, hv⟩⟩

/-- When the class group is torsion and `S` is finite, the ring of `S`-integers is obtained from
`R` by inverting a single candidate denominator `s`. For instance, the product of one candidate
denominator from each prime of `S` works as `s`. -/
theorem exists_integer_isLocalization_away [Fact (IsMulTorsion (ClassGroup R))] [Finite S] :
    ∃ s ∈ Localization.submonoid S, IsLocalization.Away s (S.integer K) :=
  (exists_integer_isLocalization_away_iff K S).2 fun _ hv ↦ exists_mem_submonoid_mem_asIdeal S hv

/-- Inverting a nonzero element `r` of `R` gives the ring of `S`-integers for the set `S` of primes
containing `r`: `R[1/r]` consists of the elements of `K` integral at every prime not containing
`r`. -/
theorem integer_isLocalization_away_setOf_mem {r : R} (hr : r ≠ 0) :
    IsLocalization.Away r ({v : HeightOneSpectrum R | r ∈ v.asIdeal}.integer K) :=
  (integer_isLocalization_iff K _ _).2
    ⟨Submonoid.powers_le.2 ((Localization.mem_submonoid_iff _).2
      ⟨fun _ hv ↦ hv, mem_nonZeroDivisors_of_ne_zero hr⟩),
    fun _ hv ↦ ⟨r, Submonoid.mem_powers r, hv⟩⟩

/-- An element `x` of `K` becomes an element of `R` after multiplication by some power of `r`
exactly when `x` is an `S`-integer for the set `S` of primes containing `r`, that is, `x` is
integral at every prime not containing `r`. For `r = 0` both sides hold for every `x`. -/
theorem exists_pow_mul_mem_range_iff_mem_integer (r : R) (x : K) :
    (∃ n : ℕ, algebraMap R K r ^ n * x ∈ (algebraMap R K).range) ↔
      x ∈ {v : HeightOneSpectrum R | r ∈ v.asIdeal}.integer K := by
  refine ⟨fun ⟨n, a, ha⟩ ↦ (Set.mem_integer_iff K _).2 fun v hv ↦ ?_, fun h ↦ ?_⟩
  · have hle : v.valuation K (algebraMap R K a) ≤ 1 := v.valuation_le_one a
    rwa [ha, map_mul, map_pow, (v.valuation_eq_one_iff_notMem).2 hv, one_pow, one_mul] at hle
  obtain rfl | hr := eq_or_ne r 0
  · exact ⟨1, 0, by simp⟩
  have := integer_isLocalization_away_setOf_mem K hr
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj r (⟨x, h⟩ :
    {v : HeightOneSpectrum R | r ∈ v.asIdeal}.integer K)
  exact ⟨n, a, by simpa [mul_comm] using (congrArg Subtype.val ha).symm⟩

/-- Let `R` be the integral closure of `A` in `K`, such as the ring of integers of a number field
over `ℤ`. An element `x` of `K` becomes integral over `A` after multiplication by some power of
`r` exactly when `x` is an `S`-integer for the set `S` of primes containing `r`. -/
theorem exists_isIntegral_pow_mul_iff_mem_integer {A : Type*} [CommRing A] [Algebra A K]
    [IsIntegralClosure R A K] (r : R) (x : K) :
    (∃ n : ℕ, IsIntegral A (algebraMap R K r ^ n * x)) ↔
      x ∈ {v : HeightOneSpectrum R | r ∈ v.asIdeal}.integer K := by
  rw [← exists_pow_mul_mem_range_iff_mem_integer]
  simp [IsIntegralClosure.isIntegral_iff (A := R), RingHom.mem_range]

end IsDedekindDomain
