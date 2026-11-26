/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Nagata
public import TauCeti.RingTheory.RegularLocalRing.Locus

import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
import TauCeti.RingTheory.Ideal.Height
import TauCeti.RingTheory.Ideal.RegularPrincipal
import TauCeti.RingTheory.KrullDimension.Quotient
import TauCeti.RingTheory.Localization.Ideal
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.OfQuotient

/-!
# Finitely many non-regular points on a one-dimensional special fibre

Let `A` be a Noetherian ring and `π ∈ A` a nonzerodivisor such that `A ⧸ (π)` is a Nagata ring of
Krull dimension at most one; for instance, `A` is a flat algebra of finite type over a discrete
valuation ring with uniformizer `π` whose special fibre is a curve. If `A` is regular at the
minimal primes of `(π)`, the generic points of the special fibre, then only finitely many primes
containing `π` are non-regular points of `A`. For the total space of a normal model of a curve
over a discrete valuation ring, this says that the model has only finitely many singular points
in its special fibre: that is one of the hypotheses of Lipman's resolution of two-dimensional
schemes by normalized blowups, and it holds without any excellence assumption on the discrete
valuation ring.

The proof spreads regularity out from each minimal prime `q` of `(π)`. The local ring `A_q` is a
discrete valuation ring, so `q` is generated near `q` by a single nonzerodivisor `t`; on a basic
open neighbourhood `D(r)` of `q`, regularity of `A` at a prime containing `q` then follows from
regularity of the domain `A ⧸ q` there. As `A ⧸ q` is a one-dimensional Japanese domain, it is
integrally closed, hence regular, on a nonempty basic open `D(b)`. The non-regular primes
containing `q` therefore contain `q + (r b)`, and these are maximal, hence finitely many.

## Main results

* `TauCeti.Excellence.exists_ne_zero_basicOpen_subset_regularLocus`: the regular locus of a
  Noetherian N-1 domain of dimension at most one contains a nonempty basic open.
* `TauCeti.Excellence.exists_notMem_forall_comap_mem_regularLocus_of_height_eq_one`: regularity at a
  prime `q` of height one spreads to the primes near `q` at which `A ⧸ q` is regular.
* `TauCeti.Excellence.finite_zeroLocus_sdiff_regularLocus`: only finitely many primes containing
  `π` are non-regular.

## References

* The Stacks Project, Lemma 10.106.7 (00NU), for regularity along a nonzerodivisor.
* The Stacks Project, Lemma 55.8.3 (0C2U) and Theorem 54.14.5 (0BGP), where the finiteness of the
  singular locus of a normal model of a smooth curve enters Lipman's resolution.
-/

public section

namespace TauCeti.Excellence

/-- **The regular locus of a one-dimensional N-1 domain contains a nonempty basic open.** If `B`
is a Noetherian N-1 domain of Krull dimension at most one, for instance a one-dimensional domain
of finite type over a field, there is a nonzero `b` such that `B` is regular at every prime not
containing `b`: on `D(b)` the domain `B` is integrally closed, hence a Dedekind domain. -/
theorem exists_ne_zero_basicOpen_subset_regularLocus (B : Type*) [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [Ring.IsN1 B] [Ring.KrullDimLE 1 B] :
    ∃ b : B, b ≠ 0 ∧ (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ regularLocus B := by
  obtain ⟨b, hb, _⟩ := Ring.IsN1.exists_isIntegrallyClosed_localization_away (R := B)
  refine ⟨b, hb, fun P hbP ↦ ?_⟩
  let S := Localization.Away b
  -- `P` is the contraction of a prime `Q` of `S`, at which the integrally closed `S` is regular.
  obtain ⟨Q, rfl⟩ : P ∈ Set.range (PrimeSpectrum.comap (algebraMap B S)) := by
    rwa [PrimeSpectrum.localization_away_comap_range S b]
  rw [← Set.mem_preimage, Submonoid.preimage_comap_regularLocus (.powers b)]
  have : IsDomain S :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hb)
  have hheight : Q.asIdeal.height ≤ 1 := by
    rw [← IsLocalization.map_under (.powers b) S Q.asIdeal, IsLocalization.height_map_of_disjoint
      (.powers b) (Q.asIdeal.under B) ((Ideal.disjoint_powers_iff_notMem_of_isPrime b).mpr hbP)]
    exact_mod_cast Ideal.height_le_ringKrullDim_of_isPrime.trans
      (Ring.krullDimLE_iff.mp ‹Ring.KrullDimLE 1 B›)
  have := IsLocalization.AtPrime.isPrincipalIdealRing_of_height_le_one hheight
    (Localization.AtPrime Q.asIdeal)
  have : IsDomain (Localization.AtPrime Q.asIdeal) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
  exact mem_regularLocus.mpr inferInstance

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

/-- **Regularity spreads out from a regular prime of height one.** Let `q` be a prime of height one
of a Noetherian ring `A` at which `A` is regular. Then there is `r ∉ q` such that `A` is regular at
every prime containing `q` and not containing `r` at which `A ⧸ q` is regular: near `q`, the
ideal `q` is generated by a single nonzerodivisor. -/
theorem exists_notMem_forall_comap_mem_regularLocus_of_height_eq_one {q : Ideal A} [q.IsPrime]
    (hq : q.height = 1) (hreg : IsRegularLocalRing (Localization.AtPrime q)) :
    ∃ r ∉ q, ∀ P : PrimeSpectrum (A ⧸ q), Ideal.Quotient.mk q r ∉ P.asIdeal →
      P ∈ regularLocus (A ⧸ q) → PrimeSpectrum.comap (Ideal.Quotient.mk q) P ∈ regularLocus A := by
  -- `A_q` is a discrete valuation ring, so `q A_q` is generated by a uniformizer.
  have : IsDiscreteValuationRing (Localization.AtPrime q) :=
    IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr <| by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
      norm_cast
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  -- Spread this out: `q A_r` is generated by a nonzerodivisor for some `r ∉ q`.
  obtain ⟨r, hrq, hr⟩ := q.exists_notMem_map_mem_spanSubmonoid_nonZeroDivisors_away
    (Localization.AtPrime q) q (Localization.AtPrime.map_eq_maximalIdeal.trans hϖ.maximalIdeal_eq)
    (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
  refine ⟨r, hrq, fun P hrP hP ↦ ?_⟩
  set Q := P.asIdeal.comap (Ideal.Quotient.mk q)
  have hle : Submonoid.powers r ≤ Q.primeCompl :=
    Submonoid.powers_le.mpr (by rwa [Ideal.mem_primeCompl_iff, Ideal.mem_comap])
  -- `A_Q` is a localization of `A_r`, hence flat over it, so `q A_Q` is generated by a
  -- nonzerodivisor too, which may be taken from `q`.
  let := IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away r)
    (Localization.AtPrime Q) _ _ hle
  have := IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away r)
    (Localization.AtPrime Q) _ _ hle
  have := IsLocalization.isLocalization_of_submonoid_le (Localization.Away r)
    (Localization.AtPrime Q) _ _ hle
  have : Module.Flat (Localization.Away r) (Localization.AtPrime Q) :=
    IsLocalization.flat _ (Q.primeCompl.map (algebraMap A (Localization.Away r)))
  have hQ : q.map (algebraMap A (Localization.AtPrime Q)) ∈
      Ideal.spanSubmonoid (nonZeroDivisors _) := by
    rw [IsScalarTower.algebraMap_eq A (Localization.Away r), ← Ideal.map_map]
    exact Ideal.map_mem_spanSubmonoid_nonZeroDivisors_of_flat (hr _)
      (RingHom.flat_algebraMap_iff.mpr ‹_›)
  obtain ⟨⟨s, _⟩, hs⟩ := (Ideal.mem_spanSubmonoid_iff _).mp hQ
  obtain ⟨t, -, ht⟩ := q.exists_mem_map_eq_span_singleton Q.primeCompl hs
  have : IsRegularLocalRing (Localization.AtPrime P.asIdeal) := mem_regularLocus.mp hP
  exact mem_regularLocus.mpr <|
    IsRegularLocalRing.localization_of_quotient_of_map_eq_span_singleton_of_mem_nonZeroDivisors ht
      (Ideal.mem_nonZeroDivisors_of_span_eq_of_mem_spanSubmonoid hQ ht.symm)

variable {π : A}

/-- The non-regular primes containing a minimal prime `q` of `(π)` are finitely many: they contain
`q` and a fixed element outside `q`. -/
private lemma finite_zeroLocus_sdiff_regularLocus_of_mem_minimalPrimes (hπ : π ∈ nonZeroDivisors A)
    [Ring.IsNagata (A ⧸ Ideal.span {π})] [Ring.KrullDimLE 1 (A ⧸ Ideal.span {π})] {q : Ideal A}
    [q.IsPrime] (hq : q ∈ (Ideal.span {π}).minimalPrimes)
    (hreg : IsRegularLocalRing (Localization.AtPrime q)) :
    (PrimeSpectrum.zeroLocus (q : Set A) \ regularLocus A).Finite := by
  have hle : Ideal.span {π} ≤ q := hq.1.2
  have hheight : q.height = 1 := Ideal.height_eq_one_of_mem_minimalPrimes_span_singleton hπ hq
  -- `A ⧸ q` is a Nagata domain of dimension at most one, regular on some `D(b)`.
  have : Ring.IsNagata (A ⧸ q) := (DoubleQuot.quotQuotEquivQuotOfLE hle).isNagata
  have : Ring.KrullDimLE 1 (A ⧸ q) := Ring.krullDimLE_iff.mpr <|
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)).trans
      (Ring.krullDimLE_iff.mp ‹_›)
  obtain ⟨b, hb0, hb⟩ := exists_ne_zero_basicOpen_subset_regularLocus (A ⧸ q)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨r, hrq, hr⟩ := exists_notMem_forall_comap_mem_regularLocus_of_height_eq_one hheight hreg
  have hrb : r * b ∉ q := fun h ↦ (‹q.IsPrime›.mem_or_mem h).elim hrq
    fun h' ↦ hb0 (Ideal.Quotient.eq_zero_iff_mem.mpr h')
  refine (q.finite_setOf_le_and_mem hrb).subset ?_
  rintro p ⟨hqp, hpreg⟩
  -- A non-regular prime containing `q` comes from a prime of `A ⧸ q`, and it contains `r * b`.
  obtain ⟨P, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk q)) := by
    rwa [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at hqp
  refine ⟨hqp, by_contra fun h ↦ hpreg (hr P (fun h' ↦ h (Ideal.mul_mem_right _ _ h')) (hb ?_))⟩
  exact (PrimeSpectrum.mem_basicOpen _ _).mpr fun h' ↦ h (Ideal.mul_mem_left _ _ h')

/-- **A one-dimensional special fibre has finitely many non-regular points.** Let `A` be a
Noetherian ring and `π` a nonzerodivisor of `A` such that `A ⧸ (π)` is a Nagata ring of dimension
at most one. If `A` is regular at every minimal prime of `(π)`, then only finitely many primes
containing `π` are not in the regular locus of `A`. -/
theorem finite_zeroLocus_sdiff_regularLocus (hπ : π ∈ nonZeroDivisors A)
    [Ring.IsNagata (A ⧸ Ideal.span {π})] [Ring.KrullDimLE 1 (A ⧸ Ideal.span {π})]
    (hreg : ∀ q : PrimeSpectrum A, q.asIdeal ∈ (Ideal.span {π}).minimalPrimes →
      q ∈ regularLocus A) :
    (PrimeSpectrum.zeroLocus {π} \ regularLocus A).Finite := by
  refine (((Ideal.span {π}).finite_minimalPrimes_of_isNoetherianRing A).biUnion fun q hq ↦
    have := hq.1.1
    finite_zeroLocus_sdiff_regularLocus_of_mem_minimalPrimes hπ hq
      (mem_regularLocus.mp (hreg ⟨q, hq.1.1⟩ hq))).subset ?_
  rintro p ⟨hπp, hp⟩
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr
    (Set.singleton_subset_iff.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp hπp)))
  exact Set.mem_biUnion hq ⟨(PrimeSpectrum.mem_zeroLocus _ _).mpr hqp, hp⟩

end TauCeti.Excellence
