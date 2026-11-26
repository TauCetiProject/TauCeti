/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Nagata
public import TauCeti.RingTheory.RegularLocalRing.Locus

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
import TauCeti.RingTheory.Ideal.Maps
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
* `TauCeti.Excellence.exists_notMem_forall_mem_regularLocus_of_height_eq_one`: regularity at a
  prime `q` of height one spreads to the primes near `q` at which `A ⧸ q` is regular.
* `TauCeti.Excellence.finite_zeroLocus_diff_regularLocus`: only finitely many primes containing
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
  have hdisj : Disjoint (Submonoid.powers b : Set B) P.asIdeal :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime b).mpr hbP
  have hP := IsLocalization.isPrime_of_isPrime_disjoint (.powers b) S P.asIdeal P.isPrime hdisj
  -- `P` is the contraction of the prime `P S`, at which the integrally closed `S` is regular.
  have hcomap : PrimeSpectrum.comap (algebraMap B S) ⟨_, hP⟩ = P := PrimeSpectrum.ext <|
    IsLocalization.under_map_of_isPrime_disjoint (.powers b) S P.isPrime hdisj
  rw [← hcomap, ← Set.mem_preimage, Submonoid.preimage_comap_regularLocus (.powers b)]
  have : IsDomain S :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hb)
  have hheight : (P.asIdeal.map (algebraMap B S)).height ≤ 1 := by
    rw [IsLocalization.height_map_of_disjoint (.powers b) P.asIdeal hdisj]
    exact_mod_cast Ideal.height_le_ringKrullDim_of_isPrime.trans
      (Ring.krullDimLE_iff.mp ‹Ring.KrullDimLE 1 B›)
  have := IsLocalization.AtPrime.isPrincipalIdealRing_of_height_le_one hheight
    (Localization.AtPrime (P.asIdeal.map (algebraMap B S)))
  have : IsDomain (Localization.AtPrime (P.asIdeal.map (algebraMap B S))) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
  exact mem_regularLocus.mpr inferInstance

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

/-- **Regularity spreads out from a regular prime of height one.** Let `q` be a prime of height one
of a Noetherian ring `A` at which `A` is regular. Then there is `r ∉ q` such that `A` is regular at
every prime containing `q` and not containing `r` at which `A ⧸ q` is regular: near `q`, the
ideal `q` is generated by a single nonzerodivisor. -/
theorem exists_notMem_forall_mem_regularLocus_of_height_eq_one {q : Ideal A} [q.IsPrime]
    (hq : q.height = 1) (hreg : IsRegularLocalRing (Localization.AtPrime q)) :
    ∃ r ∉ q, ∀ P : PrimeSpectrum (A ⧸ q), Ideal.Quotient.mk q r ∉ P.asIdeal →
      P ∈ regularLocus (A ⧸ q) → PrimeSpectrum.comap (Ideal.Quotient.mk q) P ∈ regularLocus A := by
  -- `A_q` is a discrete valuation ring; choose `t ∈ q` whose image generates its maximal ideal.
  have : IsDiscreteValuationRing (Localization.AtPrime q) :=
    IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr <| by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
      norm_cast
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  obtain ⟨t, htq, ht⟩ := q.exists_mem_map_eq_span_singleton q.primeCompl
    (Localization.AtPrime.map_eq_maximalIdeal.trans hϖ.maximalIdeal_eq)
  have ht0 : algebraMap A (Localization.AtPrime q) t ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl, Localization.AtPrime.map_eq_maximalIdeal] at ht
    exact IsDiscreteValuationRing.not_a_field _ ht
  obtain ⟨r, hrq, hr, hann⟩ := Ideal.exists_notMem_smul_le_span_singleton_of_map_eq (P := q) _ ht
    (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ht0 : IsLeftRegular _).isSMulRegular
  refine ⟨r, hrq, fun P hrP hP ↦ ?_⟩
  have hrP' : r ∈ (P.asIdeal.comap (Ideal.Quotient.mk q)).primeCompl := by
    rwa [Ideal.mem_primeCompl_iff, Ideal.mem_comap]
  -- Near `q`, the ideal `q` is generated by `t`, which stays a nonzerodivisor.
  have hmap := Ideal.map_eq_span_singleton_of_isUnit
    (algebraMap A (Localization.AtPrime (P.asIdeal.comap (Ideal.Quotient.mk q)))) htq hr
    (IsLocalization.map_units _ ⟨r, hrP'⟩)
  have htreg : algebraMap A (Localization.AtPrime (P.asIdeal.comap (Ideal.Quotient.mk q))) t ∈
      nonZeroDivisors _ := by
    refine mem_nonZeroDivisors_iff_right.mpr fun z hz ↦ ?_
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
      (P.asIdeal.comap (Ideal.Quotient.mk q)).primeCompl z
    rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨⟨u, hu⟩, hut⟩ := hz
    -- `u a` is killed by `t`, hence by `r`, and `r u` is a unit near `q`.
    have hrua : r * u * a = 0 := by
      rw [mul_assoc]
      exact hann _ (by rw [← hut]; ring)
    exact (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨r * u, mul_mem hrP' hu⟩, hrua⟩
  have : IsRegularLocalRing (Localization.AtPrime P.asIdeal) := mem_regularLocus.mp hP
  exact mem_regularLocus.mpr
    (IsRegularLocalRing.localization_of_quotient_of_map_eq_span_singleton P.asIdeal hmap htreg)

variable {π : A}

/-- If `A ⧸ q` is a domain of dimension at most one, only finitely many primes contain both `q`
and a given element `f ∉ q`: they are maximal, hence minimal over `q + (f)`. -/
private lemma finite_setOf_le_and_mem {q : Ideal A} [q.IsPrime] [Ring.KrullDimLE 1 (A ⧸ q)]
    {f : A} (hf : f ∉ q) : {p : PrimeSpectrum A | q ≤ p.asIdeal ∧ f ∈ p.asIdeal}.Finite := by
  set J := q ⊔ Ideal.span {f}
  -- Every prime containing `J` is maximal, since it gives a nonzero prime of `A ⧸ q`.
  have hmax (p : Ideal A) [p.IsPrime] (hp : J ≤ p) : p.IsMaximal := by
    have hqp : q ≤ p := le_sup_left.trans hp
    have hP : (p.map (Ideal.Quotient.mk q)).IsPrime := Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    have hP0 : p.map (Ideal.Quotient.mk q) ≠ ⊥ := fun h ↦ hf <|
      Ideal.Quotient.eq_zero_iff_mem.mp <| Ideal.mem_bot.mp <|
        h ▸ Ideal.mem_map_of_mem _ (le_sup_right.trans hp (Ideal.mem_span_singleton_self _))
    have := Ideal.isMaximal_of_isPrime_of_ne_bot _ hP0
    simpa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, hqp] using
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
        (K := p.map (Ideal.Quotient.mk q))
  refine ((J.finite_minimalPrimes_of_isNoetherianRing A).preimage
    (fun _ _ _ _ h ↦ PrimeSpectrum.ext h : Set.InjOn PrimeSpectrum.asIdeal _)).subset ?_
  rintro p ⟨hqp, hfp⟩
  have hJp : J ≤ p.asIdeal := sup_le hqp ((Ideal.span_singleton_le_iff_mem _).mpr hfp)
  exact ⟨⟨p.isPrime, hJp⟩, fun p' ⟨_, hJp'⟩ hp'p ↦
    ((hmax p' hJp').eq_of_le p.isPrime.ne_top hp'p).ge⟩

/-- The non-regular primes containing a minimal prime `q` of `(π)` are finitely many: they contain
`q` and a fixed element outside `q`. -/
private lemma finite_zeroLocus_diff_regularLocus_of_mem_minimalPrimes (hπ : π ∈ nonZeroDivisors A)
    [Ring.IsNagata (A ⧸ Ideal.span {π})] [Ring.KrullDimLE 1 (A ⧸ Ideal.span {π})] {q : Ideal A}
    [q.IsPrime] (hq : q ∈ (Ideal.span {π}).minimalPrimes)
    (hreg : IsRegularLocalRing (Localization.AtPrime q)) :
    (PrimeSpectrum.zeroLocus (q : Set A) \ regularLocus A).Finite := by
  have hle : Ideal.span {π} ≤ q := hq.1.2
  -- `q` has height one: at most one by Krull's principal ideal theorem, and it is not a minimal
  -- prime of `A` since it contains the nonzerodivisor `π`.
  have hheight : q.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq)
      (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr fun h0 ↦ ?_))
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes
      (Ideal.height_eq_zero_iff.mp h0)) (hle (Ideal.mem_span_singleton_self π)) hπ
  -- `A ⧸ q` is a Nagata domain of dimension at most one, regular on some `D(b)`.
  have : Ring.IsNagata (A ⧸ q) := (DoubleQuot.quotQuotEquivQuotOfLE hle).isNagata
  have : Ring.KrullDimLE 1 (A ⧸ q) := Ring.krullDimLE_iff.mpr <|
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)).trans
      (Ring.krullDimLE_iff.mp ‹_›)
  obtain ⟨b, hb0, hb⟩ := exists_ne_zero_basicOpen_subset_regularLocus (A ⧸ q)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨r, hrq, hr⟩ := exists_notMem_forall_mem_regularLocus_of_height_eq_one hheight hreg
  have hrb : r * b ∉ q := fun h ↦ (‹q.IsPrime›.mem_or_mem h).elim hrq
    fun h' ↦ hb0 (Ideal.Quotient.eq_zero_iff_mem.mpr h')
  refine (finite_setOf_le_and_mem hrb).subset ?_
  rintro p ⟨hqp, hpreg⟩
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at hqp
  -- A non-regular prime containing `q` contains `r * b`.
  refine ⟨hqp, by_contra fun h ↦ ?_⟩
  let P : PrimeSpectrum (A ⧸ q) := ⟨p.asIdeal.map (Ideal.Quotient.mk q),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩
  have hPp : PrimeSpectrum.comap (Ideal.Quotient.mk q) P = p := PrimeSpectrum.ext <| by
    simp [P, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, hqp]
  have hmem (a : A) : Ideal.Quotient.mk q a ∈ P.asIdeal ↔ a ∈ p.asIdeal := by
    rw [← Ideal.mem_comap, ← PrimeSpectrum.comap_asIdeal, hPp]
  refine hpreg (hPp ▸ hr P (fun h' ↦ h (Ideal.mul_mem_right _ _ ((hmem r).mp h'))) (hb ?_))
  exact (PrimeSpectrum.mem_basicOpen _ _).mpr fun h' ↦
    h (Ideal.mul_mem_left _ _ ((hmem b).mp h'))

/-- **A one-dimensional special fibre has finitely many non-regular points.** Let `A` be a
Noetherian ring and `π` a nonzerodivisor of `A` such that `A ⧸ (π)` is a Nagata ring of dimension
at most one. If `A` is regular at every minimal prime of `(π)`, then only finitely many primes
containing `π` are not in the regular locus of `A`. -/
theorem finite_zeroLocus_diff_regularLocus (hπ : π ∈ nonZeroDivisors A)
    [Ring.IsNagata (A ⧸ Ideal.span {π})] [Ring.KrullDimLE 1 (A ⧸ Ideal.span {π})]
    (hreg : ∀ q : PrimeSpectrum A, q.asIdeal ∈ (Ideal.span {π}).minimalPrimes →
      q ∈ regularLocus A) :
    (PrimeSpectrum.zeroLocus {π} \ regularLocus A).Finite := by
  refine (((Ideal.span {π}).finite_minimalPrimes_of_isNoetherianRing A).biUnion fun q hq ↦
    have := hq.1.1
    finite_zeroLocus_diff_regularLocus_of_mem_minimalPrimes hπ hq
      (mem_regularLocus.mp (hreg ⟨q, hq.1.1⟩ hq))).subset ?_
  rintro p ⟨hπp, hp⟩
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr
    (Set.singleton_subset_iff.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp hπp)))
  exact Set.mem_biUnion hq ⟨(PrimeSpectrum.mem_zeroLocus _ _).mpr hqp, hp⟩

end TauCeti.Excellence
