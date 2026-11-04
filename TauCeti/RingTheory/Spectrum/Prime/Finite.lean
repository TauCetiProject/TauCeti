/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Rings with finitely many prime ideals

A one-dimensional local domain, such as a discrete valuation ring, has exactly two prime ideals.
In a ring with finitely many prime ideals, the localization at a prime `p` is already a
localization away from a single element `f ∉ p`: take for `f` a product of elements, one from
each prime ideal not contained in `p`, chosen outside `p`.

This turns local statements into statements about a principal open neighbourhood. For an étale
algebra `E` over a discrete valuation ring, which has finitely many primes, the localization
`E[1/f]` is then a local étale algebra and, when its closed point lies over the closed point of
the base, a discrete valuation ring étale over the base.

## Main results

* `PrimeSpectrum.finite_of_krullDimLE_one`: a local domain of Krull dimension at most one has
  finitely many prime ideals.
* `PrimeSpectrum.exists_notMem_isLocalization_atPrime_away`: in a ring with finitely many prime
  ideals, the localization at a prime `p` is the localization away from some `f ∉ p`.
-/

public section

namespace PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- A local domain of Krull dimension at most one has finitely many prime ideals: its only
primes are `0` and the maximal ideal. -/
instance finite_of_krullDimLE_one [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R] :
    Finite (PrimeSpectrum R) := by
  refine Set.finite_univ_iff.mp ((Set.toFinite {⟨⊥, Ideal.isPrime_bot⟩,
    IsLocalRing.closedPoint R}).subset fun p _ ↦ ?_)
  rcases eq_or_ne p.asIdeal ⊥ with h | h
  · exact .inl (PrimeSpectrum.ext h)
  · exact .inr (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (p.isPrime.isMaximal_of_ne_bot h)))

/-- **Localizing at a prime of a ring with finitely many primes inverts a single element.** If
`R` has finitely many prime ideals, then for every prime `p` there is some `f ∉ p` such that
`R[1/f]` is the localization of `R` at `p`. In particular `R[1/f]` is a local ring whose maximal
ideal lies over `p`.

The proof adapts that of Mathlib's
`PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`. -/
theorem exists_notMem_isLocalization_atPrime_away [Finite (PrimeSpectrum R)]
    (p : PrimeSpectrum R) :
    ∃ f ∉ p.asIdeal, IsLocalization.AtPrime (Localization.Away f) p.asIdeal := by
  classical
  -- Choose, in every prime not contained in `p`, an element outside `p`.
  have : ∀ q : {q : PrimeSpectrum R // ¬q.asIdeal ≤ p.asIdeal}, ∃ a ∈ q.1.asIdeal, a ∉ p.asIdeal :=
    fun q ↦ Set.not_subset.mp q.2
  choose a ha hap using this
  have := Fintype.ofFinite {q : PrimeSpectrum R // ¬q.asIdeal ≤ p.asIdeal}
  have hf : ∏ q, a q ∉ p.asIdeal := by
    rw [Ideal.IsPrime.prod_mem_iff]
    simpa using hap
  refine ⟨∏ q, a q, hf, .of_le_of_exists_dvd (.powers _) _
    (Submonoid.powers_le.mpr hf) fun r hr ↦ ?_⟩
  -- If `r ∉ p` divided no power of `f`, some prime containing `r` would avoid `f`, so it would be
  -- contained in `p`.
  contrapose! hr
  simp_rw [← Ideal.mem_span_singleton] at hr
  obtain ⟨q, hq, hle, hdisj⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {r})
    (.powers (∏ q, a q)) (Set.disjoint_right.mpr hr)
  have hqp : q ≤ p.asIdeal := by
    by_contra h
    exact Set.disjoint_right.mp hdisj (Submonoid.mem_powers _)
      (Ideal.IsPrime.prod_mem_iff.mpr ⟨⟨⟨q, hq⟩, h⟩, Finset.mem_univ _, ha ⟨⟨q, hq⟩, h⟩⟩ :
        ∏ q, a q ∈ q)
  rw [Ideal.mem_primeCompl_iff, not_not]
  exact hqp (hle (Ideal.mem_span_singleton_self r))

end PrimeSpectrum
