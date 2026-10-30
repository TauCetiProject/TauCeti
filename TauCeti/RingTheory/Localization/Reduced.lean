/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Localizations and total quotient rings of reduced rings

Every localization of a reduced ring is reduced (`IsLocalization.isReduced`).

In a reduced ring every zero divisor lies in a minimal prime, and a Noetherian ring has only
finitely many minimal primes. By prime avoidance, a prime ideal of a reduced Noetherian ring
consists of zero divisors exactly when it is minimal
(`Ideal.mem_minimalPrimes_iff_disjoint_nonZeroDivisors`).

Consequently the total quotient ring `K` of a reduced Noetherian ring `A` has Krull dimension
zero. Being Noetherian too, `K` is Artinian (`IsFractionRing.isArtinianRing_of_isReduced`), and
it is reduced. Mathlib's `IsArtinianRing.equivPi` then decomposes
`K` as the finite product of its residue fields `K ⧸ m` over its maximal ideals `m`. When every
positive integer is a non-zero-divisor of `A`, these residue fields have characteristic zero
(`IsFractionRing.charZero_quotient`).

## References

* The Stacks Project, Algebra, section *Zerodivisors and total rings of fractions*.
-/

public section

open scoped nonZeroDivisors

variable {A : Type*} [CommRing A]

/-- Every localization of a reduced ring is reduced. -/
theorem IsLocalization.isReduced [IsReduced A] (M : Submonoid A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization M S] : IsReduced S :=
  let e := IsLocalization.algEquiv M S (Localization M)
  isReduced_of_injective e e.injective

/-- In a reduced Noetherian ring, a prime ideal is minimal if and only if it consists of zero
divisors. -/
theorem Ideal.mem_minimalPrimes_iff_disjoint_nonZeroDivisors [IsNoetherianRing A] [IsReduced A]
    {p : Ideal A} [p.IsPrime] :
    p ∈ minimalPrimes A ↔ Disjoint (p : Set A) A⁰ := by
  refine ⟨Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes, fun h ↦ ?_⟩
  -- Every zero divisor of the reduced ring `A` lies in a minimal prime.
  have hsub : (p : Set A) ⊆ ⋃ q ∈ minimalPrimes A, (q : Set A) := by
    intro x hx
    have hx' : x ∉ A⁰ := Set.disjoint_left.mp h hx
    rw [mem_nonZeroDivisors_iff_right] at hx'
    push Not at hx'
    obtain ⟨y, hxy, hy⟩ := hx'
    rw [minimalPrimes, Ideal.iUnion_minimalPrimes, Ideal.radical_bot_of_isReduced]
    exact ⟨y, hy, by rw [mul_comm, hxy]; exact Ideal.zero_mem ⊥⟩
  obtain ⟨q, hq, hpq⟩ := (Ideal.subset_union_prime_finite
    (minimalPrimes.finite_of_isNoetherianRing A) (f := id) 0 0
    fun q hq _ _ ↦ hq.isPrime).mp hsub
  rwa [le_antisymm hpq (hq.2 ⟨‹_›, bot_le⟩ hpq)]

namespace IsFractionRing

variable (A) (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K]

/-- The total quotient ring of a reduced Noetherian ring is Artinian. -/
theorem isArtinianRing_of_isReduced [IsNoetherianRing A] [IsReduced A] : IsArtinianRing K := by
  have : IsNoetherianRing K := IsLocalization.isNoetherianRing A⁰ K inferInstance
  refine isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, ?_⟩
  -- Every prime of `K` contracts to a minimal prime of `A`, so every prime of `K` is minimal.
  have hmin (P : Ideal K) [P.IsPrime] : P ∈ minimalPrimes K := by
    have hP : P.comap (algebraMap A K) ∈ minimalPrimes A :=
      Ideal.mem_minimalPrimes_iff_disjoint_nonZeroDivisors.mpr
        ((IsLocalization.isPrime_iff_isPrime_disjoint A⁰ K P).mp ‹_›).2.symm
    have h := IsLocalization.minimalPrimes_map A⁰ K (⊥ : Ideal A)
    rw [Ideal.map_bot] at h
    exact (Set.ext_iff.mp h P).mpr hP
  refine Ring.KrullDimLE.mk₀ fun P hP ↦ ?_
  obtain ⟨M, hM, hPM⟩ := P.exists_le_maximal hP.ne_top
  rwa [le_antisymm hPM ((hmin M).2 ⟨hP, bot_le⟩ hPM)]

/-- If every positive integer is a non-zero-divisor of `A`, then every quotient of the total
quotient ring of `A` by a proper ideal has characteristic zero. -/
theorem charZero_quotient (h : ∀ n : ℕ, n ≠ 0 → (n : A) ∈ A⁰) {I : Ideal K} (hI : I ≠ ⊤) :
    CharZero (K ⧸ I) := by
  refine charZero_of_inj_zero fun n hn ↦ ?_
  by_contra h0
  have hu : IsUnit (n : K) := by
    simpa using IsLocalization.map_units K ⟨(n : A), h n h0⟩
  have := Ideal.Quotient.nontrivial_iff.mpr hI
  exact (hu.map (Ideal.Quotient.mk I)).ne_zero (by simpa using hn)

end IsFractionRing
