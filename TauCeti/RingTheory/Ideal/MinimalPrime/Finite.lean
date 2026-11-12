/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Isolating a minimal prime among finitely many

Let `I` be an ideal in a commutative semiring with finitely many minimal primes over it. For a
minimal prime `P` over `I`, the intersection of the other minimal primes is not contained in `P`,
so it has an element `g ∉ P`. Every prime `q` over `I` not containing `g` contains some minimal
prime over `I`, which must be `P`. Geometrically, when `I = ⊥`, the basic open set `D(g)` of
`Spec A` is a nonempty open subset of the irreducible component `V(P)` meeting no other
irreducible component. This reduces statements about a single irreducible component to statements
about a localization `A[1/g]`.

In a reduced ring every zero divisor lies in a minimal prime. By prime avoidance, a prime ideal of
a reduced ring with finitely many minimal primes, such as a reduced Noetherian ring, consists of
zero divisors exactly when it is minimal.

## Main results

* `Ideal.exists_notMem_forall_le_of_mem_minimalPrimes`: for a minimal prime `P` over an ideal
  with finitely many minimal primes, there is `g ∉ P` such that every prime over that ideal not
  containing `g` contains `P`.
* `Ideal.mem_minimalPrimes_iff_disjoint_nonZeroDivisors`: in a reduced ring with finitely many
  minimal primes, a prime ideal is minimal if and only if it consists of zero divisors.
-/

public section

namespace Ideal

/-- Let `P` be a minimal prime over an ideal `I` with finitely many minimal primes. Then there is
an element `g ∉ P` such that every prime `q` over `I` with `g ∉ q` contains `P`. -/
theorem exists_notMem_forall_le_of_mem_minimalPrimes {A : Type*} [CommSemiring A] (I : Ideal A)
    (hfin : I.minimalPrimes.Finite) {P : Ideal A} (hP : P ∈ I.minimalPrimes) :
    ∃ g ∉ P, ∀ q : Ideal A, q.IsPrime → I ≤ q → g ∉ q → P ≤ q := by
  classical
  -- The intersection of the other minimal primes is not contained in `P`.
  obtain ⟨g, hg, hgP⟩ : ∃ g ∈ (hfin.toFinset.erase P).inf id, g ∉ P := by
    by_contra! hle
    obtain ⟨Q, hQ, hQP⟩ := hP.1.1.inf_le'.mp hle
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hQ
    exact hQ.1 (le_antisymm hQP (hP.2 hQ.2.1 hQP))
  refine ⟨g, hgP, fun q hq hIq hgq ↦ ?_⟩
  -- Every prime `q` contains a minimal prime `Q`, and `g ∉ q` forces `Q = P`.
  obtain ⟨Q, hQ, hQq⟩ := exists_minimalPrimes_le hIq
  obtain rfl | hQP := eq_or_ne Q P
  · exact hQq
  · have hQs : Q ∈ hfin.toFinset.erase P := by simpa using ⟨hQP, hQ⟩
    exact absurd (hQq (Finset.inf_le (f := id) hQs hg)) hgq

/-- In a reduced ring with finitely many minimal primes, a prime ideal is minimal if and only if
it consists of zero divisors. -/
theorem mem_minimalPrimes_iff_disjoint_nonZeroDivisors {A : Type*} [CommRing A] [IsReduced A]
    (hfin : (minimalPrimes A).Finite) {p : Ideal A} [p.IsPrime] :
    p ∈ minimalPrimes A ↔ Disjoint (p : Set A) (nonZeroDivisors A) := by
  refine ⟨disjoint_nonZeroDivisors_of_mem_minimalPrimes, fun h ↦ ?_⟩
  -- Every zero divisor of the reduced ring `A` lies in a minimal prime.
  have hsub : (p : Set A) ⊆ ⋃ q ∈ minimalPrimes A, (q : Set A) := fun x hx ↦ by
    obtain ⟨y, hyx, hy⟩ : ∃ y, y * x = 0 ∧ y ≠ 0 := by
      simpa [mem_nonZeroDivisors_iff_right] using Set.disjoint_left.mp h hx
    rw [minimalPrimes, iUnion_minimalPrimes, radical_bot_of_isReduced]
    exact ⟨y, hy, mem_bot.mpr <| by rw [mul_comm, hyx]⟩
  obtain ⟨q, hq, hpq⟩ := (subset_union_prime_finite hfin (f := id) 0 0
    fun q hq _ _ ↦ hq.isPrime).mp hsub
  rwa [le_antisymm hpq (hq.2 ⟨‹_›, bot_le⟩ hpq)]

/-- A finite intersection of principal prime ideals in a decomposition domain is generated
by a nonzero product of their generators. -/
theorem exists_ne_zero_finsetInf_eq_span_singleton
    {R : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R] (b : Finset (Ideal R))
    (h : ∀ P ∈ b, ∃ π : R, Prime π ∧ P = Ideal.span {π}) :
    ∃ a : R, a ≠ 0 ∧ b.inf id = Ideal.span {a} := by
  classical
  choose π hπ hgen using fun P : b ↦ h P P.2
  have hpair : Pairwise (fun P Q ↦ IsRelPrime (π P) (π Q)) := by
    intro P Q hPQ
    refine (hπ P).irreducible.isRelPrime_iff_not_dvd.mpr fun hdvd ↦ hPQ ?_
    apply Subtype.ext
    rw [hgen P, hgen Q]
    exact Ideal.span_singleton_eq_span_singleton.mpr
      ((hπ P).associated_of_dvd (hπ Q) hdvd)
  refine ⟨∏ P, π P, Finset.prod_ne_zero_iff.mpr (fun P _ ↦ (hπ P).ne_zero), ?_⟩
  ext x
  simp only [Submodule.mem_finsetInf, id_eq, Ideal.mem_span_singleton]
  constructor
  · intro hx
    exact Fintype.prod_dvd_of_isRelPrime hpair fun P ↦ by
      have := hx P P.2
      rwa [hgen P, Ideal.mem_span_singleton] at this
  · intro hx P hP
    rw [show P = _ from hgen ⟨P, hP⟩, Ideal.mem_span_singleton]
    exact (Finset.dvd_prod_of_mem π (Finset.mem_univ ⟨P, hP⟩)).trans hx

/-- A radical ideal of a Noetherian decomposition domain is generated by a nonzero element
if all its minimal primes are generated by prime elements. -/
theorem IsRadical.exists_ne_zero_eq_span_singleton
    {R : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I.IsRadical)
    (h : ∀ P ∈ I.minimalPrimes, ∃ π : R, Prime π ∧ P = Ideal.span {π}) :
    ∃ a : R, a ≠ 0 ∧ I = Ideal.span {a} := by
  have hfin := I.finite_minimalPrimes_of_isNoetherianRing
  obtain ⟨a, ha, hgen⟩ := exists_ne_zero_finsetInf_eq_span_singleton hfin.toFinset
    fun P hP ↦ h P (hfin.mem_toFinset.mp hP)
  refine ⟨a, ha, ?_⟩
  rw [← hgen, Finset.inf_id_eq_sInf, hfin.coe_toFinset, Ideal.sInf_minimalPrimes, hI.radical]

end Ideal
