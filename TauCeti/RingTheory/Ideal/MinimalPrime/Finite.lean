/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
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
  have hPp : P.IsPrime := hP.1.1
  -- The intersection of the other minimal primes is not contained in `P`.
  let s : Finset (Ideal A) := (hfin.sdiff (t := {P})).toFinset
  have hs : ¬ s.inf id ≤ P := by
    rw [hPp.inf_le']
    rintro ⟨Q, hQs, hQP⟩
    rw [Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_singleton_iff] at hQs
    exact hQs.2 (le_antisymm hQP (hP.2 hQs.1.1 hQP))
  obtain ⟨g, hg, hgP⟩ := IsConcreteLE.not_le_iff_exists.mp hs
  refine ⟨g, hgP, fun q hq hIq hgq ↦ ?_⟩
  -- Every prime `q` contains a minimal prime `Q`, and `g ∉ q` forces `Q = P`.
  obtain ⟨Q, hQ, hQq⟩ := Ideal.exists_minimalPrimes_le hIq
  by_cases hQP : Q = P
  · exact hQP ▸ hQq
  · have hQs : Q ∈ s := by
      rw [Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨hQ, hQP⟩
    exact absurd (hQq (Finset.inf_le (f := id) hQs hg)) hgq

/-- In a reduced ring with finitely many minimal primes, a prime ideal is minimal if and only if
it consists of zero divisors. -/
theorem mem_minimalPrimes_iff_disjoint_nonZeroDivisors {A : Type*} [CommRing A] [IsReduced A]
    (hfin : (minimalPrimes A).Finite) {p : Ideal A} [p.IsPrime] :
    p ∈ minimalPrimes A ↔ Disjoint (p : Set A) (nonZeroDivisors A) := by
  refine ⟨Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes, fun h ↦ ?_⟩
  -- Every zero divisor of the reduced ring `A` lies in a minimal prime.
  have hsub : (p : Set A) ⊆ ⋃ q ∈ minimalPrimes A, (q : Set A) := by
    intro x hx
    have hx' : x ∉ nonZeroDivisors A := Set.disjoint_left.mp h hx
    rw [mem_nonZeroDivisors_iff_right] at hx'
    push Not at hx'
    obtain ⟨y, hxy, hy⟩ := hx'
    rw [minimalPrimes, Ideal.iUnion_minimalPrimes, Ideal.radical_bot_of_isReduced]
    exact ⟨y, hy, by rw [mul_comm, hxy]; exact Ideal.zero_mem ⊥⟩
  obtain ⟨q, hq, hpq⟩ := (Ideal.subset_union_prime_finite hfin (f := id) 0 0
    fun q hq _ _ ↦ hq.isPrime).mp hsub
  rwa [le_antisymm hpq (hq.2 ⟨‹_›, bot_le⟩ hpq)]

end Ideal
