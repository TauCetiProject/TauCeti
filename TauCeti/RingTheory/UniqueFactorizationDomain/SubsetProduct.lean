/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Radical.Basic
import Mathlib.Algebra.BigOperators.Associated

/-!
# Products over a finite set of primes

In a unique factorization monoid whose only unit is `1`, the passage from a finite set `S` of
primes to the product `∏ p ∈ S, p` loses no information: the normalized factors of the product
are exactly the elements of `S`, distinct sets of primes have distinct products, and the divisors
of the product are exactly the products of the subsets of `S`. The last two facts need only a
cancellative monoid with zero whose only unit is `1`, not unique factorization.

These are the facts that turn a divisibility statement about a product of distinct primes into a
statement about subsets of the set of factors. The hypothesis on the units is what makes the
conclusions equalities rather than statements up to associates; the motivating example is the
multiplicative monoid of ideals of a Dedekind domain.

For products of powers no hypothesis on the units is needed. The normalized factors of
`∏ p ∈ S, p ^ e p`, for a finite set `S` of normalized irreducible elements, are the `p ∈ S`, each
`e p` times (`TauCeti.normalizedFactors_finset_prod_pow`,
`TauCeti.count_normalizedFactors_finset_prod_pow`). Conversely, a nonzero normalized element is the
product of its normalized factors with their multiplicities, over any finite set that contains
them (`TauCeti.finset_prod_pow_count_normalizedFactors`).

Without the hypothesis on the units, the product of the prime factors of `a` satisfying an
associate-invariant predicate `s` is divisible by exactly the primes dividing `a` that satisfy
`s` (`prime_dvd_prod_filter_primeFactors_iff`). This is how one builds an element with
prescribed prime divisors among those of `a`.
-/

public section

namespace TauCeti

open UniqueFactorizationMonoid

variable {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α] [UniqueFactorizationMonoid α]

section UniqueUnits

variable [Subsingleton αˣ] {S T : Finset α}

/-- The normalized factors of the product of a finite set of primes are that set. -/
@[simp]
theorem normalizedFactors_finset_prod_of_prime (hS : ∀ p ∈ S, Prime p) :
    normalizedFactors (∏ p ∈ S, p) = S.val := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  exact normalizedFactors_prod_of_prime hS

end UniqueUnits

section ProdPow

variable {S : Finset α}

/-- The normalized factors of `∏ p ∈ S, p ^ e p`, for a finite set `S` of normalized irreducible
elements, are the `p ∈ S`, each `e p` times. -/
theorem normalizedFactors_finset_prod_pow (hS : ∀ p ∈ S, normalize p = p ∧ Irreducible p)
    (e : α → ℕ) : normalizedFactors (∏ p ∈ S, p ^ e p) = ∑ p ∈ S, e p • {p} := by
  have hprod : ∏ p ∈ S, p ^ e p = (∑ p ∈ S, e p • {p} : Multiset α).prod := by
    rw [Multiset.prod_sum]
    exact Finset.prod_congr rfl fun p _ ↦ by rw [Multiset.prod_nsmul, Multiset.prod_singleton]
  have hmem {q : α} (hq : q ∈ ∑ p ∈ S, e p • ({p} : Multiset α)) :
      normalize q = q ∧ Irreducible q := by
    obtain ⟨p, hp, hqp⟩ := Multiset.mem_sum.1 hq
    rw [Multiset.mem_nsmul] at hqp
    rw [Multiset.mem_singleton.1 hqp.2]
    exact hS p hp
  rw [hprod, normalizedFactors_prod_eq _ fun q hq ↦ (hmem hq).2,
    Multiset.map_congr rfl fun q hq ↦ (hmem hq).1, Multiset.map_id']

/-- In `∏ q ∈ S, q ^ e q`, for a finite set `S` of normalized irreducible elements, each `p ∈ S`
occurs `e p` times as a normalized factor. -/
theorem count_normalizedFactors_finset_prod_pow [DecidableEq α]
    (hS : ∀ p ∈ S, normalize p = p ∧ Irreducible p) (e : α → ℕ) {p : α} (hp : p ∈ S) :
    (normalizedFactors (∏ q ∈ S, q ^ e q)).count p = e p := by
  rw [normalizedFactors_finset_prod_pow hS, Multiset.count_sum', Finset.sum_eq_single p]
  · simp
  · intro q _ hqp
    simp [hqp.symm]
  · exact fun h ↦ (h hp).elim

end ProdPow

section StrongNormalization

variable {α : Type*} [CommMonoidWithZero α] [StrongNormalizationMonoid α]
  [UniqueFactorizationMonoid α] [DecidableEq α]

/-- A nonzero normalized element `a` whose normalized factors lie in a finite set `S` is
`∏ p ∈ S, p ^ m p`, where `m p` is the number of times that `p` occurs as a normalized factor. -/
theorem finset_prod_pow_count_normalizedFactors {a : α} (ha : a ≠ 0) (hna : normalize a = a)
    {S : Finset α} (hS : (normalizedFactors a).toFinset ⊆ S) :
    ∏ p ∈ S, p ^ (normalizedFactors a).count p = a := by
  rw [← Finset.prod_multiset_count_of_subset _ _ hS, prod_normalizedFactors_eq ha, hna]

end StrongNormalization

section UniqueUnitsCancel

variable {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α] [Subsingleton αˣ] {S T : Finset α}

/-- A finite set of primes is determined by its product. -/
@[simp]
theorem finset_prod_eq_iff_of_prime (hS : ∀ p ∈ S, Prime p) (hT : ∀ p ∈ T, Prime p) :
    ∏ p ∈ S, p = ∏ p ∈ T, p ↔ S = T := by
  refine ⟨fun h => Finset.val_inj.1 ?_, fun h => by rw [h]⟩
  have h' : S.val.prod = T.val.prod := by
    simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using h
  have := prime_factors_unique (f := S.val) (g := T.val) hS hT (Associated.of_eq h')
  rwa [associated_eq_eq, Multiset.rel_eq] at this

/-- The divisors of a product of distinct primes are exactly the products of subsets of them. -/
theorem dvd_finset_prod_iff_of_prime (hS : ∀ p ∈ S, Prime p) {a : α} :
    a ∣ ∏ p ∈ S, p ↔ ∃ T ⊆ S, a = ∏ p ∈ T, p := by
  refine ⟨fun hdvd => ?_, fun ⟨T, hTS, ha⟩ => ha ▸ Finset.prod_dvd_prod_of_subset T S _ hTS⟩
  induction S using Finset.cons_induction generalizing a with
  | empty =>
    exact ⟨∅, Finset.empty_subset _, isUnit_iff_eq_one.1 (isUnit_of_dvd_one (by simpa using hdvd))⟩
  | cons p S hpS ih =>
    have hp : Prime p := hS p (Finset.mem_cons_self p S)
    have hS' : ∀ q ∈ S, Prime q := fun q hq => hS q (Finset.mem_cons.2 (Or.inr hq))
    rw [Finset.prod_cons] at hdvd
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul hdvd with ⟨b, rfl⟩ | h
    · obtain ⟨T, hTS, hb⟩ := ih hS' ((mul_dvd_mul_iff_left hp.ne_zero).1 hdvd)
      exact ⟨Finset.cons p T (fun hp' => hpS (hTS hp')), Finset.cons_subset_cons.2 hTS, by
        rw [Finset.prod_cons, hb]⟩
    · obtain ⟨T, hTS, ha⟩ := ih hS' h
      exact ⟨T, hTS.trans (Finset.subset_cons hpS), ha⟩

end UniqueUnitsCancel

/-- A prime divides the product of the prime factors of `a ≠ 0` satisfying an
associate-invariant predicate `s` exactly when it divides `a` and satisfies `s`. -/
theorem prime_dvd_prod_filter_primeFactors_iff {a p : α} (ha : a ≠ 0) (hp : Prime p)
    (s : α → Prop) [DecidablePred s] (hs : ∀ {q r : α}, Associated q r → (s q ↔ s r)) :
    p ∣ ∏ q ∈ (primeFactors a).filter s, q ↔ p ∣ a ∧ s p := by
  rw [hp.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hpq⟩
    rw [Finset.mem_filter, mem_primeFactors] at hq
    exact ⟨hpq.trans (dvd_of_mem_normalizedFactors hq.1),
      (hs (hp.associated_of_dvd (prime_of_normalized_factor q hq.1) hpq)).mpr hq.2⟩
  · rintro ⟨hpa, hsp⟩
    obtain ⟨q, hq, hpq⟩ := exists_mem_normalizedFactors_of_dvd ha hp.irreducible hpa
    exact ⟨q, Finset.mem_filter.mpr ⟨mem_primeFactors.mpr hq, (hs hpq).mp hsp⟩, hpq.dvd⟩

end TauCeti
