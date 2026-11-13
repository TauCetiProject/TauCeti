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
