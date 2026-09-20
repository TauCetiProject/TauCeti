/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Products over a finite set of primes

In a unique factorization monoid whose only unit is `1`, the passage from a finite set `S` of
primes to the product `∏ p ∈ S, p` loses no information: the normalized factors of the product
are exactly the elements of `S`, distinct sets of primes have distinct products, and every
divisor of the product is the product of a subset of `S`.

These are the facts that turn a divisibility statement about a product of distinct primes into a
statement about subsets of the set of factors. The hypothesis on the units is what makes the
conclusions equalities rather than statements up to associates; the motivating example is the
monoid of nonzero ideals of a Dedekind domain.
-/

public section

namespace TauCeti

open UniqueFactorizationMonoid

variable {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
  [StrongNormalizationMonoid α] [Subsingleton αˣ] {S T : Finset α}

/-- The normalized factors of the product of a finite set of primes are that set. -/
theorem normalizedFactors_finset_prod_of_prime (hS : ∀ p ∈ S, Prime p) :
    normalizedFactors (∏ p ∈ S, p) = S.val := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  exact normalizedFactors_prod_of_prime (by simpa using hS)

/-- A finite set of primes is determined by its product. -/
theorem finset_prod_eq_iff_of_prime (hS : ∀ p ∈ S, Prime p) (hT : ∀ p ∈ T, Prime p) :
    ∏ p ∈ S, p = ∏ p ∈ T, p ↔ S = T := by
  refine ⟨fun h => Finset.val_inj.1 ?_, fun h => by rw [h]⟩
  rw [← normalizedFactors_finset_prod_of_prime hS, ← normalizedFactors_finset_prod_of_prime hT, h]

/-- Every divisor of a product of distinct primes is the product of a subset of them. -/
theorem exists_subset_finset_prod_eq_of_dvd [Nontrivial α] (hS : ∀ p ∈ S, Prime p) {a : α}
    (hdvd : a ∣ ∏ p ∈ S, p) : ∃ T ⊆ S, a = ∏ p ∈ T, p := by
  have hprod : ∏ p ∈ S, p ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hS p hp).ne_zero
  have hzero : a ≠ 0 := ne_zero_of_dvd_ne_zero hprod hdvd
  have hle : normalizedFactors a ≤ S.val := by
    rw [← normalizedFactors_finset_prod_of_prime hS]
    exact (dvd_iff_normalizedFactors_le_normalizedFactors hzero hprod).mp hdvd
  refine ⟨⟨normalizedFactors a, Multiset.nodup_of_le hle S.nodup⟩, Finset.val_le_iff.mp hle, ?_⟩
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  exact (associated_iff_eq.1 (prod_normalizedFactors hzero)).symm

end TauCeti
