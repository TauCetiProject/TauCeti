/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Squarefree

/-!
# Products over finite sets of primes

Mathlib's `Nat.primeFactors_prod` recovers a finite set of primes from its product, so the
product map is injective on finite sets of primes (`Nat.prod_primeFactors_invOn_squarefree`). This
file records consequences: such a product is squarefree, its squarefree divisors are the products
of subsets, two such products are coprime exactly when the sets are disjoint, and a finite set `s`
of primes has exactly `(#s).choose m` distinct products of `m`-element subsets.

## Main results

* `Nat.squarefree_prod_of_prime`: a product of distinct primes is squarefree.
* `Nat.dvd_prod_iff_primeFactors_subset`: a squarefree `d` divides `∏ p ∈ s, p` if and only if
  every prime factor of `d` lies in `s`.
* `Nat.Prime.dvd_prod_iff_mem`: a prime divides `∏ q ∈ s, q` if and only if it lies in `s`.
* `Nat.coprime_prod_prod_iff_disjoint`: the products of two finite sets of primes are coprime if
  and only if the sets are disjoint.
* `Nat.card_image_prod_powersetCard`: a finite set `s` of primes has `(#s).choose m` distinct
  products of `m`-element subsets.
-/

public section

open Finset

namespace Nat

variable {s : Finset ℕ}

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_of_prime (hs : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  have h := squarefree_prod_primeFactors (∏ p ∈ s, p)
  rwa [primeFactors_prod hs] at h

/-- A squarefree natural number divides a product of distinct primes if and only if all of its
prime factors are among them. -/
theorem dvd_prod_iff_primeFactors_subset (hs : ∀ p ∈ s, p.Prime) {d : ℕ} (hd : Squarefree d) :
    d ∣ ∏ p ∈ s, p ↔ d.primeFactors ⊆ s := by
  have h := prod_primeFactors_dvd_iff (n := d) (prod_ne_zero_iff.2 fun p hp ↦ (hs p hp).ne_zero)
  rwa [prod_primeFactors_of_squarefree hd, primeFactors_prod hs] at h

/-- A prime divides a product of distinct primes if and only if it is one of them. -/
theorem Prime.dvd_prod_iff_mem (hs : ∀ p ∈ s, p.Prime) {p : ℕ} (hp : p.Prime) :
    p ∣ ∏ q ∈ s, q ↔ p ∈ s := by
  rw [dvd_prod_iff_primeFactors_subset hs hp.prime.squarefree, hp.primeFactors,
    singleton_subset_iff]

/-- The products of two finite sets of primes are coprime if and only if the sets are
disjoint. -/
theorem coprime_prod_prod_iff_disjoint (hs : ∀ p ∈ s, p.Prime) {t : Finset ℕ}
    (ht : ∀ p ∈ t, p.Prime) : Coprime (∏ p ∈ s, p) (∏ p ∈ t, p) ↔ Disjoint s t := by
  rw [← disjoint_primeFactors (prod_ne_zero_iff.2 fun p hp ↦ (hs p hp).ne_zero)
    (prod_ne_zero_iff.2 fun p hp ↦ (ht p hp).ne_zero), primeFactors_prod hs, primeFactors_prod ht]

/-- A finite set `s` of primes has `(#s).choose m` distinct products of `m`-element subsets. -/
theorem card_image_prod_powersetCard (hs : ∀ p ∈ s, p.Prime) (m : ℕ) :
    #((s.powersetCard m).image fun t ↦ ∏ p ∈ t, p) = (#s).choose m := by
  rw [Finset.card_image_of_injOn, card_powersetCard]
  have hsub : (s.powersetCard m : Set (Finset ℕ)) ⊆ {t | ∀ p ∈ t, p.Prime} :=
    fun t ht p hp ↦ hs p ((mem_powersetCard.mp (mem_coe.mp ht)).1 hp)
  exact prod_primeFactors_invOn_squarefree.1.injOn.mono hsub

end Nat
