/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Squarefree

/-!
# Products over finite sets of primes

Mathlib's `Nat.primeFactors_prod` recovers a finite set of primes from its product. This file
records the consequences: such a product is squarefree, the product map is injective on finite
sets of primes, and a finite set `s` of primes has exactly `(#s).choose m` distinct products of
`m`-element subsets.

## Main results

* `Nat.squarefree_prod_of_prime`: a product of distinct primes is squarefree.
* `Nat.injOn_prod_of_prime`: the product map is injective on finite sets of primes.
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

/-- The product map is injective on finite sets of primes. -/
theorem injOn_prod_of_prime :
    Set.InjOn (fun t : Finset ℕ ↦ ∏ p ∈ t, p) {t | ∀ p ∈ t, p.Prime} := by
  intro t ht u hu h
  rw [← primeFactors_prod ht, ← primeFactors_prod hu]
  exact congrArg primeFactors h

/-- A finite set `s` of primes has `(#s).choose m` distinct products of `m`-element subsets. -/
theorem card_image_prod_powersetCard (hs : ∀ p ∈ s, p.Prime) (m : ℕ) :
    #((s.powersetCard m).image fun t ↦ ∏ p ∈ t, p) = (#s).choose m := by
  rw [Finset.card_image_of_injOn, card_powersetCard]
  have hsub : (s.powersetCard m : Set (Finset ℕ)) ⊆ {t | ∀ p ∈ t, p.Prime} :=
    fun t ht p hp ↦ hs p ((mem_powersetCard.mp (mem_coe.mp ht)).1 hp)
  exact injOn_prod_of_prime.mono hsub

end Nat
