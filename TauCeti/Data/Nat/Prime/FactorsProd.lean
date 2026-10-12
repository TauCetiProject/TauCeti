/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.RingTheory.Int.Basic

/-!
# Products over a set of prime factors

A product of distinct primes taken from `n.primeFactors` is squarefree, divides `n`, and introduces
no prime that `n` does not already have; and it is coprime to any prime left out of the set. These
are the facts an induction over the primes of `n` spends at each step, when it peels one prime off
and recurses on the rest.

## Main results

* `TauCeti.squarefree_prod_and_coprime_of_subset_primeFactors`: the three facts above, for a subset
  of `n.primeFactors` and a prime outside it.
-/

public section

namespace TauCeti

/-- **A product of some of `n`'s prime factors is squarefree, coprime to any prime left out, and
introduces no new prime.** For `S ⊆ n.primeFactors` and a prime `p ∉ S`, the product `∏ q ∈ S, q`
is squarefree (the members are distinct primes), coprime to `p` (it is coprime to each member), and
its prime factors are again among `n`'s (it divides `n`). -/
theorem squarefree_prod_and_coprime_of_subset_primeFactors {n : ℕ} [NeZero n] {S : Finset ℕ}
    (hS : S ⊆ n.primeFactors) {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) :
    Squarefree (S.prod id) ∧ Nat.Coprime p (S.prod id) ∧
      (S.prod id).primeFactors ⊆ n.primeFactors := by
  have hprime : ∀ q ∈ S, q.Prime := fun q hq ↦ Nat.prime_of_mem_primeFactors (hS hq)
  refine ⟨?_, ?_, ?_⟩
  · refine Finset.squarefree_prod_of_pairwise_isCoprime (fun q₁ hq₁ q₂ hq₂ hne ↦ ?_)
      fun q hq ↦ (hprime q hq).squarefree
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hprime q₁ hq₁) (hprime q₂ hq₂)).mpr hne)
  · exact Nat.Coprime.prod_right fun q hq ↦
      (Nat.coprime_primes hp (hprime q hq)).mpr fun h ↦ hpS (h ▸ hq)
  · exact Nat.primeFactors_mono (Finset.prod_primes_dvd n (fun q hq ↦ (hprime q hq).prime)
      fun q hq ↦ Nat.dvd_of_mem_primeFactors (hS hq)) (NeZero.ne n)

end TauCeti
