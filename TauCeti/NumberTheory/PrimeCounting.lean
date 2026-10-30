/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.PrimeCounting
import TauCeti.Order.Filter.AtTopBot

/-!
# Partial products over primes along cofinal cutoffs

The primes `p ≤ n` are exactly the first `π n` primes `nth Nat.Prime 0, …, nth Nat.Prime (π n - 1)`,
so a finite product `∏ p ∈ primesLE n, f p` is the product of `f` over the first `π n` primes.
Since the prime counting function `π` tends to infinity and never increases by more than one at a
time, the ordered products over the primes `p ≤ n` converge exactly when the products over the
first `k` primes do.

The same comparison applies to any sequence of cutoffs `B k` tending to infinity such that,
eventually, each interval `(B k, B (k + 1)]` contains at most one prime: the products over the
primes `p ≤ B k` converge exactly when the products over the primes `p ≤ n` do. The cutoffs
`B k = nth Nat.Prime k`, the increasing enumeration of the primes, are the basic example. Along
an arbitrary sequence of cutoffs tending to infinity only the forward implication holds, and it
is `Filter.Tendsto.comp`; real cutoffs `x ↦ ∏ p ∈ primesLE ⌊x⌋₊, f p` are handled by
`TauCeti.tendsto_comp_natFloor_iff`.

These comparisons concern conditionally convergent products such as Euler products at the edge
of their half-plane of absolute convergence, where only ordered cutoffs make sense and different
orderings of the primes could give different limits. No topology on the values is needed.

## Main results

* `Nat.primesBelow_eq_image_nth`, `Nat.primesLE_eq_image_nth`: the primes below a bound are the
  first primes in increasing order.
* `Nat.prod_primesLE_eq_prod_range_nth`: a product over the primes `p ≤ n` is the product over
  the first `π n` primes.
* `Nat.tendsto_prod_primesLE_iff`: the ordered products over the primes `p ≤ n` converge exactly
  when the products over the first `k` primes do.
* `Nat.tendsto_prod_primesLE_comp_iff`: the same along cutoffs passing every prime one at a time.
* `Nat.tendsto_prod_primesLE_nth_iff`: the same along the cutoffs `nth Nat.Prime k`.
-/

public section

open Filter Finset

namespace Nat

/-- The primes below `n` are the first `π' n` primes. -/
theorem primesBelow_eq_image_nth (n : ℕ) :
    primesBelow n = (range (primeCounting' n)).image (nth Nat.Prime) := by
  ext p
  simp only [mem_primesBelow, mem_image, mem_range, primeCounting']
  refine ⟨fun ⟨hpn, hp⟩ ↦ ⟨count Nat.Prime p, count_strict_mono hp hpn, nth_count hp⟩, ?_⟩
  rintro ⟨k, hk, rfl⟩
  exact ⟨nth_lt_of_lt_count hk, prime_nth_prime k⟩

/-- The primes `p ≤ n` are the first `π n` primes. -/
theorem primesLE_eq_image_nth (n : ℕ) :
    primesLE n = (range (primeCounting n)).image (nth Nat.Prime) := by
  rw [primesLE, primeCounting_eq_primeCounting'_succ, primesBelow_eq_image_nth]

/-- A product over the primes `p ≤ n` is the product over the first `π n` primes. -/
@[to_additive /-- A sum over the primes `p ≤ n` is the sum over the first `π n` primes. -/]
theorem prod_primesLE_eq_prod_range_nth {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∏ p ∈ primesLE n, f p = ∏ k ∈ range (primeCounting n), f (nth Nat.Prime k) := by
  rw [primesLE_eq_image_nth,
    prod_image fun _ _ _ _ h ↦ nth_injective infinite_setOfPred_prime h]

/-- The prime counting function increases by at most one at each step. -/
theorem primeCounting_add_one_le (n : ℕ) : primeCounting (n + 1) ≤ primeCounting n + 1 := by
  rw [primeCounting_eq_primeCounting'_succ, primeCounting_eq_primeCounting'_succ, primeCounting',
    count_succ]
  split_ifs <;> omega

/-- The prime counting function at the `k`-th prime, counting from `nth Nat.Prime 0 = 2`,
is `k + 1`. -/
@[simp]
theorem primeCounting_nth_prime (k : ℕ) : primeCounting (nth Nat.Prime k) = k + 1 := by
  rw [primeCounting_eq_primeCounting'_succ, primeCounting',
    count_nth_succ_of_infinite infinite_setOfPred_prime]

variable {M : Type*} [CommMonoid M] {f : ℕ → M} {l : Filter M}

/-- The ordered products over the primes `p ≤ n` converge exactly when the products over the
first `k` primes do. -/
@[to_additive /-- The ordered sums over the primes `p ≤ n` converge exactly when the sums over the
first `k` primes do. -/]
theorem tendsto_prod_primesLE_iff :
    Tendsto (fun n ↦ ∏ p ∈ primesLE n, f p) atTop l ↔
      Tendsto (fun k ↦ ∏ i ∈ range k, f (nth Nat.Prime i)) atTop l := by
  simp_rw [prod_primesLE_eq_prod_range_nth]
  exact TauCeti.tendsto_comp_iff_of_le_add_one (u := fun k ↦ ∏ i ∈ range k, f (nth Nat.Prime i))
    tendsto_primeCounting (.of_forall primeCounting_add_one_le)

/-- Let the cutoffs `B k` tend to infinity, and eventually let each interval `(B k, B (k + 1)]`
contain at most one prime. Then the products over the primes `p ≤ B k` converge exactly when the
ordered products over the primes `p ≤ n` do. -/
@[to_additive /-- Let the cutoffs `B k` tend to infinity, and eventually let each interval
`(B k, B (k + 1)]` contain at most one prime. Then the sums over the primes `p ≤ B k` converge
exactly when the ordered sums over the primes `p ≤ n` do. -/]
theorem tendsto_prod_primesLE_comp_iff {B : ℕ → ℕ} (hB : Tendsto B atTop atTop)
    (hgap : ∀ᶠ k in atTop, primeCounting (B (k + 1)) ≤ primeCounting (B k) + 1) :
    Tendsto (fun k ↦ ∏ p ∈ primesLE (B k), f p) atTop l ↔
      Tendsto (fun n ↦ ∏ p ∈ primesLE n, f p) atTop l := by
  rw [tendsto_prod_primesLE_iff]
  simp_rw [prod_primesLE_eq_prod_range_nth]
  exact TauCeti.tendsto_comp_iff_of_le_add_one (g := fun k ↦ primeCounting (B k))
    (u := fun k ↦ ∏ i ∈ range k, f (nth Nat.Prime i)) (tendsto_primeCounting.comp hB) hgap

/-- The products over the primes up to the `k`-th prime converge exactly when the ordered
products over the primes `p ≤ n` do. -/
@[to_additive /-- The sums over the primes up to the `k`-th prime converge exactly when the
ordered sums over the primes `p ≤ n` do. -/]
theorem tendsto_prod_primesLE_nth_iff :
    Tendsto (fun k ↦ ∏ p ∈ primesLE (nth Nat.Prime k), f p) atTop l ↔
      Tendsto (fun n ↦ ∏ p ∈ primesLE n, f p) atTop l :=
  tendsto_prod_primesLE_comp_iff (nth_strictMono infinite_setOfPred_prime).tendsto_atTop
    (.of_forall fun k ↦ by simp)

end Nat
