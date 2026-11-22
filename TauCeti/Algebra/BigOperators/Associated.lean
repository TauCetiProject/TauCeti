/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import TauCeti.Algebra.GroupWithZero.Associated

/-!
# Divisors of products of prime elements

In a cancellative commutative monoid with zero, Mathlib's `dvd_prime_pow` characterizes the
divisors of `p ^ n` for a prime element `p` without assuming unique factorization, and Tau Ceti's
`Prime.exists_associated_pow_mul_of_dvd_pow_mul` (in `TauCeti.Algebra.GroupWithZero.Associated`)
extends that characterization to divisors of `p ^ n * a`.

This file extends that characterization to finite products of prime elements and their powers:
every divisor of `∏ i ∈ s, p i ^ n i` is associated to `∏ i ∈ s, p i ^ m i` with `m i ≤ n i`,
and when the primes `p i` are pairwise non-associated the exponents `m i` on `s` are uniquely
determined up to association of the product.

## Main results

* `Finset.dvd_prod_pow_primes_iff` and `Finset.dvd_prod_primes_pow_iff`: `x` divides
  `∏ i ∈ s, p i ^ n i` (or `(∏ i ∈ s, p i) ^ k`) if and only if `x` is associated to
  `∏ i ∈ s, p i ^ m i` with bounded exponents.
* `Finset.eq_of_associated_prod_pow_primes`: for pairwise non-associated primes on `s`, if
  `∏ i ∈ s, p i ^ m i` and `∏ i ∈ s, p i ^ n i` are associated, then `m i = n i` for every `i ∈ s`.
-/

public section

assert_not_exists Field

namespace Finset

variable {ι M₀ : Type*} [CommMonoidWithZero M₀] [IsCancelMulZero M₀]

/-- In a cancellative commutative monoid with zero, an element divides `∏ i ∈ s, p i ^ n i` for
prime elements `p i` (`i ∈ s`) if and only if it is associated to `∏ i ∈ s, p i ^ m i` for some
exponent function `m` bounded by `n` on `s`. -/
theorem dvd_prod_pow_primes_iff (s : Finset ι) {p : ι → M₀} (hp : ∀ i ∈ s, Prime (p i))
    (n : ι → ℕ) {x : M₀} :
    x ∣ ∏ i ∈ s, p i ^ n i ↔
      ∃ m : ι → ℕ, (∀ i ∈ s, m i ≤ n i) ∧ Associated x (∏ i ∈ s, p i ^ m i) := by
  classical
  refine ⟨fun hx ↦ ?_, fun ⟨m, hm, hxm⟩ ↦
    hxm.dvd.trans (Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow (p i) (hm i hi))⟩
  induction s using Finset.induction generalizing x with
  | empty =>
    rw [prod_empty, ← isUnit_iff_dvd_one, ← associated_one_iff_isUnit] at hx
    exact ⟨0, fun _ h ↦ absurd h (notMem_empty _), by simpa using hx⟩
  | insert a s ha ih =>
    have hpa : Prime (p a) := hp a (mem_insert_self a s)
    have hps : ∀ i ∈ s, Prime (p i) := fun i hi ↦ hp i (mem_insert_of_mem hi)
    rw [prod_insert ha] at hx
    obtain ⟨j, hj, y, hy, hxy⟩ := hpa.exists_associated_pow_mul_of_dvd_pow_mul hx
    obtain ⟨m, hm, hym⟩ := ih hps hy
    refine ⟨Function.update m a j, fun i hi ↦ ?_, ?_⟩
    · rcases mem_insert.mp hi with rfl | his
      · simpa using hj
      · simpa [ne_of_mem_of_not_mem his ha] using hm i his
    · rw [prod_insert ha, Function.update_self,
        prod_congr rfl fun i hi ↦ by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]]
      exact hxy.trans (hym.mul_left (p a ^ j))

/-- In a cancellative commutative monoid with zero, an element divides `(∏ i ∈ s, p i) ^ k` for
prime elements `p i` (`i ∈ s`) if and only if it is associated to `∏ i ∈ s, p i ^ m i` with
`m i ≤ k` for every `i ∈ s`. -/
theorem dvd_prod_primes_pow_iff (s : Finset ι) {p : ι → M₀} (hp : ∀ i ∈ s, Prime (p i))
    (k : ℕ) {x : M₀} :
    x ∣ (∏ i ∈ s, p i) ^ k ↔
      ∃ m : ι → ℕ, (∀ i ∈ s, m i ≤ k) ∧ Associated x (∏ i ∈ s, p i ^ m i) := by
  rw [← prod_pow]
  exact s.dvd_prod_pow_primes_iff hp fun _ ↦ k

/-- If `p i` (`i ∈ s`) are pairwise non-associated primes in a cancellative commutative monoid with
zero and `∏ i ∈ s, p i ^ m i` is associated to `∏ i ∈ s, p i ^ n i`, then `m i = n i` for every
`i ∈ s`. -/
theorem eq_of_associated_prod_pow_primes (s : Finset ι) {p : ι → M₀} (hp : ∀ i ∈ s, Prime (p i))
    (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j)) {m n : ι → ℕ}
    (h : Associated (∏ i ∈ s, p i ^ m i) (∏ i ∈ s, p i ^ n i)) ⦃i : ι⦄ (hi : i ∈ s) :
    m i = n i := by
  classical
  -- If `m i < n i`, cancelling `p i ^ m i` leaves a factor of `p i` dividing the remaining product
  -- on the left, forcing `p i` to divide `p j` for some `j ∈ s \ {i}`.
  have hle : ∀ {a b : ι → ℕ}, Associated (∏ j ∈ s, p j ^ a j) (∏ j ∈ s, p j ^ b j) →
      ∀ j ∈ s, a j ≤ b j := by
    intro a b hab j hj
    by_contra! hlt
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    have hpj : Prime (p j) := hp j hj
    have hpow : p j ^ a j = p j ^ b j * p j ^ (k + 1) := by rw [hk, add_assoc, pow_add]
    rw [← Finset.mul_prod_erase s (fun l ↦ p l ^ a l) hj,
      ← Finset.mul_prod_erase s (fun l ↦ p l ^ b l) hj, hpow, mul_assoc] at hab
    have hab' : Associated (p j ^ (k + 1) * ∏ l ∈ s.erase j, p l ^ a l)
        (∏ l ∈ s.erase j, p l ^ b l) :=
      Associated.of_mul_left hab Associated.rfl (pow_ne_zero (b j) hpj.ne_zero)
    have hdvd : p j ∣ ∏ l ∈ s.erase j, p l ^ b l :=
      (dvd_mul_of_dvd_left (dvd_pow_self (p j) (Nat.succ_ne_zero k)) _).trans hab'.dvd
    obtain ⟨l, hl, hpl⟩ := hpj.exists_mem_finset_dvd hdvd
    obtain ⟨hlne, hls⟩ := mem_erase.mp hl
    exact hs hj hls (Ne.symm hlne)
      (hpj.associated_of_dvd (hp l hls) (hpj.dvd_of_dvd_pow hpl))
  exact le_antisymm (hle h i hi) (hle h.symm i hi)

end Finset
