/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated

/-!
# Divisors of products of prime powers

Mathlib's `dvd_prime_pow` characterizes the divisors of a single prime power `p ^ n` in a
cancellative commutative monoid with zero as the elements associated to `p ^ i` for `i ≤ n`.
To induct over several primes one needs the version with a cofactor (`Prime.dvd_pow_mul_iff`):
every divisor of `p ^ n * b` splits as `p ^ i * r` with `i ≤ n` and `r ∣ b`. Iterating over a
finite family gives `TauCeti.dvd_prod_prime_pow`, which characterizes the divisors of
`∏ i ∈ s, p i ^ n i` up to associates without assuming unique factorization or pairwise
non-associated primes, and `TauCeti.dvd_prod_prime` for a product of primes with unit exponents.

## Main results

* `Prime.dvd_pow_mul_iff`: `q ∣ p ^ n * b` if and only if `q = p ^ i * r` for some `i ≤ n` and
  `r ∣ b`.
* `TauCeti.dvd_prod_prime_pow`: the divisors of `∏ i ∈ s, p i ^ n i`, for primes `p i`, are up to
  associates the subproducts `∏ i ∈ s, p i ^ k i` with `k i ≤ n i`.
* `TauCeti.dvd_prod_prime`: the divisors of `∏ i ∈ s, p i`, for primes `p i`, are up to associates
  the subproducts over subsets `t ⊆ s`.
-/

public section

assert_not_exists Field

section Prime

variable {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]

/-- In a cancellative commutative monoid with zero, a divisor of `p ^ n * b`, with `p` prime,
factors as `p ^ i * r` with `i ≤ n` and `r ∣ b`. -/
theorem Prime.dvd_pow_mul_iff {p q b : M} (hp : Prime p) (n : ℕ) :
    q ∣ p ^ n * b ↔ ∃ i ≤ n, ∃ r, q = p ^ i * r ∧ r ∣ b := by
  induction n generalizing q with
  | zero =>
    refine ⟨fun h ↦ ⟨0, le_rfl, q, by simp, by simpa using h⟩, ?_⟩
    rintro ⟨i, hi, r, rfl, hr⟩
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    simpa using hr
  | succ n ih =>
    refine ⟨fun h ↦ ?_, ?_⟩
    · rw [pow_succ', mul_assoc] at h
      rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with ⟨q', rfl⟩ | h'
      · obtain ⟨i, hi, r, rfl, hr⟩ := ih.mp ((mul_dvd_mul_iff_left hp.ne_zero).mp h)
        exact ⟨i + 1, Nat.succ_le_succ hi, r, by rw [pow_succ', mul_assoc], hr⟩
      · obtain ⟨i, hi, r, rfl, hr⟩ := ih.mp h'
        exact ⟨i, Nat.le_succ_of_le hi, r, rfl, hr⟩
    · rintro ⟨i, hi, r, rfl, hr⟩
      exact mul_dvd_mul (pow_dvd_pow p hi) hr

end Prime

namespace TauCeti

variable {ι M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]

/-- **Divisors of a product of prime powers.** In a cancellative commutative monoid with zero, an
element divides `∏ i ∈ s, p i ^ n i`, where each `p i` (`i ∈ s`) is prime, if and only if it is
associated to `∏ i ∈ s, p i ^ k i` for some exponents `k i ≤ n i`. Neither unique factorization nor
pairwise non-association of the `p i` is needed. -/
theorem dvd_prod_prime_pow {s : Finset ι} {p : ι → M} (hp : ∀ i ∈ s, Prime (p i)) (n : ι → ℕ)
    {q : M} :
    q ∣ ∏ i ∈ s, p i ^ n i ↔
      ∃ k : ι → ℕ, (∀ i ∈ s, k i ≤ n i) ∧ Associated q (∏ i ∈ s, p i ^ k i) := by
  refine ⟨fun hdvd ↦ ?_, fun ⟨k, hk, hq⟩ ↦
    hq.dvd.trans (Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow (p i) (hk i hi))⟩
  classical
  induction s using Finset.cons_induction generalizing q with
  | empty =>
    exact ⟨0, by simp,
      by simpa [associated_one_iff_isUnit] using isUnit_of_dvd_one (by simpa using hdvd)⟩
  | cons j t hj ih =>
    have hpj : Prime (p j) := hp j (Finset.mem_cons_self j t)
    have hpt : ∀ i ∈ t, Prime (p i) := fun i hi ↦ hp i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons] at hdvd
    obtain ⟨m, hm, r, rfl, hr⟩ := (hpj.dvd_pow_mul_iff (n j)).mp hdvd
    obtain ⟨k, hk, hassoc⟩ := ih hpt hr
    refine ⟨Function.update k j m, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_cons.mp hi with rfl | hit
      · simpa using hm
      · have hij : i ≠ j := fun h ↦ hj (h ▸ hit)
        simpa [hij] using hk i hit
    · have ht_eq : ∏ i ∈ t, p i ^ Function.update k j m i = ∏ i ∈ t, p i ^ k i :=
        Finset.prod_congr rfl fun i hi ↦ by
          rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
      rw [Finset.prod_cons, Function.update_self, ht_eq]
      exact hassoc.mul_left (p j ^ m)

/-- **Divisors of a product of primes.** In a cancellative commutative monoid with zero, an element
divides `∏ i ∈ s, p i`, where each `p i` (`i ∈ s`) is prime, if and only if it is associated to
`∏ i ∈ t, p i` for some subset `t ⊆ s`. Unlike `TauCeti.dvd_finset_prod_iff_of_prime`, this holds
without `[Subsingleton Mˣ]` and allows associated factors among the `p i`. -/
theorem dvd_prod_prime {s : Finset ι} {p : ι → M} (hp : ∀ i ∈ s, Prime (p i)) {q : M} :
    q ∣ ∏ i ∈ s, p i ↔ ∃ t ⊆ s, Associated q (∏ i ∈ t, p i) := by
  classical
  refine ⟨fun hdvd ↦ ?_, fun ⟨t, hts, hq⟩ ↦ hq.dvd.trans (Finset.prod_dvd_prod_of_subset t s p hts)⟩
  have hdvd' : q ∣ ∏ i ∈ s, p i ^ (1 : ι → ℕ) i := by simpa using hdvd
  obtain ⟨k, hk, hq⟩ := (dvd_prod_prime_pow hp 1).mp hdvd'
  refine ⟨s.filter fun i ↦ k i = 1, Finset.filter_subset _ s, hq.trans (Associated.of_eq ?_)⟩
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hk i hi) with h | h <;> simp [h]

end TauCeti
