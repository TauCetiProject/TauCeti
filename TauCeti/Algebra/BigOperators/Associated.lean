/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated

/-!
# Divisors of products of prime powers

In a cancellative commutative monoid with zero, the divisors of a product `∏ i ∈ s, p i ^ n i` of
powers of prime elements are, up to multiplication by units, the products `∏ i ∈ s, p i ^ k i` with
`k i ≤ n i`. Neither unique factorization nor pairwise non-associatedness of the primes `p i` is
needed: prime divisibility peels off one factor `p i` at a time.

## Main results

* `Prime.dvd_pow_mul_iff`: for a prime `p`, a divisor of `p ^ n * r` has the form `p ^ i * s` with
  `i ≤ n` and `s ∣ r`.
* `Finset.dvd_prod_pow_iff_of_prime`: the divisors of `∏ i ∈ s, p i ^ n i` for primes `p i` are
  the elements associated to `∏ i ∈ s, p i ^ k i` with `k i ≤ n i`.
* `Finset.dvd_prod_iff_of_prime`: the divisors of `∏ i ∈ s, p i` for primes `p i` are the elements
  associated to subproducts `∏ i ∈ t, p i` with `t ⊆ s`.
-/

public section

assert_not_exists Field

variable {ι M₀ : Type*} [CommMonoidWithZero M₀] [IsCancelMulZero M₀]

/-- For a prime `p` in a cancellative commutative monoid with zero, an element divides `p ^ n * r`
if and only if it is `p ^ i * s` for some `i ≤ n` and some divisor `s` of `r`. -/
theorem Prime.dvd_pow_mul_iff {p q r : M₀} (hp : Prime p) (n : ℕ) :
    q ∣ p ^ n * r ↔ ∃ i ≤ n, ∃ s, s ∣ r ∧ q = p ^ i * s := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    refine ⟨fun h ↦ ?_, fun ⟨i, hi, s, hs, hq⟩ ↦ hq ▸ mul_dvd_mul (pow_dvd_pow p hi) hs⟩
    rw [pow_succ', mul_assoc] at h
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with ⟨q', rfl⟩ | hno
    · rw [mul_dvd_mul_iff_left hp.ne_zero, ih] at h
      obtain ⟨i, hi, s, hs, rfl⟩ := h
      exact ⟨i + 1, Nat.succ_le_succ hi, s, hs, by rw [pow_succ', mul_assoc]⟩
    · obtain ⟨i, hi, s, hs, hq⟩ := ih.mp hno
      exact ⟨i, Nat.le_succ_of_le hi, s, hs, hq⟩

/-- In a cancellative commutative monoid with zero, an element divides a product of powers of prime
elements `∏ i ∈ s, p i ^ n i` if and only if it is associated to `∏ i ∈ s, p i ^ k i` for some
exponents `k i ≤ n i`. The primes `p i` need not be pairwise non-associated. -/
theorem Finset.dvd_prod_pow_iff_of_prime {s : Finset ι} {p : ι → M₀} {n : ι → ℕ} {q : M₀}
    (hp : ∀ i ∈ s, Prime (p i)) :
    q ∣ ∏ i ∈ s, p i ^ n i ↔
      ∃ k : ι → ℕ, (∀ i ∈ s, k i ≤ n i) ∧ Associated q (∏ i ∈ s, p i ^ k i) := by
  refine ⟨fun h ↦ ?_, fun ⟨k, hk, hassoc⟩ ↦
    hassoc.dvd.trans (Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow (p i) (hk i hi))⟩
  classical
  induction s using Finset.induction generalizing q with
  | empty =>
    exact ⟨0, by simp, associated_one_iff_isUnit.mpr (isUnit_iff_dvd_one.mpr (by simpa using h))⟩
  | insert j s hjs ih =>
    rw [Finset.prod_insert hjs] at h
    obtain ⟨m, hm, r, hr, rfl⟩ :=
      ((hp j (Finset.mem_insert_self j s)).dvd_pow_mul_iff (n j)).mp h
    obtain ⟨k, hk, hassoc⟩ := (ih fun i hi ↦ hp i (Finset.mem_insert_of_mem hi)) hr
    refine ⟨Function.update k j m, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa using hm
      · simpa [ne_of_mem_of_not_mem hi hjs] using hk i hi
    · rw [Finset.prod_insert hjs, Function.update_self,
        Finset.prod_congr rfl fun i hi ↦ by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hjs)]]
      exact hassoc.mul_left (p j ^ m)

/-- In a cancellative commutative monoid with zero, an element divides a finite product of prime
elements `∏ i ∈ s, p i` if and only if it is associated to a subproduct `∏ i ∈ t, p i` with
`t ⊆ s`. -/
theorem Finset.dvd_prod_iff_of_prime {s : Finset ι} {p : ι → M₀} {q : M₀}
    (hp : ∀ i ∈ s, Prime (p i)) :
    q ∣ ∏ i ∈ s, p i ↔ ∃ t ⊆ s, Associated q (∏ i ∈ t, p i) := by
  refine ⟨fun h ↦ ?_, fun ⟨t, hts, hq⟩ ↦ hq.dvd.trans (Finset.prod_dvd_prod_of_subset t s p hts)⟩
  classical
  obtain ⟨k, hk, hassoc⟩ :=
    (Finset.dvd_prod_pow_iff_of_prime (n := fun _ ↦ 1) hp).mp (by simpa using h)
  refine ⟨{i ∈ s | k i = 1}, Finset.filter_subset _ _, hassoc.trans (Associated.of_eq ?_)⟩
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun i ↦ k i = 1)]
  have h1 : ∏ i ∈ s with k i = 1, p i ^ k i = ∏ i ∈ s with k i = 1, p i :=
    Finset.prod_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.mp hi).2, pow_one]
  have h0 : ∏ i ∈ s with ¬k i = 1, p i ^ k i = 1 :=
    Finset.prod_eq_one fun i hi ↦ by
      obtain ⟨his, hne⟩ := Finset.mem_filter.mp hi
      have hki : k i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ
        (lt_of_le_of_ne (hk i his) hne))
      rw [hki, pow_zero]
  rw [h1, h0, mul_one]
