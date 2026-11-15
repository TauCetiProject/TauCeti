/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated

/-!
# Divisors of finite products of primes

In a cancellative commutative monoid with zero, `dvd_prime_pow` characterizes the divisors of a
power `p ^ n` of a prime element `p`: an element `a` divides `p ^ n` if and only if it is
associated to `p ^ i` for some `i ≤ n`. Iterating the same cancellation step characterizes the
divisors of any finite product of prime elements, without assuming unique factorization or that the
prime factors are pairwise non-associated.

## Main results

* `Prime.dvd_pow_mul_iff`: for a prime element `p`, `a ∣ p ^ n * b` if and only if `a` is
  associated to `p ^ i * c` for some `i ≤ n` and some divisor `c` of `b`.
* `Multiset.dvd_prod_iff_of_prime`: the divisors of the product of a multiset `s` of primes are the
  elements associated to `t.prod` for a submultiset `t ≤ s`.
* `Finset.dvd_prod_iff_of_prime`: the divisors of `∏ i ∈ s, p i` for a family of primes `p` are
  the elements associated to `∏ i ∈ t, p i` for a subset `t ⊆ s`.
* `Finset.dvd_prod_pow_iff_of_prime` and `Finset.dvd_pow_prod_iff_of_prime`: the divisors of
  `∏ i ∈ s, p i ^ n i` (and in particular of `(∏ i ∈ s, p i) ^ n`) are the elements associated to
  `∏ i ∈ s, p i ^ k i` with `k i ≤ n i` for each `i ∈ s`.
-/

public section

variable {ι M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]

namespace Prime

/-- **Splitting a divisor across a prime power.** For a prime element `p`, an element `a` divides
`p ^ n * b` if and only if `a` is associated to `p ^ i * c` for some `i ≤ n` and some `c ∣ b`. -/
theorem dvd_pow_mul_iff {p a b : M} (hp : Prime p) (n : ℕ) :
    a ∣ p ^ n * b ↔ ∃ i ≤ n, ∃ c, c ∣ b ∧ Associated a (p ^ i * c) := by
  induction n generalizing a with
  | zero =>
    refine ⟨fun ha ↦ ⟨0, le_rfl, a, by simpa using ha, by simp⟩, ?_⟩
    rintro ⟨i, hi, c, hc, hac⟩
    obtain rfl := Nat.le_zero.mp hi
    exact hac.dvd.trans (by simpa using hc)
  | succ n ih =>
    refine ⟨fun ha ↦ ?_,
      fun ⟨i, hi, c, hc, hac⟩ ↦ hac.dvd.trans (mul_dvd_mul (pow_dvd_pow p hi) hc)⟩
    rw [pow_succ', mul_assoc] at ha
    -- Either `p` divides `a` and cancels from both sides, or `a` already divides `p ^ n * b`.
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul ha with ⟨a', rfl⟩ | ha'
    · rw [mul_dvd_mul_iff_left hp.ne_zero, ih] at ha
      obtain ⟨i, hi, c, hc, ha'c⟩ := ha
      refine ⟨i + 1, Nat.succ_le_succ hi, c, hc, (ha'c.mul_left p).trans ?_⟩
      rw [pow_succ', mul_assoc]
    · obtain ⟨i, hi, c, hc, hac⟩ := ih.mp ha'
      exact ⟨i, Nat.le_succ_of_le hi, c, hc, hac⟩

end Prime

namespace Multiset

/-- In a cancellative commutative monoid with zero, an element divides the product of a multiset
`s` of primes if and only if it is associated to the product of some submultiset `t ≤ s`. -/
theorem dvd_prod_iff_of_prime (s : Multiset M) (hs : ∀ p ∈ s, Prime p) {a : M} :
    a ∣ s.prod ↔ ∃ t ≤ s, Associated a t.prod := by
  refine ⟨?_, fun ⟨t, hts, hat⟩ ↦ hat.dvd.trans (prod_dvd_prod_of_le hts)⟩
  induction s using Multiset.induction_on generalizing a with
  | empty =>
    intro ha
    exact ⟨0, le_rfl, associated_one_iff_isUnit.mpr (isUnit_iff_dvd_one.mpr (by simpa using ha))⟩
  | cons p s ih =>
    intro ha
    have hp : Prime p := hs p (mem_cons_self p s)
    have hs' : ∀ q ∈ s, Prime q := fun q hq ↦ hs q (mem_cons_of_mem hq)
    rw [prod_cons] at ha
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul ha with ⟨a', rfl⟩ | ha'
    · rw [mul_dvd_mul_iff_left hp.ne_zero] at ha
      obtain ⟨t, hts, ha't⟩ := ih hs' ha
      exact ⟨p ::ₘ t, cons_le_cons p hts, by simpa using ha't.mul_left p⟩
    · obtain ⟨t, hts, hat⟩ := ih hs' ha'
      exact ⟨t, hts.trans (le_cons_self s p), hat⟩

end Multiset

namespace Finset

/-- In a cancellative commutative monoid with zero, an element divides a product `∏ i ∈ s, p i` of
primes if and only if it is associated to the subproduct over some subset `t ⊆ s`. -/
theorem dvd_prod_iff_of_prime (s : Finset ι) {p : ι → M} (hp : ∀ i ∈ s, Prime (p i)) {a : M} :
    a ∣ ∏ i ∈ s, p i ↔ ∃ t ⊆ s, Associated a (∏ i ∈ t, p i) := by
  refine ⟨?_, fun ⟨t, hts, hat⟩ ↦ hat.dvd.trans (prod_dvd_prod_of_subset t s p hts)⟩
  induction s using Finset.cons_induction generalizing a with
  | empty =>
    intro ha
    exact ⟨∅, empty_subset _,
      associated_one_iff_isUnit.mpr (isUnit_iff_dvd_one.mpr (by simpa using ha))⟩
  | cons j s hjs ih =>
    intro ha
    have hpj : Prime (p j) := hp j (mem_cons_self j s)
    have hps : ∀ i ∈ s, Prime (p i) := fun i hi ↦ hp i (mem_cons.mpr (.inr hi))
    rw [prod_cons] at ha
    rcases hpj.left_dvd_or_dvd_right_of_dvd_mul ha with ⟨a', rfl⟩ | ha'
    · rw [mul_dvd_mul_iff_left hpj.ne_zero] at ha
      obtain ⟨t, hts, ha't⟩ := ih hps ha
      have hjt : j ∉ t := fun hj ↦ hjs (hts hj)
      refine ⟨cons j t hjt, ?_, by simpa [prod_cons] using ha't.mul_left (p j)⟩
      intro y hy
      rcases mem_cons.mp hy with rfl | hy
      · exact mem_cons_self y s
      · exact mem_cons.mpr (.inr (hts hy))
    · obtain ⟨t, hts, hat⟩ := ih hps ha'
      exact ⟨t, fun y hy ↦ mem_cons.mpr (.inr (hts hy)), hat⟩

/-- In a cancellative commutative monoid with zero, an element divides a product
`∏ i ∈ s, p i ^ n i` of prime powers if and only if it is associated to `∏ i ∈ s, p i ^ k i` for
exponents `k i ≤ n i`. No pairwise non-associatedness of the `p i` is assumed. -/
theorem dvd_prod_pow_iff_of_prime (s : Finset ι) {p : ι → M} (hp : ∀ i ∈ s, Prime (p i))
    (n : ι → ℕ) {a : M} :
    a ∣ ∏ i ∈ s, p i ^ n i ↔
      ∃ k : ι → ℕ, (∀ i ∈ s, k i ≤ n i) ∧ Associated a (∏ i ∈ s, p i ^ k i) := by
  refine ⟨?_, fun ⟨k, hk, hak⟩ ↦
    hak.dvd.trans (prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow (p i) (hk i hi))⟩
  classical
  induction s using Finset.cons_induction generalizing a with
  | empty =>
    intro ha
    rw [prod_empty, ← isUnit_iff_dvd_one, ← associated_one_iff_isUnit] at ha
    exact ⟨0, by simp, by simpa using ha⟩
  | cons j s hjs ih =>
    intro ha
    have hpj : Prime (p j) := hp j (mem_cons_self j s)
    have hps : ∀ i ∈ s, Prime (p i) := fun i hi ↦ hp i (mem_cons.mpr (.inr hi))
    rw [prod_cons, hpj.dvd_pow_mul_iff] at ha
    obtain ⟨kj, hkj, c, hc, hac⟩ := ha
    obtain ⟨k, hk, hck⟩ := ih hps hc
    refine ⟨Function.update k j kj, ?_, hac.trans ?_⟩
    · intro i hi
      rcases mem_cons.mp hi with rfl | hi
      · simpa using hkj
      · rw [Function.update_of_ne (fun h : i = j ↦ hjs (h ▸ hi))]
        exact hk i hi
    · rw [prod_cons, Function.update_self,
        prod_congr rfl fun i hi ↦ congrArg (p i ^ ·)
          (Function.update_of_ne (fun h : i = j ↦ hjs (h ▸ hi)) kj k)]
      exact hck.mul_left (p j ^ kj)

/-- In a cancellative commutative monoid with zero, an element divides `(∏ i ∈ s, p i) ^ n` for a
family of primes `p` if and only if it is associated to `∏ i ∈ s, p i ^ k i` with `k i ≤ n` for
each `i ∈ s`. -/
theorem dvd_pow_prod_iff_of_prime (s : Finset ι) {p : ι → M} (hp : ∀ i ∈ s, Prime (p i)) (n : ℕ)
    {a : M} :
    a ∣ (∏ i ∈ s, p i) ^ n ↔
      ∃ k : ι → ℕ, (∀ i ∈ s, k i ≤ n) ∧ Associated a (∏ i ∈ s, p i ^ k i) := by
  rw [← prod_pow, s.dvd_prod_pow_iff_of_prime hp]

end Finset
