/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated

/-!
# Divisors of products of prime powers

In a commutative monoid with zero, for a left-regular prime `p`, the divisors of a prime power
`p ^ n` are associated to `p ^ i` for `i ≤ n`. This file extends that characterization first to
multiples `p ^ n * a` and then, by induction on a finite index set, to finite products
`∏ i ∈ s, p i ^ m i` of powers of left-regular primes. No unique factorization hypothesis or
global cancellation is required, and the prime factors `p i` need not be distinct.

## Main results

* `TauCeti.dvd_prime_pow_mul_iff`: `q ∣ p ^ n * a` if and only if `q` is associated to `p ^ i * b`
  for some `i ≤ n` and `b ∣ a`.
* `TauCeti.dvd_finsetProd_pow_iff_of_prime`: `q ∣ ∏ i ∈ s, p i ^ m i` for left-regular primes
  `p i` if and only if `q` is associated to `∏ i ∈ s, p i ^ k i` for some `k` with `k i ≤ m i` on
  `s`.
-/

public section

namespace TauCeti

variable {M : Type*} [CommMonoidWithZero M]

/-- For a left-regular prime `p` in a commutative monoid with zero, an element divides `p ^ n * a`
if and only if it is associated to `p ^ i * b` for some `i ≤ n` and `b ∣ a`. -/
theorem dvd_prime_pow_mul_iff {p a q : M} (hp : Prime p) (hreg : IsLeftRegular p) (n : ℕ) :
    q ∣ p ^ n * a ↔ ∃ i ≤ n, ∃ b, b ∣ a ∧ Associated q (p ^ i * b) := by
  refine ⟨fun h ↦ ?_,
    fun ⟨i, hi, b, hb, hq⟩ ↦ hq.dvd.trans (mul_dvd_mul (pow_dvd_pow p hi) hb)⟩
  induction n generalizing q with
  | zero =>
    exact ⟨0, le_rfl, q, by simpa using h, by simp⟩
  | succ n ih =>
    rw [pow_succ', mul_assoc] at h
    obtain ⟨c, hc⟩ := h
    rcases hp.dvd_or_dvd ⟨p ^ n * a, hc.symm⟩ with ⟨r, rfl⟩ | ⟨d, rfl⟩
    · have hr : r ∣ p ^ n * a := ⟨c, hreg (hc.trans (mul_assoc p r c))⟩
      obtain ⟨i, hi, b, hb, hr'⟩ := ih hr
      refine ⟨i + 1, Nat.succ_le_succ hi, b, hb, ?_⟩
      rw [pow_succ', mul_assoc]
      exact hr'.mul_left p
    · have hq' : q ∣ p ^ n * a := ⟨d, hreg (hc.trans (mul_left_comm q p d))⟩
      obtain ⟨i, hi, b, hb, hq⟩ := ih hq'
      exact ⟨i, hi.trans (Nat.le_succ n), b, hb, hq⟩

/-- In a commutative monoid with zero, an element divides a finite product of powers of
left-regular primes `∏ i ∈ s, p i ^ m i` if and only if it is associated to `∏ i ∈ s, p i ^ k i`
for some exponents `k i ≤ m i`. The primes `p i` need not be distinct. -/
theorem dvd_finsetProd_pow_iff_of_prime {ι : Type*} {s : Finset ι} {p : ι → M}
    (hp : ∀ i ∈ s, Prime (p i)) (hreg : ∀ i ∈ s, IsLeftRegular (p i)) (m : ι → ℕ) {q : M} :
    q ∣ ∏ i ∈ s, p i ^ m i ↔
      ∃ k : ι → ℕ, (∀ i ∈ s, k i ≤ m i) ∧ Associated q (∏ i ∈ s, p i ^ k i) := by
  refine ⟨fun h ↦ ?_, fun ⟨k, hk, hq⟩ ↦
    hq.dvd.trans (Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow (p i) (hk i hi))⟩
  classical
  induction s using Finset.cons_induction generalizing q with
  | empty =>
    exact ⟨0, by simp, associated_one_iff_isUnit.mpr (isUnit_of_dvd_one (by simpa using h))⟩
  | cons a s has ih =>
    rw [Finset.prod_cons] at h
    have ha : Prime (p a) := hp a (Finset.mem_cons_self a s)
    have hrega : IsLeftRegular (p a) := hreg a (Finset.mem_cons_self a s)
    have hs : ∀ i ∈ s, Prime (p i) := fun i hi ↦ hp i (Finset.mem_cons.mpr (Or.inr hi))
    have hregs : ∀ i ∈ s, IsLeftRegular (p i) := fun i hi ↦ hreg i (Finset.mem_cons.mpr (Or.inr hi))
    obtain ⟨j, hj, b, hb, hqb⟩ := (dvd_prime_pow_mul_iff ha hrega (m a)).mp h
    obtain ⟨k, hk, hbk⟩ := ih hs hregs hb
    refine ⟨Function.update k a j, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_cons.mp hi with rfl | his
      · simpa using hj
      · simpa [ne_of_mem_of_not_mem his has] using hk i his
    · rw [Finset.prod_cons, Function.update_self]
      have hprod : ∏ i ∈ s, p i ^ Function.update k a j i = ∏ i ∈ s, p i ^ k i :=
        Finset.prod_congr rfl fun i hi ↦ by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hi has)]
      rw [hprod]
      exact hqb.trans (hbk.mul_left _)

end TauCeti
