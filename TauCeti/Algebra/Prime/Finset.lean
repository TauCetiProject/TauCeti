/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Prime.Lemmas

/-!
# Divisors of finite products of prime powers

In a cancellative commutative monoid with zero, divisibility by a finite product of prime powers
is completely described without assuming unique factorization: every divisor of `∏ i ∈ s, p i ^ n i`
with each `p i` prime is associated to a subproduct `∏ i ∈ s, p i ^ k i` with `k i ≤ n i`.

## Main results

* `Prime.exists_eq_pow_mul_of_dvd_pow_mul`: a divisor of `p ^ n * b` splits as `p ^ k * q'` with
  `k ≤ n` and `q' ∣ b`.
* `TauCeti.dvd_finsetProd_prime_pow_iff`: `q ∣ ∏ i ∈ s, p i ^ n i` if and only if `q` is
  associated to `∏ i ∈ s, p i ^ k i` for some `k` with `k i ≤ n i` on `s`.
-/

public section

variable {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]

namespace Prime

/-- If `p` is prime and `q ∣ p ^ n * b`, then `q = p ^ k * q'` for some `k ≤ n` and `q' ∣ b`. -/
theorem exists_eq_pow_mul_of_dvd_pow_mul {p q b : M} (hp : Prime p) {n : ℕ}
    (h : q ∣ p ^ n * b) : ∃ k ≤ n, ∃ q', q' ∣ b ∧ q = p ^ k * q' := by
  induction n generalizing q with
  | zero => exact ⟨0, le_rfl, q, by simpa using h, by simp⟩
  | succ n ih =>
    rw [pow_succ', mul_assoc] at h
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with ⟨q₁, rfl⟩ | hno
    · rw [mul_dvd_mul_iff_left hp.ne_zero] at h
      obtain ⟨k, hk, q', hq', rfl⟩ := ih h
      exact ⟨k + 1, Nat.succ_le_succ hk, q', hq', by rw [pow_succ', mul_assoc]⟩
    · obtain ⟨k, hk, q', hq', rfl⟩ := ih hno
      exact ⟨k, Nat.le_succ_of_le hk, q', hq', rfl⟩

end Prime

namespace TauCeti

/-- **Divisors of a finite product of prime powers.** In a cancellative commutative monoid with
zero, an element divides `∏ i ∈ s, p i ^ n i` (with each `p i` prime) if and only if it is
associated to `∏ i ∈ s, p i ^ k i` for some exponents `k i ≤ n i`. -/
theorem dvd_finsetProd_prime_pow_iff {ι : Type*} {s : Finset ι} {p : ι → M}
    (hp : ∀ i ∈ s, Prime (p i)) (n : ι → ℕ) {q : M} :
    q ∣ ∏ i ∈ s, p i ^ n i ↔
      ∃ k : ι → ℕ, (∀ i ∈ s, k i ≤ n i) ∧ Associated q (∏ i ∈ s, p i ^ k i) := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨k, hk, hq⟩ ↦
    hq.dvd.trans (Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow _ (hk i hi))⟩
  induction s using Finset.induction generalizing q with
  | empty =>
    exact ⟨0, by simp, by simpa [associated_one_iff_isUnit, isUnit_iff_dvd_one] using h⟩
  | insert a s has ih =>
    rw [Finset.prod_insert has] at h
    obtain ⟨k₀, hk₀, q', hq', rfl⟩ :=
      (hp a (Finset.mem_insert_self a s)).exists_eq_pow_mul_of_dvd_pow_mul h
    obtain ⟨k, hk, hassoc⟩ := ih (fun i hi ↦ hp i (Finset.mem_insert_of_mem hi)) hq'
    refine ⟨Function.update k a k₀, fun i hi ↦ ?_, ?_⟩
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa using hk₀
      · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hi has)] using hk i hi
    · rw [Finset.prod_insert has, Function.update_self,
        Finset.prod_congr rfl fun i hi ↦ by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hi has)]]
      exact hassoc.mul_left _

end TauCeti
