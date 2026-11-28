/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated
import TauCeti.Algebra.Regular.Basic

/-!
# Products of primes and divisors of prime powers

In a commutative monoid with zero:
1. If each member of a finite family of primes divides `n`, and no member of the family divides
   another, then the product of the family divides `n`. Mathlib's `Finset.prod_primes_dvd` states
   this for a finset of primes in a cancellative monoid with trivial units, and
   `Multiset.prod_primes_dvd` for a multiset counted up to association; this is the form for an
   indexed family. For instance, in a polynomial ring over a domain the differences `X j - X i`
   of pairs of variables with `i < j` are such a family, and their product is the Vandermonde
   product.
2. For a left-regular prime `p`, the divisors of a prime power `p ^ n` are associated to `p ^ i`
   for `i ≤ n`. This file extends that characterization first to multiples `p ^ n * a` and then,
   by induction on a finite index set, to finite products `∏ i ∈ s, p i ^ m i` of powers of
   left-regular primes. No unique factorization hypothesis or global cancellation is required, and
   the prime factors `p i` need not be distinct.

## Main results

* `Finset.prod_primes_dvd_of_pairwise_not_dvd`: the product of a finite family of primes, each
  dividing `n` and none dividing another, divides `n`.
* `TauCeti.dvd_prime_pow_mul_iff`: `q ∣ p ^ n * a` if and only if `q` is associated to `p ^ i * b`
  for some `i ≤ n` and `b ∣ a`.
* `TauCeti.dvd_finsetProd_pow_mul_iff_of_prime`: `q ∣ (∏ i ∈ s, p i ^ m i) * r` for
  left-regular primes `p i` if and only if `q` is associated to `(∏ i ∈ s, p i ^ k i) * b` for
  some `k` with `k i ≤ m i` on `s` and `b ∣ r`.
* `TauCeti.dvd_finsetProd_pow_iff_of_prime`: `q ∣ ∏ i ∈ s, p i ^ m i` for left-regular primes
  `p i` if and only if `q` is associated to `∏ i ∈ s, p i ^ k i` for some `k` with `k i ≤ m i` on
  `s`.
* `TauCeti.exists_associated_finsetProd_pow_of_dvd_pow`: if `f` is left-regular and associated to
  `∏ i ∈ s, p i`, any divisor `a` of `f ^ n` is associated to `∏ i ∈ s, p i ^ k i` with `k i ≤ n`.
-/

public section

namespace Finset

variable {ι M : Type*} [CommMonoidWithZero M]

/-- The product of a finite family of primes, each of which divides `n` and none of which divides
another, divides `n`. -/
theorem prod_primes_dvd_of_pairwise_not_dvd {s : Finset ι} {f : ι → M} {n : M}
    (hprime : ∀ i ∈ s, Prime (f i)) (hndvd : (s : Set ι).Pairwise fun i j ↦ ¬ f i ∣ f j)
    (hdvd : ∀ i ∈ s, f i ∣ n) : ∏ i ∈ s, f i ∣ n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    obtain ⟨w, rfl⟩ := ih (fun i hi ↦ hprime i (mem_insert_of_mem hi))
      (hndvd.mono (by simp)) fun i hi ↦ hdvd i (mem_insert_of_mem hi)
    -- `f a` divides `(∏ i ∈ s, f i) * w` but none of the `f i`, so it divides `w`.
    have hpa := hprime a (mem_insert_self a s)
    have hnot : ¬ f a ∣ ∏ i ∈ s, f i := hpa.not_dvd_finsetProd fun i hi ↦
      hndvd (mem_insert_self a s) (mem_insert_of_mem hi) fun hai ↦ ha (hai ▸ hi)
    obtain ⟨v, rfl⟩ := (hpa.dvd_or_dvd (hdvd a (mem_insert_self a s))).resolve_left hnot
    exact ⟨v, by ac_rfl⟩

end Finset

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

/-- In a commutative monoid with zero, an element divides `(∏ i ∈ s, p i ^ m i) * r` for
left-regular primes `p i` if and only if it is associated to `(∏ i ∈ s, p i ^ k i) * b` for some
exponents `k i ≤ m i` and `b ∣ r`. The primes `p i` need not be distinct. -/
theorem dvd_finsetProd_pow_mul_iff_of_prime {ι : Type*} {s : Finset ι} {p : ι → M}
    (hp : ∀ i ∈ s, Prime (p i)) (hreg : ∀ i ∈ s, IsLeftRegular (p i)) (m : ι → ℕ) {r q : M} :
    q ∣ (∏ i ∈ s, p i ^ m i) * r ↔
      ∃ k : ι → ℕ, (∀ i ∈ s, k i ≤ m i) ∧ ∃ b, b ∣ r ∧ Associated q ((∏ i ∈ s, p i ^ k i) * b) := by
  refine ⟨fun h ↦ ?_, fun ⟨k, hk, b, hb, hq⟩ ↦
    hq.dvd.trans (mul_dvd_mul
      (Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow (p i) (hk i hi)) hb)⟩
  classical
  induction s using Finset.cons_induction generalizing q with
  | empty =>
    exact ⟨0, by simp, q, by simpa using h, by simp⟩
  | cons a s has ih =>
    rw [Finset.prod_cons, mul_assoc] at h
    have ha : Prime (p a) := hp a (Finset.mem_cons_self a s)
    have hrega : IsLeftRegular (p a) := hreg a (Finset.mem_cons_self a s)
    have hs : ∀ i ∈ s, Prime (p i) := fun i hi ↦ hp i (Finset.mem_cons.mpr (Or.inr hi))
    have hregs : ∀ i ∈ s, IsLeftRegular (p i) := fun i hi ↦
      hreg i (Finset.mem_cons.mpr (Or.inr hi))
    obtain ⟨j, hj, c, hc, hqc⟩ := (dvd_prime_pow_mul_iff ha hrega (m a)).mp h
    obtain ⟨k, hk, b, hb, hcb⟩ := ih hs hregs hc
    refine ⟨Function.update k a j, ?_, b, hb, ?_⟩
    · intro i hi
      rcases Finset.mem_cons.mp hi with rfl | his
      · simpa using hj
      · simpa [ne_of_mem_of_not_mem his has] using hk i his
    · rw [Finset.prod_cons, Function.update_self]
      have hprod : ∏ i ∈ s, p i ^ Function.update k a j i = ∏ i ∈ s, p i ^ k i :=
        Finset.prod_congr rfl fun i hi ↦ by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hi has)]
      rw [hprod, mul_assoc]
      exact hqc.trans (hcb.mul_left _)

/-- In a commutative monoid with zero, an element divides a finite product of powers of
left-regular primes `∏ i ∈ s, p i ^ m i` if and only if it is associated to `∏ i ∈ s, p i ^ k i`
for some exponents `k i ≤ m i`. The primes `p i` need not be distinct. -/
theorem dvd_finsetProd_pow_iff_of_prime {ι : Type*} {s : Finset ι} {p : ι → M}
    (hp : ∀ i ∈ s, Prime (p i)) (hreg : ∀ i ∈ s, IsLeftRegular (p i)) (m : ι → ℕ) {q : M} :
    q ∣ ∏ i ∈ s, p i ^ m i ↔
      ∃ k : ι → ℕ, (∀ i ∈ s, k i ≤ m i) ∧ Associated q (∏ i ∈ s, p i ^ k i) := by
  rw [← mul_one (∏ i ∈ s, p i ^ m i), dvd_finsetProd_pow_mul_iff_of_prime hp hreg m]
  refine ⟨fun ⟨k, hk, b, hb, hq⟩ ↦ ⟨k, hk, ?_⟩,
    fun ⟨k, hk, hq⟩ ↦ ⟨k, hk, 1, dvd_rfl, by simpa using hq⟩⟩
  have hu : Associated b 1 := associated_one_iff_isUnit.mpr (isUnit_of_dvd_one hb)
  exact hq.trans (by simpa using hu.mul_left (∏ i ∈ s, p i ^ k i))

/-- In a commutative monoid with zero, if `f` is left-regular and associated to a finite product
`∏ i ∈ s, p i` of primes, then any divisor `a` of `f ^ n` is associated to `∏ i ∈ s, p i ^ k i`
for some exponents `k i ≤ n`. -/
theorem exists_associated_finsetProd_pow_of_dvd_pow {ι : Type*} {s : Finset ι} {p : ι → M}
    {f a : M} {n : ℕ} (hp : ∀ i ∈ s, Prime (p i)) (hf : Associated f (∏ i ∈ s, p i))
    (hreg : IsLeftRegular f) (h : a ∣ f ^ n) :
    ∃ k : ι → ℕ, (∀ i ∈ s, k i ≤ n) ∧ Associated a (∏ i ∈ s, p i ^ k i) := by
  have h' : a ∣ ∏ i ∈ s, p i ^ n := by
    rw [Finset.prod_pow]
    exact h.trans hf.pow_pow.dvd
  have hregp : ∀ i ∈ s, IsLeftRegular (p i) := fun i hi ↦
    hreg.of_dvd ((Finset.dvd_prod_of_mem p hi).trans hf.symm.dvd)
  exact (dvd_finsetProd_pow_iff_of_prime hp hregp (fun _ ↦ n)).mp h'

end TauCeti
