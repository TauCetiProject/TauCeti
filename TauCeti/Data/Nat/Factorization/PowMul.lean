/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Splitting off an `n`-th power away from finitely many primes

If every prime `p` outside a finite set `S` occurs in `m` with multiplicity divisible by `n`, then
`m = a * u ^ n` where `a` is a product of primes of `S`, each to a power less than `n`: reduce
every exponent `v_p(m)` modulo `n` and collect the quotients into `u`. Equivalently,
`a ∣ (∏ p ∈ S, p) ^ (n - 1)`.

The typical source of this hypothesis is an equation `P * Q = y ^ n` in which `P` and `Q` share
no prime factor outside `S`: at such a prime only one of `P`, `Q` contributes, so its multiplicity
is a multiple of `n`. This is the first step in the reduction of a superelliptic equation
`y ^ n = (p x + q) (r x + s)` with two nonproportional linear factors to finitely many Thue
equations: a common prime of the two factors divides the fixed integer `q r - p s ≠ 0`, so each
factor is an `n`-th power up to one of finitely many coefficients `a`.

## Main results

* `Nat.exists_dvd_and_eq_mul_pow_of_dvd_factorization`: if `n ∣ v_p(m)` for every `p ∉ S`, then
  `m = a * u ^ n` with `a ∣ (∏ p ∈ S, p) ^ (n - 1)`.
* `Int.exists_dvd_and_eq_mul_pow_of_mul_eq_pow`: if `P * Q = y ^ n` and every prime dividing both
  `P` and `Q` lies in `S`, then `P = a * u ^ n` with `a ∣ (∏ p ∈ S, p) ^ (n - 1)`.

## References

* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, the example following Theorem 5.13, pp. 98–99.
-/

public section

open Finset

namespace Nat

/-- **Splitting off an `n`-th power.** If every prime outside the finite set `S` occurs in `m`
with multiplicity divisible by `n ≠ 0`, then `m = a * u ^ n` for some `a` dividing
`(∏ p ∈ S, p) ^ (n - 1)`. When `S` consists of primes, such an `a` is a product of primes of `S`,
each to a power less than `n`. -/
theorem exists_dvd_and_eq_mul_pow_of_dvd_factorization {m n : ℕ} {S : Finset ℕ} (hn : n ≠ 0)
    (h : ∀ p ∉ S, n ∣ m.factorization p) :
    ∃ a u : ℕ, a ∣ (∏ p ∈ S, p) ^ (n - 1) ∧ m = a * u ^ n := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact ⟨1, 0, one_dvd _, by simp [hn]⟩
  set f := m.factorization
  refine ⟨∏ p ∈ S, p ^ (f p % n), ∏ p ∈ m.primeFactors, p ^ (f p / n), ?_, ?_⟩
  · rw [← prod_pow]
    exact prod_dvd_prod_of_dvd _ _ fun p _ ↦
      pow_dvd_pow p (le_sub_one_of_lt (mod_lt _ (pos_of_ne_zero hn)))
  · -- Both products over `S` and over the prime factors of `m` agree with the product over
    -- their union, since the extra factors are `p ^ 0`.
    have hS : ∏ p ∈ S, p ^ (f p % n) = ∏ p ∈ m.primeFactors, p ^ (f p % n) := by
      rw [prod_subset subset_union_left (s₂ := S ∪ m.primeFactors),
        prod_subset subset_union_right (s₂ := S ∪ m.primeFactors)]
      · intro p _ hp
        rw [Finsupp.notMem_support_iff.mp hp, zero_mod, pow_zero]
      · intro p _ hp
        rw [mod_eq_zero_of_dvd (h p hp), pow_zero]
    conv_lhs => rw [← prod_factorization_pow_eq_self hm]
    rw [hS, Finsupp.prod, ← prod_pow, ← prod_mul_distrib]
    refine prod_congr rfl fun p _ ↦ ?_
    rw [← pow_mul, ← pow_add, mod_add_div']

end Nat

namespace Int

/-- **Splitting off an `n`-th power from a factor of an `n`-th power.** If `P * Q = y ^ n` with
`n ≠ 0` and every prime dividing both `P` and `Q` lies in the finite set `S`, then
`P = a * u ^ n` for some `a` dividing `(∏ p ∈ S, p) ^ (n - 1)`. For `S = ∅`, that is coprime `P`
and `Q`, this says that `P` is an `n`-th power up to sign. -/
theorem exists_dvd_and_eq_mul_pow_of_mul_eq_pow {n : ℕ} {S : Finset ℕ} {P Q y : ℤ} (hn : n ≠ 0)
    (h : P * Q = y ^ n) (hS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ P → (p : ℤ) ∣ Q → p ∈ S) :
    ∃ a u : ℤ, a ∣ (∏ p ∈ S, (p : ℤ)) ^ (n - 1) ∧ P = a * u ^ n := by
  have hfac : ∀ p ∉ S, n ∣ P.natAbs.factorization p := by
    intro p hpS
    by_contra hdvd
    have hP : P.natAbs.factorization p ≠ 0 := fun h0 ↦ hdvd (h0 ▸ dvd_zero n)
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hP)
    have hpP : (p : ℤ) ∣ P := Int.natCast_dvd.mpr (Nat.dvd_of_factorization_pos hP)
    have hP0 : P ≠ 0 := by rintro rfl; simp at hP
    -- At a prime outside `S`, the factor `Q` contributes nothing to `y ^ n`.
    have hQ : Q.natAbs.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hpQ ↦ hpS (hS p hp hpP (Int.natCast_dvd.mpr hpQ))
    have hQ0 : Q ≠ 0 := by rintro rfl; exact hpS (hS p hp hpP (dvd_zero _))
    have hPQ := congrArg (fun k : ℕ ↦ k.factorization p) (congrArg Int.natAbs h)
    simp only [Int.natAbs_mul, Int.natAbs_pow] at hPQ
    rw [Nat.factorization_mul (Int.natAbs_ne_zero.mpr hP0) (Int.natAbs_ne_zero.mpr hQ0),
      Nat.factorization_pow, Finsupp.add_apply, hQ, add_zero, Finsupp.smul_apply,
      smul_eq_mul] at hPQ
    exact hdvd (hPQ ▸ dvd_mul_right n _)
  obtain ⟨a, u, ha, hau⟩ := Nat.exists_dvd_and_eq_mul_pow_of_dvd_factorization hn hfac
  have ha' : (a : ℤ) ∣ (∏ p ∈ S, (p : ℤ)) ^ (n - 1) := by
    simpa only [Nat.cast_pow, Nat.cast_prod] using Int.natCast_dvd_natCast.mpr ha
  rcases Int.natAbs_eq P with hP | hP
  · exact ⟨a, u, ha', by rw [hP, hau, Nat.cast_mul, Nat.cast_pow]⟩
  · exact ⟨-a, u, neg_dvd.mpr ha', by rw [hP, hau, Nat.cast_mul, Nat.cast_pow, neg_mul]⟩

end Int
