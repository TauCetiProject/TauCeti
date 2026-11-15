/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated

/-!
# Divisors and associates of products of prime powers

In a cancellative commutative monoid with zero, Mathlib's `dvd_prime_pow` describes the divisors
of a single prime power `p ^ n` up to associates. Without assuming unique factorization or a
trivial unit group, the same cancellation argument extends to finite products of prime powers:

* Any divisor of `p ^ n * b` with `p` prime factors literally as `p ^ i * q` with `i ≤ n` and
  `q ∣ b` (`Prime.dvd_pow_mul_iff`).
* Consequently, the divisors of a finite product `∏ i ∈ s, p i ^ n i` of prime powers are
  precisely the elements associated to `∏ i ∈ s, p i ^ c i` with `c i ≤ n i`
  (`Finset.dvd_prod_pow_iff_of_prime`).
* When the primes `p i` (`i ∈ s`) are pairwise non-associated, the exponents in such a product
  are uniquely determined up to association (`Finset.prod_pow_associated_iff_of_prime`).

These results describe the units obtained by inverting a finite product of primes in an integral
domain, without requiring the ambient domain to be factorial.

## Main results

* `Prime.dvd_pow_mul_iff`: `a ∣ p ^ n * b` iff `a = p ^ i * q` for some `i ≤ n` and `q ∣ b`.
* `Finset.dvd_prod_pow_iff_of_prime`: `a ∣ ∏ i ∈ s, p i ^ n i` iff `a` is associated to
  `∏ i ∈ s, p i ^ c i` for some `c` with `c i ≤ n i` on `s`.
* `Finset.dvd_pow_prod_iff_of_prime`: the specialization to `(∏ i ∈ s, p i) ^ k`.
* `Finset.prod_pow_associated_iff_of_prime`: for pairwise non-associated primes on `s`,
  `∏ i ∈ s, p i ^ c i` and `∏ i ∈ s, p i ^ d i` are associated iff `c` and `d` agree on `s`.
-/

public section

variable {ι M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]

namespace Prime

/-- In a cancellative commutative monoid with zero, a divisor of `p ^ n * b` with `p` prime
factors as `p ^ i * q` with `i ≤ n` and `q ∣ b`. -/
theorem dvd_pow_mul_iff {p : M} (hp : Prime p) (n : ℕ) {b a : M} :
    a ∣ p ^ n * b ↔ ∃ i ≤ n, ∃ q, q ∣ b ∧ a = p ^ i * q := by
  induction n generalizing a with
  | zero =>
    refine ⟨fun h ↦ ⟨0, le_rfl, a, by simpa using h, by simp⟩, ?_⟩
    rintro ⟨i, hi, q, hq, rfl⟩
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    simpa using hq
  | succ n ih =>
    refine ⟨fun h ↦ ?_, ?_⟩
    · rw [pow_succ', mul_assoc] at h
      rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with ⟨a', rfl⟩ | h'
      · obtain ⟨i, hi, q, hq, rfl⟩ := ih.mp ((mul_dvd_mul_iff_left hp.ne_zero).mp h)
        exact ⟨i + 1, Nat.succ_le_succ hi, q, hq, by rw [pow_succ', mul_assoc]⟩
      · obtain ⟨i, hi, q, hq, rfl⟩ := ih.mp h'
        exact ⟨i, Nat.le_succ_of_le hi, q, hq, rfl⟩
    · rintro ⟨i, hi, q, hq, rfl⟩
      exact mul_dvd_mul (pow_dvd_pow p hi) hq

end Prime

namespace Finset

/-- The divisors of a finite product `∏ i ∈ s, p i ^ n i` of powers of primes are the elements
associated to `∏ i ∈ s, p i ^ c i` with `c i ≤ n i` on `s`. -/
theorem dvd_prod_pow_iff_of_prime (s : Finset ι) {p : ι → M}
    (hp : ∀ i ∈ s, Prime (p i)) (n : ι → ℕ) {a : M} :
    a ∣ ∏ i ∈ s, p i ^ n i ↔
      ∃ c : ι → ℕ, (∀ i ∈ s, c i ≤ n i) ∧ Associated a (∏ i ∈ s, p i ^ c i) := by
  classical
  refine ⟨fun hdvd ↦ ?_, fun ⟨c, hc, ha⟩ ↦
    ha.dvd.trans (Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow (p i) (hc i hi))⟩
  induction s using Finset.cons_induction generalizing a with
  | empty =>
    exact ⟨0, by simp, associated_one_iff_isUnit.mpr (isUnit_of_dvd_one (by simpa using hdvd))⟩
  | cons j s hj ih =>
    rw [Finset.prod_cons] at hdvd
    have hpj : Prime (p j) := hp j (Finset.mem_cons_self j s)
    have hps : ∀ i ∈ s, Prime (p i) := fun i hi ↦ hp i (Finset.mem_cons_of_mem hi)
    obtain ⟨k, hk, q, hq, rfl⟩ := (hpj.dvd_pow_mul_iff (n j)).mp hdvd
    obtain ⟨c, hc, hqa⟩ := ih hps hq
    refine ⟨Function.update c j k, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_cons.mp hi with rfl | hi
      · simpa using hk
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
        exact hc i hi
    · rw [Finset.prod_cons, Function.update_self]
      have hprod : ∏ i ∈ s, p i ^ Function.update c j k i = ∏ i ∈ s, p i ^ c i :=
        Finset.prod_congr rfl fun i hi ↦ by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
      rw [hprod]
      exact Associated.mul_left _ hqa

/-- The divisors of `(∏ i ∈ s, p i) ^ k`, for primes `p i`, are the elements associated to
`∏ i ∈ s, p i ^ c i` with `c i ≤ k` on `s`. -/
theorem dvd_pow_prod_iff_of_prime (s : Finset ι) {p : ι → M}
    (hp : ∀ i ∈ s, Prime (p i)) (k : ℕ) {a : M} :
    a ∣ (∏ i ∈ s, p i) ^ k ↔
      ∃ c : ι → ℕ, (∀ i ∈ s, c i ≤ k) ∧ Associated a (∏ i ∈ s, p i ^ c i) := by
  rw [← Finset.prod_pow]
  exact s.dvd_prod_pow_iff_of_prime hp fun _ ↦ k

/-- A prime not associated to any prime in a finite family does not divide a product of powers of
that family. -/
theorem _root_.Prime.not_dvd_finsetProd_pow {s : Finset ι} {p : ι → M} {q : M}
    (hq : Prime q) (hp : ∀ i ∈ s, Prime (p i)) (hna : ∀ i ∈ s, ¬Associated q (p i))
    (c : ι → ℕ) : ¬q ∣ ∏ i ∈ s, p i ^ c i :=
  hq.not_dvd_finsetProd fun i hi hdiv ↦
    hna i hi (hq.associated_of_dvd (hp i hi) (hq.dvd_of_dvd_pow hdiv))

private theorem le_of_prod_pow_associated_cons {j : ι} {s : Finset ι} (hj : j ∉ s) {p : ι → M}
    (hp : ∀ i ∈ cons j s hj, Prime (p i))
    (hpair : (cons j s hj : Set ι).Pairwise fun a b ↦ ¬Associated (p a) (p b))
    {c d : ι → ℕ}
    (h : Associated (∏ i ∈ cons j s hj, p i ^ c i) (∏ i ∈ cons j s hj, p i ^ d i)) :
    d j ≤ c j := by
  have hpj : Prime (p j) := hp j (mem_cons_self j s)
  have hps : ∀ i ∈ s, Prime (p i) := fun i hi ↦ hp i (mem_cons_of_mem hi)
  have hna : ∀ i ∈ s, ¬Associated (p j) (p i) := fun i hi ↦
    hpair (mem_cons_self j s) (mem_cons_of_mem hi) (ne_of_mem_of_not_mem hi hj).symm
  rw [prod_cons, prod_cons] at h
  obtain ⟨u, hu⟩ := h
  by_contra! hlt
  obtain ⟨k, hk⟩ : ∃ k, d j = c j + (k + 1) := ⟨d j - c j - 1, by omega⟩
  -- Cancel `p j ^ c j`; the remaining factor of `p j` would divide `(∏ i ∈ s, p i ^ c i) * u`.
  have hcancel : (∏ i ∈ s, p i ^ c i) * u = p j ^ (k + 1) * ∏ i ∈ s, p i ^ d i := by
    apply mul_left_cancel₀ (pow_ne_zero (c j) hpj.ne_zero)
    calc
      p j ^ c j * ((∏ i ∈ s, p i ^ c i) * u) = (p j ^ c j * ∏ i ∈ s, p i ^ c i) * u :=
        (mul_assoc ..).symm
      _ = p j ^ d j * ∏ i ∈ s, p i ^ d i := hu
      _ = p j ^ c j * (p j ^ (k + 1) * ∏ i ∈ s, p i ^ d i) := by rw [hk, pow_add, mul_assoc]
  have hdvd : p j ∣ (∏ i ∈ s, p i ^ c i) * u := by
    rw [hcancel, pow_succ', mul_assoc]
    exact dvd_mul_right _ _
  exact hpj.not_dvd_finsetProd_pow hps hna c
    ((hpj.dvd_or_dvd hdvd).resolve_right fun hpu ↦ hpj.not_isUnit (isUnit_of_dvd_unit hpu u.isUnit))

/-- For pairwise non-associated primes `p i` (`i ∈ s`), two products `∏ i ∈ s, p i ^ c i` and
`∏ i ∈ s, p i ^ d i` are associated if and only if their exponents agree on `s`. -/
theorem prod_pow_associated_iff_of_prime (s : Finset ι) {p : ι → M}
    (hp : ∀ i ∈ s, Prime (p i))
    (hpair : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j)) {c d : ι → ℕ} :
    Associated (∏ i ∈ s, p i ^ c i) (∏ i ∈ s, p i ^ d i) ↔ ∀ i ∈ s, c i = d i := by
  refine ⟨fun h ↦ ?_, fun h ↦ Associated.of_eq (Finset.prod_congr rfl fun i hi ↦ by rw [h i hi])⟩
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    have hcj : c j = d j := le_antisymm (le_of_prod_pow_associated_cons hj hp hpair h.symm)
      (le_of_prod_pow_associated_cons hj hp hpair h)
    have hpj : Prime (p j) := hp j (mem_cons_self j s)
    have hps : ∀ i ∈ s, Prime (p i) := fun i hi ↦ hp i (mem_cons_of_mem hi)
    have hpairs : (s : Set ι).Pairwise fun a b ↦ ¬Associated (p a) (p b) :=
      hpair.mono (by simp)
    rw [prod_cons, prod_cons, hcj] at h
    obtain ⟨u, hu⟩ := h
    have hs : Associated (∏ i ∈ s, p i ^ c i) (∏ i ∈ s, p i ^ d i) :=
      ⟨u, mul_left_cancel₀ (pow_ne_zero (d j) hpj.ne_zero) (by rwa [← mul_assoc])⟩
    intro i hi
    rcases mem_cons.mp hi with rfl | hi
    · exact hcj
    · exact ih hps hpairs hs i hi

end Finset
