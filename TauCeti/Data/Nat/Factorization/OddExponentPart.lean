/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Ring

/-!
# The odd-exponent part of a natural number away from a modulus

Fix a natural number `m`. The odd-exponent part `Nat.oddExpPart m n` of `n` away from `m` is the
product of the primes `p ∤ m` dividing `n` to an odd power. For `n ≠ 0` it is the squarefree part
of `n` with the primes dividing `m` removed; for `n = 0` it is the empty product `1`. Every `n` is
`oddExpPart m n · t² · A`, where every prime factor of `A` divides `m`.

## Main definitions

* `Nat.oddExpPart m n`: the product of the primes `p ∤ m` dividing `n` to an odd power.

## Main results

* `Nat.mem_primeFactors_oddExpPart`: the prime factors of `oddExpPart m n` are exactly the primes
  `p ∤ m` dividing `n` to an odd power.
* `Nat.oddExpPart_eq_one_iff`, `Nat.oddExpPart_eq_one_iff_of_isPrimePow`: `oddExpPart m n = 1`
  exactly when every prime factor of `n` divides `m` or divides `n` to an even power.
* `Nat.exists_eq_oddExpPart_mul_sq_mul`: `n = oddExpPart m n · t² · A` for some `t` and some `A`
  whose prime factors divide `m`.
* `Nat.oddExpPart_prime_pow`, `Nat.oddExpPart_mul_of_isPrimePow`: the odd-exponent part of a
  prime power and of a product of two prime powers.
-/

public section

namespace Nat

/-- The odd-exponent part of `n` away from `m`: the product of the primes `p ∤ m` dividing `n` to
an odd power. For `n = 0` the product is empty, so `oddExpPart m 0 = 1`. It unfolds by
`oddExpPart_def`, and its prime factors are described by `mem_primeFactors_oddExpPart`. -/
def oddExpPart (m n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with ¬ p ∣ m ∧ Odd (n.factorization p), p

theorem oddExpPart_def (m n : ℕ) :
    oddExpPart m n = ∏ p ∈ n.primeFactors with ¬ p ∣ m ∧ Odd (n.factorization p), p := by
  rw [oddExpPart]

@[simp]
theorem oddExpPart_zero (m : ℕ) : oddExpPart m 0 = 1 := by
  simp [oddExpPart_def]

@[simp]
theorem oddExpPart_one (m : ℕ) : oddExpPart m 1 = 1 := by
  simp [oddExpPart_def]

/-- The prime factors of `oddExpPart m n` are the primes `p ∤ m` dividing `n` to an odd power. -/
theorem mem_primeFactors_oddExpPart {m n p : ℕ} :
    p ∈ (oddExpPart m n).primeFactors ↔
      p ∈ n.primeFactors ∧ ¬ p ∣ m ∧ Odd (n.factorization p) := by
  rw [oddExpPart_def, primeFactors_prod fun q hq =>
    prime_of_mem_primeFactors (Finset.mem_filter.1 hq).1, Finset.mem_filter]

/-- The odd-exponent part of `n` away from `m` is `1` exactly when every prime factor of `n`
divides `m` or divides `n` to an even power. -/
theorem oddExpPart_eq_one_iff {m n : ℕ} :
    oddExpPart m n = 1 ↔ ∀ p ∈ n.primeFactors, p ∣ m ∨ Even (n.factorization p) := by
  rw [oddExpPart_def, Finset.prod_eq_one_iff_of_one_le fun p hp =>
    (prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).one_lt.le]
  refine forall_congr' fun p => ?_
  simp only [Finset.mem_filter, and_imp, ← not_odd_iff_even]
  refine imp_congr_right fun hp => ?_
  have := (prime_of_mem_primeFactors hp).ne_one
  tauto

/-- The odd-exponent part of `n` away from an even `m` is odd. -/
theorem odd_oddExpPart {m : ℕ} (n : ℕ) (h2 : 2 ∣ m) : Odd (oddExpPart m n) := by
  rw [oddExpPart_def]
  refine Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rcases (prime_of_mem_primeFactors hp.1).eq_two_or_odd' with rfl | hodd
  · exact (hp.2.1 h2).elim
  · exact hodd

theorem squarefree_oddExpPart (m n : ℕ) : Squarefree (oddExpPart m n) :=
  n.squarefree_prod_primeFactors.squarefree_of_dvd
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))

theorem coprime_oddExpPart (m n : ℕ) : (oddExpPart m n).Coprime m := by
  rw [oddExpPart_def]
  refine Nat.coprime_prod_left_iff.mpr fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact ((prime_of_mem_primeFactors hp.1).coprime_iff_not_dvd).mpr hp.2.1

/-- Every `n` is `s t² A`, where `s = oddExpPart m n` is the product of the primes `p ∤ m`
dividing `n` to an odd power, and every prime factor of `A` divides `m`. For `n = 0`, `t = 0` and
`A = 1` serve. -/
theorem exists_eq_oddExpPart_mul_sq_mul (m n : ℕ) :
    ∃ t A : ℕ, n = oddExpPart m n * t ^ 2 * A ∧ ∀ p, p.Prime → p ∣ A → p ∣ m := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨0, 1, by simp, fun p hp h => (hp.ne_one (Nat.dvd_one.1 h)).elim⟩
  rw [oddExpPart_def]
  have key : ∀ p e : ℕ, p ^ e = (if Odd e then p else 1) * (p ^ (e / 2)) ^ 2 := by
    intro p e
    rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
    · have hk : 2 * k / 2 = k := by omega
      simp only [Nat.not_odd_iff_even.2 (even_two_mul k), ↓reduceIte, hk]
      ring
    · have hk : (2 * k + 1) / 2 = k := by omega
      simp only [odd_two_mul_add_one k, ↓reduceIte, hk]
      ring
  refine ⟨∏ p ∈ n.primeFactors with ¬ p ∣ m, p ^ (n.factorization p / 2),
    ∏ p ∈ n.primeFactors with p ∣ m, p ^ n.factorization p, ?_, fun p hp hpA => ?_⟩
  · conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn,
      ← Finset.prod_filter_not_mul_prod_filter _ (· ∣ m)]
    rw [Finset.prod_congr rfl fun p _ => key p _, Finset.prod_mul_distrib, Finset.prod_pow,
      ← Finset.prod_filter, Finset.filter_filter]
  · obtain ⟨r, hr, hpr⟩ := (_root_.Prime.dvd_finsetProd_iff hp.prime _).1 hpA
    exact (hp.dvd_of_dvd_pow hpr).trans (Finset.mem_filter.1 hr).2

theorem oddExpPart_dvd (m n : ℕ) : oddExpPart m n ∣ n := by
  obtain ⟨t, A, h, -⟩ := exists_eq_oddExpPart_mul_sq_mul m n
  exact ⟨t ^ 2 * A, by rw [← mul_assoc]; exact h⟩

theorem oddExpPart_le {m n : ℕ} (hn : n ≠ 0) : oddExpPart m n ≤ n :=
  le_of_dvd (pos_of_ne_zero hn) (oddExpPart_dvd m n)

/-- The odd-exponent part of `p ^ k` is `p` if `p ∤ m` and `k` is odd, and `1` otherwise. -/
@[simp]
theorem oddExpPart_prime_pow {m p k : ℕ} (hp : p.Prime) :
    oddExpPart m (p ^ k) = if ¬ p ∣ m ∧ Odd k then p else 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [oddExpPart_def, ← not_even_iff_odd]
  rw [oddExpPart_def, primeFactors_pow p hk, hp.primeFactors, Finset.filter_singleton,
    hp.factorization_pow, Finsupp.single_eq_same]
  split_ifs <;> simp

/-- The odd-exponent part of a prime power `n` is its prime `n.minFac` if `n.minFac ∤ m` and the
exponent of `n.minFac` in `n` is odd, and `1` otherwise. -/
theorem oddExpPart_of_isPrimePow {m n : ℕ} (hn : IsPrimePow n) :
    oddExpPart m n =
      if ¬ n.minFac ∣ m ∧ Odd (n.factorization n.minFac) then n.minFac else 1 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  rw [oddExpPart_prime_pow hp.nat_prime, hp.nat_prime.pow_minFac hk.ne',
    hp.nat_prime.factorization_pow, Finsupp.single_eq_same]

/-- The odd-exponent part of a prime power `n` away from `m` is `1` exactly when `n.minFac`
divides `m` or the exponent of `n.minFac` in `n` is even. -/
theorem oddExpPart_eq_one_iff_of_isPrimePow {m n : ℕ} (hn : IsPrimePow n) :
    oddExpPart m n = 1 ↔ n.minFac ∣ m ∨ Even (n.factorization n.minFac) := by
  rw [oddExpPart_of_isPrimePow hn, ← not_odd_iff_even]
  have := (minFac_prime hn.ne_one).ne_one
  split_ifs <;> tauto

/-- A prime power whose odd-exponent part is not `1` has odd-exponent part its prime. -/
theorem oddExpPart_eq_minFac_of_isPrimePow {m n : ℕ} (hn : IsPrimePow n)
    (h : oddExpPart m n ≠ 1) : oddExpPart m n = n.minFac := by
  rw [oddExpPart_of_isPrimePow hn] at h ⊢
  split_ifs at h ⊢
  · rfl
  · exact (h rfl).elim

/-- The odd-exponent part of a product of two prime powers `n` and `n'`: the other factor's part
when one part is `1`, `1` when both parts are the same prime, and the product of the two primes
otherwise. -/
theorem oddExpPart_mul_of_isPrimePow {m n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n') :
    oddExpPart m (n * n') =
      if oddExpPart m n = 1 then oddExpPart m n'
      else if oddExpPart m n' = 1 then oddExpPart m n
      else if n.minFac = n'.minFac then 1
      else n.minFac * n'.minFac := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  obtain ⟨q, l, hq, hl, rfl⟩ := hn'
  replace hp := hp.nat_prime
  replace hq := hq.nat_prime
  rw [hp.pow_minFac hk.ne', hq.pow_minFac hl.ne']
  by_cases hpq : p = q
  · subst hpq
    rw [ite_eq_left rfl, ← pow_add, oddExpPart_prime_pow hp, oddExpPart_prime_pow hp,
      oddExpPart_prime_pow hp]
    by_cases hdiv : p ∣ m
    · simp [hdiv]
    rcases even_or_odd k with hk' | hk' <;> rcases even_or_odd l with hl' | hl'
    · simp [hdiv, not_odd_iff_even.2 hk', not_odd_iff_even.2 hl', not_odd_iff_even.2 (hk'.add hl')]
    · simp [hdiv, not_odd_iff_even.2 hk', hl', hk'.add_odd hl']
    · simp [hdiv, hk', not_odd_iff_even.2 hl', hk'.add_even hl', hp.ne_one]
    · simp [hdiv, hk', hl', not_odd_iff_even.2 (hk'.add_odd hl'), hp.ne_one]
  have hk0 := pow_ne_zero k hp.ne_zero
  have hl0 := pow_ne_zero l hq.ne_zero
  have hpf : (p ^ k * q ^ l).primeFactors = {p, q} := by
    rw [primeFactors_mul hk0 hl0, primeFactors_pow p hk.ne', primeFactors_pow q hl.ne',
      hp.primeFactors, hq.primeFactors, ← Finset.insert_eq]
  have hfac : (p ^ k * q ^ l).factorization = Finsupp.single p k + Finsupp.single q l := by
    rw [factorization_mul hk0 hl0, hp.factorization_pow, hq.factorization_pow]
  rw [oddExpPart_prime_pow hp, oddExpPart_prime_pow hq, oddExpPart_def, hpf,
    Finset.filter_insert, Finset.filter_singleton, hfac]
  by_cases h1 : ¬ p ∣ m ∧ Odd k <;> by_cases h2 : ¬ q ∣ m ∧ Odd l <;>
    simp [h1, h2, hpq, Ne.symm hpq, hp.ne_one, hq.ne_one]

end Nat
