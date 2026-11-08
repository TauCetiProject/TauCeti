/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factors

/-!
# Primitive prime divisors at small exponents

A primitive prime divisor of `a ^ n - b ^ n` is a prime `p` dividing `a ^ n - b ^ n` and none of
the `a ^ k - b ^ k` with `0 < k < n`. The Bang–Zsigmondy theorem asserts that for coprime
`a > b > 0` and `n ≥ 2` such a prime exists, with exactly two exceptions: `n = 2` with `a + b` a
power of two, and `(a, b, n) = (2, 1, 6)`. This file settles the cases that need no cyclotomic
input: the exponents `n = 1` and `n = 2`, completely, and the nonexistence at `(2, 1, 6)`.

At `n = 2` the factorization `a ^ 2 - b ^ 2 = (a + b) * (a - b)` decides everything: for coprime
`a` and `b`, the greatest common divisor of `a + b` and `a - b` divides `2`, so an odd prime
factor of `a + b` is primitive, while if `a + b` is a power of two every prime divisor of
`a ^ 2 - b ^ 2` already divides `a - b`.

Primitivity is written out as
`p.Prime ∧ p ∣ a ^ n - b ^ n ∧ ∀ k, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k` rather than through a
predicate, and subtraction is natural subtraction.

## Main results

* `TauCeti.exists_prime_dvd_sub_iff`: `a - b` has a primitive prime divisor iff `1 < a - b`.
* `Nat.Prime.dvd_sub_of_dvd_sq_sub_sq_of_add_eq_two_pow`: if `a + b` is a power of two, every
  prime divisor of `a ^ 2 - b ^ 2` divides `a - b`.
* `TauCeti.exists_prime_dvd_sq_sub_sq_iff`: for coprime `b ≤ a`, `a ^ 2 - b ^ 2` has a primitive
  prime divisor iff `a + b` is not a power of two.
* `TauCeti.exists_prime_dvd_sq_sub_sq_iff_exists_odd_prime_dvd`: equivalently, iff `a + b` has
  an odd prime factor.
* `TauCeti.not_exists_prime_dvd_two_pow_six_sub_one_pow_six`: `2 ^ 6 - 1 ^ 6 = 63` has no
  primitive prime divisor.

## References

* K. Zsigmondy, *Zur Theorie der Potenzreste*, Monatsh. Math. Phys. 3 (1892), 265–284, p. 283.
* G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of `a ^ n - b ^ n`*, Ann. of
  Math. (2) 5 (1904), 173–180, Theorem V.
* M. Roitman, *On Zsigmondy primes*, Proc. Amer. Math. Soc. 125 (1997), 1913–1919, Theorem 3
  and p. 1916.
-/

public section

/-- If `a + b` is a power of two, then every prime divisor of `a ^ 2 - b ^ 2` divides `a - b`,
so `a ^ 2 - b ^ 2` has no primitive prime divisor. -/
theorem Nat.Prime.dvd_sub_of_dvd_sq_sub_sq_of_add_eq_two_pow {p a b k : ℕ} (hp : p.Prime)
    (hk : a + b = 2 ^ k) (hdvd : p ∣ a ^ 2 - b ^ 2) : p ∣ a - b := by
  rw [Nat.pow_two_sub_pow_two] at hdvd
  rcases hp.dvd_mul.1 hdvd with hpab | hpab
  · rw [hk] at hpab
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpab)
    rcases le_or_gt b a with hba | hab
    · -- `a - b = (a + b) - 2 * b` is even because `a + b = 2 ^ k` is.
      have hsub : a - b = a + b - 2 * b := by omega
      rw [hsub, hk]
      exact Nat.dvd_sub hpab (dvd_mul_right 2 b)
    · rw [Nat.sub_eq_zero_of_le hab.le]
      exact dvd_zero 2
  · exact hpab

namespace TauCeti

/-- Exponent one: for `b < a`, the number `a - b` has a primitive prime divisor (the condition on
the exponents `0 < k < 1` being vacuous) if and only if `1 < a - b`. -/
theorem exists_prime_dvd_sub_iff {a b : ℕ} (hba : b < a) :
    (∃ p : ℕ, p.Prime ∧ p ∣ a - b ∧ ∀ k : ℕ, 0 < k → k < 1 → ¬ p ∣ a ^ k - b ^ k) ↔
      1 < a - b := by
  constructor
  · rintro ⟨p, hp, hdvd, -⟩
    exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (Nat.sub_pos_of_lt hba) hdvd)
  · intro h
    obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd h.ne'
    exact ⟨p, hp, hdvd, fun k hk hk1 => absurd hk1 (by omega)⟩

/-- Exponent two: for coprime `b ≤ a`, the number `a ^ 2 - b ^ 2` has a primitive prime divisor
if and only if `a + b` has an odd prime factor. -/
theorem exists_prime_dvd_sq_sub_sq_iff_exists_odd_prime_dvd {a b : ℕ} (hba : b ≤ a)
    (hab : a.Coprime b) :
    (∃ p : ℕ, p.Prime ∧ p ∣ a ^ 2 - b ^ 2 ∧ ∀ k : ℕ, 0 < k → k < 2 → ¬ p ∣ a ^ k - b ^ k) ↔
      ∃ p : ℕ, p.Prime ∧ p ∣ a + b ∧ Odd p := by
  constructor
  · rintro ⟨p, hp, hdvd, hprim⟩
    obtain ⟨k, hk⟩ | h := (a + b).eq_two_pow_or_exists_odd_prime_and_dvd
    · exact absurd (by simpa using hp.dvd_sub_of_dvd_sq_sub_sq_of_add_eq_two_pow hk hdvd)
        (hprim 1 Nat.one_pos Nat.one_lt_two)
    · exact h
  · -- An odd prime factor of `a + b` cannot divide `a - b`: it would divide
    -- `(a + b) + (a - b) = 2 * a`, hence `a` and then `b`.
    rintro ⟨p, hp, hpab, hodd⟩
    refine ⟨p, hp, Nat.pow_two_sub_pow_two a b ▸ dvd_mul_of_dvd_left hpab _,
      fun k hk hk2 hdvd => ?_⟩
    obtain rfl : k = 1 := by omega
    rw [pow_one, pow_one] at hdvd
    have h2a : p ∣ 2 * a := by
      have hsum : 2 * a = (a + b) + (a - b) := by omega
      exact hsum ▸ dvd_add hpab hdvd
    have ha : p ∣ a := (Nat.Coprime.dvd_mul_left (Nat.coprime_two_right.2 hodd)).1 h2a
    have hb : p ∣ b := (Nat.dvd_add_right ha).1 hpab
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hab ha hb)

/-- Exponent two: for coprime `b ≤ a`, the number `a ^ 2 - b ^ 2` has a primitive prime divisor
if and only if `a + b` is not a power of two. This is the Bang–Zsigmondy theorem at `n = 2`
together with its exceptional case. -/
theorem exists_prime_dvd_sq_sub_sq_iff {a b : ℕ} (hba : b ≤ a) (hab : a.Coprime b) :
    (∃ p : ℕ, p.Prime ∧ p ∣ a ^ 2 - b ^ 2 ∧ ∀ k : ℕ, 0 < k → k < 2 → ¬ p ∣ a ^ k - b ^ k) ↔
      ¬ ∃ k : ℕ, a + b = 2 ^ k := by
  rw [exists_prime_dvd_sq_sub_sq_iff_exists_odd_prime_dvd hba hab]
  constructor
  · rintro ⟨p, hp, hpab, hodd⟩ ⟨k, hk⟩
    rw [hk] at hpab
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpab)
    exact Nat.not_even_iff_odd.2 hodd even_two
  · exact (a + b).eq_two_pow_or_exists_odd_prime_and_dvd.resolve_left

/-- The exceptional case `(a, b, n) = (2, 1, 6)` of the Bang–Zsigmondy theorem: every prime
divisor of `2 ^ 6 - 1 ^ 6 = 63 = 3 ^ 2 * 7` divides an earlier `2 ^ k - 1 ^ k`, namely
`3 ∣ 2 ^ 2 - 1` and `7 ∣ 2 ^ 3 - 1`. -/
theorem not_exists_prime_dvd_two_pow_six_sub_one_pow_six :
    ¬ ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ 6 - 1 ^ 6 ∧
      ∀ k : ℕ, 0 < k → k < 6 → ¬ p ∣ 2 ^ k - 1 ^ k := by
  rintro ⟨p, hp, hdvd, hprim⟩
  have h63 : p ∣ 3 ^ 2 * 7 := by simpa using hdvd
  rcases hp.dvd_mul.1 h63 with h | h
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
    exact hprim 2 (by decide) (by decide) (by decide)
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1 h
    exact hprim 3 (by decide) (by decide) (by decide)

end TauCeti
