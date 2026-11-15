/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors

/-!
# Prime natural numbers: the `Fact` instance on the subtype, the primes prime to `6`,
gcd and lcm with a multiple by a prime, and prime-power divisibility

Mathlib's `Nat.Primes` is the subtype of prime natural numbers. Much of the prime-indexed API
(`ZMod p` as a field, the `p`-adic integers `ℤ_[p]`, Sylow theory) takes its prime as a natural
number `p : ℕ` together with an instance `[Fact p.Prime]`, so a family indexed by `Nat.Primes`, such
as `∀ p : Nat.Primes, ℤ_[p]`, can only be written once the primality of `(p : ℕ)` is available to
instance search. Mathlib supplies it only as a local instance
(`Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean`); this module makes it global.

Arguments that treat the primes `2` and `3` separately, as for Weierstrass equations, need the
complementary fact that every other prime, that is, every prime `p ≥ 5`, does not divide `6`.

If `n ∣ m` but `q * n ∤ m` for a prime `q`, then `m` and `n` have the same `q`-part, hence so do
`q * m` and `q * n`; this pins down the gcd and lcm of `m` and `q * n`, which are used to compare
a level `q * n` with a multiple `q * m` of the same `q`-part, as for congruence subgroups.

For coprime natural bases `b ≤ a`, a prime dividing `a ^ n - b ^ n` with `n > 0` divides
neither base; this ensures that their ratio modulo the prime is a unit.

For a prime `p`, every prime `q ≠ p` is coprime to `p ^ k`, and a natural number `k` has no prime
divisor distinct from `p` precisely when `k` is a power of `p` (equivalently, some prime `q ≠ p`
divides `k` precisely when `k` is not a power of `p`).

## Main declarations

* `Nat.Primes.instFactPrime`: for `p : Nat.Primes`, the instance `Fact (p : ℕ).Prime`.
* `Nat.Prime.not_dvd_six_of_five_le`: a prime `p ≥ 5` does not divide `6`.
* `Nat.Prime.gcd_mul_eq_of_dvd_of_not_mul_dvd`, `Nat.Prime.lcm_mul_eq_of_dvd_of_not_mul_dvd`:
  if `n ∣ m` and `q * n ∤ m`, then `gcd m (q * n) = n` and `lcm m (q * n) = q * m`.
* `Nat.Prime.dvd_gcd_of_dvd_pow_sub_pow_of_dvd_mul`: a prime dividing both
  `a ^ n - b ^ n` and `a * b`, with `b ≤ a` and `n > 0`, divides `a.gcd b`.
* `Nat.Coprime.not_dvd_mul_of_dvd_pow_sub_pow`: for coprime natural bases `b ≤ a`, prime
  divisors of `a ^ n - b ^ n` with `n > 0` do not divide the product of the bases.
* `Nat.Prime.coprime_pow_of_prime_ne`: every prime `q ≠ p` is coprime to `p ^ k`.
* `Nat.forall_prime_ne_not_dvd_iff_exists_pow`, `Nat.exists_prime_ne_dvd_iff_forall_pow_ne`:
  characterization of powers of a prime `p` by absence of prime divisors `q ≠ p`.
-/

public section

/-- A prime, as an element of the subtype `Nat.Primes`, is prime: the `Fact` instance under which
the prime-indexed API, for instance the `p`-adic integers `ℤ_[p]`, can be used for `p : Nat.Primes`.
-/
instance Nat.Primes.instFactPrime (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **A prime at least `5` does not divide `6`**: the primes dividing `6` are `2` and `3`. -/
theorem Nat.Prime.not_dvd_six_of_five_le {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ∣ 6 :=
  fun h => by
    have := Nat.le_of_dvd (by decide) h
    obtain rfl | rfl : p = 5 ∨ p = 6 := by omega
    · omega
    · exact absurd hp (by decide)

/-- If `n ∣ m` and `q * n ∤ m` for a prime `q`, then `gcd m (q * n) = n`. -/
theorem Nat.Prime.gcd_mul_eq_of_dvd_of_not_mul_dvd {q n m : ℕ} (hq : q.Prime) (hnm : n ∣ m)
    (hqnm : ¬q * n ∣ m) : Nat.gcd m (q * n) = n := by
  obtain ⟨t, rfl⟩ := hnm
  have hqt : Nat.Coprime t q := Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hq).mpr
    fun h ↦ hqnm (by rw [mul_comm q n]; exact mul_dvd_mul_left n h)
  rw [mul_comm q n, Nat.gcd_mul_left, hqt.gcd_eq_one, mul_one]

/-- If `n ∣ m` and `q * n ∤ m` for a prime `q`, then `lcm m (q * n) = q * m`. -/
theorem Nat.Prime.lcm_mul_eq_of_dvd_of_not_mul_dvd {q n m : ℕ} (hq : q.Prime) (hnm : n ∣ m)
    (hqnm : ¬q * n ∣ m) : Nat.lcm m (q * n) = q * m := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hqnm (by simpa using hnm)
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) ?_
  have := Nat.gcd_mul_lcm m (q * n)
  rw [hq.gcd_mul_eq_of_dvd_of_not_mul_dvd hnm hqnm] at this
  rw [this, Nat.mul_left_comm, Nat.mul_comm m, Nat.mul_left_comm]

namespace Nat

/-- A prime dividing both a positive-index difference of powers and the product of the
bases divides their gcd. The inequality prevents truncation of natural subtraction. -/
theorem Prime.dvd_gcd_of_dvd_pow_sub_pow_of_dvd_mul {p : ℕ} (hp : p.Prime)
    {a b n : ℕ} (hba : b ≤ a) (hn : 0 < n) (hdiv : p ∣ a ^ n - b ^ n)
    (hmul : p ∣ a * b) : p ∣ a.gcd b := by
  have hle := Nat.pow_le_pow_left hba n
  rcases hp.dvd_mul.mp hmul with ha | hb
  · exact Nat.dvd_gcd ha (hp.dvd_of_dvd_pow
      ((Nat.dvd_sub_iff_right hle (ha.pow hn.ne')).mp hdiv))
  · exact Nat.dvd_gcd (hp.dvd_of_dvd_pow
      ((Nat.dvd_sub_iff_left hle (hb.pow hn.ne')).mp hdiv)) hb

/-- A prime divisor of a positive-index difference of powers of coprime bases divides
neither base. The inequality prevents truncation of natural subtraction. -/
theorem Coprime.not_dvd_mul_of_dvd_pow_sub_pow {a b n p : ℕ} (hab : a.Coprime b)
    (hp : p.Prime) (hba : b ≤ a) (hn : 0 < n) (hdiv : p ∣ a ^ n - b ^ n) :
    ¬ p ∣ a * b := by
  intro hmul
  have h := hp.dvd_gcd_of_dvd_pow_sub_pow_of_dvd_mul hba hn hdiv hmul
  rw [hab.gcd_eq_one] at h
  exact hp.not_dvd_one h

/-- Every prime distinct from a prime `p` is coprime to `p ^ k`. -/
theorem Prime.coprime_pow_of_prime_ne {p : ℕ} (hp : p.Prime) (k : ℕ) (q : ℕ)
    (hq : q.Prime) (hqp : q ≠ p) : q.Coprime (p ^ k) :=
  ((coprime_primes hq hp).mpr hqp).pow_right k

/-- For a prime `p`, a natural number `k` has no prime divisor distinct from `p` if and only if
`k` is a power of `p`. -/
theorem forall_prime_ne_not_dvd_iff_exists_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (∀ q : ℕ, q.Prime → q ≠ p → ¬ q ∣ k) ↔ ∃ m : ℕ, p ^ m = k := by
  constructor
  · intro hk
    rcases eq_or_ne k 0 with rfl | hk0
    · by_cases hp2 : 2 = p
      · exact False.elim (hk 3 prime_three (by omega) (dvd_zero 3))
      · exact False.elim (hk 2 prime_two hp2 (dvd_zero 2))
    · exact ⟨_, (eq_prime_pow_of_unique_prime_dvd hk0
        fun hd hdk ↦ by_contra fun hne ↦ hk _ hd hne hdk).symm⟩
  · rintro ⟨m, rfl⟩ q hq hqp hqd
    exact hqp (prime_eq_prime_of_dvd_pow hq hp hqd)

/-- For a prime `p`, a natural number `k` is divisible by some prime `q ≠ p` if and only if `k`
is not a power of `p`. -/
theorem exists_prime_ne_dvd_iff_forall_pow_ne {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k) ↔ ∀ m : ℕ, p ^ m ≠ k := by
  simpa only [not_forall, not_imp, Classical.not_not, not_exists, exists_prop] using
    (forall_prime_ne_not_dvd_iff_exists_pow hp k).not

end Nat
