/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Natural casts and `p`-power maps in exponential characteristic `p`

In an additive monoid with one of exponential characteristic `p`, the natural-number cast of
`p ^ n` vanishes whenever `1 < p ^ n`. If an integer is not divisible by `p`, then `1 < p`. In an
additive monoid with one in which `1 ≠ 0` some prime, `2` or `3`, has a nonzero cast; this is how
one picks a prime `ℓ` different from the characteristic of a field. In a nontrivial ring only the
characteristic can vanish among the primes, so there are arbitrarily large primes with nonzero
cast. Without zero divisors, `4` is nonzero whenever `2` is. A natural number prime to the
characteristic of a nontrivial ring is nonzero. In characteristic a prime `p`, the binomial
coefficient `(p - 1).choose k` is `(-1) ^ k` for `k ≤ p - 1`. In characteristic `p`, the
natural-number representative of the inverse of `m` modulo `p` inverts the cast of `m` when `m` is
prime to `p`.

In a ring of exponential characteristic `p`, raising to the power `q = p ^ n` commutes with
negation. Mathlib records the special case `(-1) ^ q = -1` (`neg_one_pow_expChar_pow`) and the
additive laws `add_pow_expChar_pow` and `sub_pow_expChar_pow`; this file adds the general negation
law.

## Main results

* `TauCeti.one_lt_expChar_of_not_dvd`: nondivisibility by the exponential characteristic
  forces it to exceed one.
* `TauCeti.natCast_pow_expChar_eq_zero`: the natural-number cast of `p ^ n` vanishes when
  `1 < p ^ n`.
* `TauCeti.exists_prime_natCast_ne_zero`: if `1 ≠ 0`, some prime has nonzero cast.
* `TauCeti.exists_prime_lt_natCast_ne_zero`: in a nontrivial ring, arbitrarily large primes have
  nonzero cast.
* `TauCeti.four_ne_zero_of_two_ne_zero`: without zero divisors, `2 ≠ 0` implies `4 ≠ 0`.
* `TauCeti.ne_zero_of_coprime_ringChar`: a natural number prime to the characteristic of a
  nontrivial ring is nonzero.
* `TauCeti.natCast_choose_sub_one_eq_neg_one_pow`: `(p - 1).choose k = (-1) ^ k` in
  characteristic `p`.
* `TauCeti.natCast_mul_natCast_val_inv_eq_one`: `m * (m⁻¹ : ZMod p).val = 1` in characteristic
  `p` when `m` is prime to `p`.
* `TauCeti.neg_pow_expChar_pow`: `(-x) ^ p ^ n = -x ^ p ^ n`.
-/

public section

namespace TauCeti

/-- An exponential characteristic that does not divide an integer is greater than one. -/
theorem one_lt_expChar_of_not_dvd (R : Type*) [AddMonoidWithOne R] {p : ℕ} [ExpChar R p]
    {n : ℤ} (h : ¬(p : ℤ) ∣ n) : 1 < p := by
  rcases expChar_is_prime_or_one R p with hp | rfl
  · exact hp.one_lt
  · exact (h (one_dvd _)).elim

/-- In an additive monoid with one of exponential characteristic `p`, the natural-number cast
of `p ^ n` vanishes whenever `1 < p ^ n`. -/
theorem natCast_pow_expChar_eq_zero {R : Type*} [AddMonoidWithOne R] {p n : ℕ} [ExpChar R p]
    (hq : 1 < p ^ n) : ((p ^ n : ℕ) : R) = 0 := by
  have hn : n ≠ 0 := by rintro rfl; simp at hq
  rcases ‹ExpChar R p› with _ | hp
  · simp at hq
  · exact (CharP.cast_eq_zero_iff R p (p ^ n)).2 (dvd_pow_self p hn)

/-- **Some prime has nonzero cast** in an additive monoid with one in which `1 ≠ 0`, such as a
field: if `2` vanishes, then `3 = 2 + 1` does not. -/
theorem exists_prime_natCast_ne_zero (R : Type*) [AddMonoidWithOne R] [NeZero (1 : R)] :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : R) ≠ 0 := by
  by_cases h2 : ((2 : ℕ) : R) = 0
  · refine ⟨3, Nat.prime_three, fun h3 ↦ one_ne_zero (α := R) ?_⟩
    simpa only [h2, zero_add] using (Nat.cast_succ (R := R) 2).symm.trans h3
  · exact ⟨2, Nat.prime_two, h2⟩

/-- A natural number prime to the characteristic of a nontrivial ring is nonzero. -/
theorem ne_zero_of_coprime_ringChar {R : Type*} [NonAssocSemiring R] [Nontrivial R] {m : ℕ}
    (hm : m.Coprime (ringChar R)) : m ≠ 0 := by
  rintro rfl
  exact CharP.ringChar_ne_one (Nat.coprime_zero_left _ |>.1 hm)

/-- **Arbitrarily large primes have nonzero cast** in a nontrivial ring: a prime with zero cast is
divisible by the characteristic, so it is the characteristic. -/
theorem exists_prime_lt_natCast_ne_zero (R : Type*) [NonAssocSemiring R] [Nontrivial R] (m : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ m < ℓ ∧ (ℓ : R) ≠ 0 := by
  obtain ⟨ℓ, hle, hℓ⟩ := Nat.exists_infinite_primes (m + ringChar R + 1)
  refine ⟨ℓ, hℓ, by omega, fun h ↦ ?_⟩
  rcases hℓ.eq_one_or_self_of_dvd _ ((ringChar.spec R ℓ).mp h) with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

/-- In a semiring without zero divisors, such as a field, `4 = 2 * 2` is nonzero when `2` is. -/
theorem four_ne_zero_of_two_ne_zero {R : Type*} [NonAssocSemiring R] [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0) : (4 : R) ≠ 0 := by
  rw [← two_add_two_eq_four, ← two_mul]
  exact mul_ne_zero h2 h2

/-- In characteristic a prime `p`, the binomial coefficient `(p - 1).choose k` is `(-1) ^ k` for
every `k ≤ p - 1`: consecutive coefficients add up to `p.choose (k + 1)`, which vanishes. -/
theorem natCast_choose_sub_one_eq_neg_one_pow {R : Type*} [Ring R] (p : ℕ) [hp : Fact p.Prime]
    [CharP R p] {k : ℕ} (hk : k ≤ p - 1) : (((p - 1).choose k : ℕ) : R) = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsum : (((p - 1).choose (k + 1) : ℕ) : R) + ((p - 1).choose k : ℕ) = 0 := by
      have h := Nat.choose_succ_succ' (p - 1) k
      rw [Nat.sub_add_cancel hp.out.one_le] at h
      rw [← Nat.cast_add, add_comm, ← h, CharP.cast_eq_zero_iff R p]
      exact hp.out.dvd_choose_self (by omega) (by omega)
    rw [eq_neg_of_add_eq_zero_left hsum, ih (by omega), pow_succ, mul_neg_one]

/-- In characteristic `p`, the natural-number representative `(m⁻¹ : ZMod p).val` of the inverse
of `m` modulo `p` is a right inverse of `m` whenever `m` is prime to `p`. -/
theorem natCast_mul_natCast_val_inv_eq_one {R : Type*} [NonAssocSemiring R] (p : ℕ) [CharP R p]
    {m : ℕ} (hm : m.Coprime p) : (m : R) * ((m⁻¹ : ZMod p).val : R) = 1 := by
  rw [← Nat.cast_mul, ← Nat.cast_one]
  exact CharP.natCast_eq_natCast' R p
    ((ZMod.natCast_eq_natCast_iff _ _ _).1 (by push_cast; exact ZMod.mul_val_inv hm))

variable {R : Type*} [Ring R] (p n : ℕ) [ExpChar R p]

/-- Raising to the power `q = p ^ n` commutes with negation in exponential characteristic `p`. -/
theorem neg_pow_expChar_pow (x : R) : (-x) ^ p ^ n = -x ^ p ^ n := by
  rw [neg_pow, neg_one_pow_expChar_pow, neg_one_mul]

end TauCeti
