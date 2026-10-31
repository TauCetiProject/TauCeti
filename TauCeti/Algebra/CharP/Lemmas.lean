/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas

/-!
# Natural casts and `p`-power maps in exponential characteristic `p`

In an additive monoid with one of exponential characteristic `p`, the natural-number cast of
`p ^ n` vanishes whenever `1 < p ^ n`. If an integer is not divisible by `p`, then `1 < p`. In an
additive monoid with one in which `1 ≠ 0` some prime, `2` or `3`, has a nonzero cast; this is how
one picks a prime `ℓ` different from the characteristic of a field. In a nontrivial ring only the
characteristic can vanish among the primes, so there are arbitrarily large primes with nonzero
cast.

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

/-- **Arbitrarily large primes have nonzero cast** in a nontrivial ring: a prime with zero cast is
divisible by the characteristic, so it is the characteristic. -/
theorem exists_prime_lt_natCast_ne_zero (R : Type*) [NonAssocSemiring R] [Nontrivial R] (m : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ m < ℓ ∧ (ℓ : R) ≠ 0 := by
  obtain ⟨ℓ, hle, hℓ⟩ := Nat.exists_infinite_primes (m + ringChar R + 1)
  refine ⟨ℓ, hℓ, by omega, fun h ↦ ?_⟩
  rcases hℓ.eq_one_or_self_of_dvd _ ((ringChar.spec R ℓ).mp h) with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

variable {R : Type*} [Ring R] (p n : ℕ) [ExpChar R p]

/-- Raising to the power `q = p ^ n` commutes with negation in exponential characteristic `p`. -/
theorem neg_pow_expChar_pow (x : R) : (-x) ^ p ^ n = -x ^ p ^ n := by
  rw [neg_pow, neg_one_pow_expChar_pow, neg_one_mul]

end TauCeti
