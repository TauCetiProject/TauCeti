/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Natural casts and `p`-power maps in exponential characteristic `p`

In an additive monoid with one of exponential characteristic `p`, the natural-number cast of
`p ^ n` vanishes whenever `1 < p ^ n`, and `1 < p` as soon as `p ≠ 1`. In an additive monoid with
one in which `1 ≠ 0` some prime, `2` or `3`, has a nonzero cast; this is how one picks a prime `ℓ`
different from the characteristic of a field. In a nontrivial ring only the characteristic can
vanish among the primes, so there are arbitrarily large primes with nonzero cast. A natural number
prime to the characteristic of a nontrivial ring is nonzero; conversely, when the characteristic
is prime, a natural number with nonzero cast is prime to it. A ring map from a ring of prime
characteristic `p` to a nontrivial ring shows that the target has characteristic `p` as well. In
characteristic a prime `p`, the binomial coefficient `(p - 1).choose k` is `(-1) ^ k` for
`k ≤ p - 1`. In characteristic `p`, the natural-number representative of the inverse of `m` modulo
`p` inverts the cast of `m` when `m` is prime to `p`, so in a semiring of characteristic a prime
`p` every natural number prime to `p` is a unit; Mathlib's `CharP.isUnit_natCast_iff` states this
for rings. Consequently, a ring without zero divisors in which some natural number is a nonzero
nonunit has characteristic zero.

In a ring of exponential characteristic `p`, raising to the power `q = p ^ n` commutes with
negation. Mathlib records the special case `(-1) ^ q = -1` (`neg_one_pow_expChar_pow`) and the
additive laws `add_pow_expChar_pow` and `sub_pow_expChar_pow`; this file adds the general negation
law.

## Main results

* `TauCeti.one_lt_expChar_of_ne_one`: an exponential characteristic other than one exceeds one.
* `TauCeti.natCast_pow_expChar_eq_zero`: the natural-number cast of `p ^ n` vanishes when
  `1 < p ^ n`.
* `TauCeti.exists_prime_natCast_ne_zero`: if `1 ≠ 0`, some prime has nonzero cast.
* `TauCeti.exists_prime_lt_natCast_ne_zero`: in a nontrivial ring, arbitrarily large primes have
  nonzero cast.
* `TauCeti.ne_zero_of_coprime_ringChar`: a natural number prime to the characteristic of a
  nontrivial ring is nonzero.
* `TauCeti.coprime_ringChar_of_natCast_ne_zero`: when the characteristic is prime, a natural
  number with nonzero cast is prime to it.
* `TauCeti.charP_of_ringHom_of_prime`: a nontrivial ring receiving a ring map from a ring of prime
  characteristic `p` has characteristic `p`.
* `TauCeti.natCast_choose_sub_one_eq_neg_one_pow`: `(p - 1).choose k = (-1) ^ k` in
  characteristic `p`.
* `TauCeti.natCast_mul_natCast_val_inv_eq_one`: `m * (m⁻¹ : ZMod p).val = 1` in characteristic
  `p` when `m` is prime to `p`.
* `TauCeti.isUnit_natCast_of_not_dvd`: in a semiring of characteristic a prime `p`, a natural
  number prime to `p` is a unit.
* `TauCeti.charZero_of_natCast_ne_zero_of_not_isUnit`: a ring without zero divisors in which some
  natural number is a nonzero nonunit has characteristic zero.
* `TauCeti.neg_pow_expChar_pow`: `(-x) ^ p ^ n = -x ^ p ^ n`.
-/

public section

namespace TauCeti

/-- An exponential characteristic other than one is greater than one, since it is then prime. -/
theorem one_lt_expChar_of_ne_one (R : Type*) [AddMonoidWithOne R] {p : ℕ} [ExpChar R p]
    (hp : p ≠ 1) : 1 < p :=
  ((expChar_is_prime_or_one R p).resolve_right hp).one_lt

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

/-- When the characteristic of a semiring is prime, a natural number with nonzero cast is prime to
it. -/
theorem coprime_ringChar_of_natCast_ne_zero {R : Type*} [NonAssocSemiring R]
    (hp : (ringChar R).Prime) {m : ℕ} (hm : (m : R) ≠ 0) : m.Coprime (ringChar R) :=
  (hp.coprime_iff_not_dvd.2 fun h ↦ hm ((ringChar.spec R m).2 h)).symm

/-- A nontrivial ring receiving a ring map from a ring of prime characteristic `p` has
characteristic `p`: the image of `p` vanishes, and only the characteristic can vanish among the
primes. -/
theorem charP_of_ringHom_of_prime {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [Nontrivial S] (f : R →+* S) (p : ℕ) [Fact p.Prime] [CharP R p] : CharP S p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).2 <| by
    rw [← map_natCast f, CharP.cast_eq_zero, map_zero]

/-- **Arbitrarily large primes have nonzero cast** in a nontrivial ring: a prime with zero cast is
divisible by the characteristic, so it is the characteristic. -/
theorem exists_prime_lt_natCast_ne_zero (R : Type*) [NonAssocSemiring R] [Nontrivial R] (m : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ m < ℓ ∧ (ℓ : R) ≠ 0 := by
  obtain ⟨ℓ, hle, hℓ⟩ := Nat.exists_infinite_primes (m + ringChar R + 1)
  refine ⟨ℓ, hℓ, by omega, fun h ↦ ?_⟩
  rcases hℓ.eq_one_or_self_of_dvd _ ((ringChar.spec R ℓ).mp h) with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

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

/-- In a semiring of characteristic a prime `p`, a natural number prime to `p` is a unit. This is
the semiring version of one direction of Mathlib's `CharP.isUnit_natCast_iff`, which needs a
ring. -/
theorem isUnit_natCast_of_not_dvd {R : Type*} [Semiring R] {p : ℕ} [CharP R p] (hp : p.Prime)
    {n : ℕ} (hn : ¬p ∣ n) : IsUnit (n : R) := by
  have h := natCast_mul_natCast_val_inv_eq_one (R := R) p ((hp.coprime_iff_not_dvd.2 hn).symm)
  exact ⟨⟨n, _, h, (Nat.cast_commute _ _).eq.symm.trans h⟩, rfl⟩

/-- A ring without zero divisors in which some natural number is a nonzero nonunit has
characteristic zero: in prime characteristic every nonzero natural number is prime to the
characteristic and hence a unit (`TauCeti.isUnit_natCast_of_not_dvd`). -/
theorem charZero_of_natCast_ne_zero_of_not_isUnit {R : Type*} [Ring R] [NoZeroDivisors R]
    {n : ℕ} (h0 : (n : R) ≠ 0) (hu : ¬IsUnit (n : R)) : CharZero R := by
  have : Nontrivial R := nontrivial_of_ne _ _ h0
  rcases CharP.char_is_prime_or_zero R (ringChar R) with hp | hp0
  · exact absurd (isUnit_natCast_of_not_dvd hp (mt (ringChar.spec R n).mpr h0)) hu
  · have := ringChar.of_eq hp0
    exact CharP.charP_to_charZero R

variable {R : Type*} [Ring R] (p n : ℕ) [ExpChar R p]

/-- Raising to the power `q = p ^ n` commutes with negation in exponential characteristic `p`. -/
theorem neg_pow_expChar_pow (x : R) : (-x) ^ p ^ n = -x ^ p ^ n := by
  rw [neg_pow, neg_one_pow_expChar_pow, neg_one_mul]

end TauCeti
