/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.Data.Nat.Prime.Basic

/-!
# Primitive prime divisors and multiplicative orders

A prime not dividing the denominator divides a difference of powers exactly when the
multiplicative order of the ratio of the bases divides the exponent. For coprime natural
bases, a prime divisor is primitive exactly when that order equals the exponent. In
particular, a primitive prime divisor at exponent `n` is congruent to `1` modulo `n`
and is larger than `n`.

The integer criterion needs no ordering of the bases. Its natural-number version assumes
`b ≤ a`, so that subtraction does not truncate. Only the denominator must be nonzero
modulo the prime for the criterion itself; nonvanishing of both bases is needed for the
positive-order conclusion. Both divisibility criteria include exponent zero.

## References

* G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of aⁿ − bⁿ*,
  Annals of Mathematics (2) 5 (1904), 173–180, Theorem I.
* M. Roitman, *On Zsigmondy primes*, Proceedings of the American Mathematical Society
  125 (1997), 1913–1919, p. 1913.
-/

public section

namespace Nat.Prime

/-- For a prime `p` not dividing `b`, `p` divides `a ^ k - b ^ k` iff the order of
`a * b⁻¹` in `ZMod p` divides `k`. No ordering of the integer bases is needed.
The inverse in the conclusion is `ZMod.inv`, so the statement needs no primality instance. -/
theorem int_dvd_pow_sub_pow_iff_orderOf_dvd {p : ℕ} (hp : p.Prime)
    {a b : ℤ} (hb : ¬ (p : ℤ) ∣ b) (k : ℕ) :
    (p : ℤ) ∣ a ^ k - b ^ k ↔
      orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ k := by
  let : Fact p.Prime := ⟨hp⟩
  have hb0 : (b : ZMod p) ≠ 0 :=
    fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, orderOf_dvd_iff_pow_eq_one]
  push_cast
  simp [← div_eq_mul_inv, div_pow, div_eq_one_iff_eq (pow_ne_zero k hb0), sub_eq_zero]

/-- A prime divides a natural difference of powers exactly at multiples of the order of
the ratio modulo that prime. Only the denominator is required to be prime to `p`. -/
theorem dvd_pow_sub_pow_iff_orderOf_dvd {p : ℕ} (hp : p.Prime)
    {a b : ℕ} (hba : b ≤ a) (hb : ¬ p ∣ b) (k : ℕ) :
    p ∣ a ^ k - b ^ k ↔
      orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ k := by
  have hb' : ¬ (p : ℤ) ∣ (b : ℤ) := fun h => hb (Int.natCast_dvd_natCast.mp h)
  rw [← Int.natCast_dvd_natCast, Nat.cast_sub (Nat.pow_le_pow_left hba k),
    Nat.cast_pow, Nat.cast_pow]
  simpa only [Int.cast_natCast] using
    hp.int_dvd_pow_sub_pow_iff_orderOf_dvd (a := (a : ℤ)) hb' k

/-- The order of the ratio of two bases prime to `p` divides `p - 1`. -/
theorem orderOf_ratio_dvd_sub_one {p : ℕ} (hp : p.Prime)
    {a b : ℕ} (hab : ¬ p ∣ a * b) :
    orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ p - 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have ha : (a : ZMod p) ≠ 0 := fun h =>
    hab (dvd_mul_of_dvd_left ((ZMod.natCast_eq_zero_iff a p).mp h) b)
  have hb : (b : ZMod p) ≠ 0 := fun h =>
    hab (dvd_mul_of_dvd_right ((ZMod.natCast_eq_zero_iff b p).mp h) a)
  exact ZMod.orderOf_dvd_card_sub_one (mul_ne_zero ha (inv_ne_zero hb))

/-- If neither base vanishes modulo a prime, the order of their ratio is positive. -/
theorem orderOf_ratio_pos {p : ℕ} (hp : p.Prime)
    {a b : ℕ} (hab : ¬ p ∣ a * b) :
    0 < orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) :=
  Nat.pos_of_dvd_of_pos (hp.orderOf_ratio_dvd_sub_one hab)
    (Nat.sub_pos_of_lt hp.one_lt)

/-- If a prime not dividing `b` is primitive at positive exponent `n`, then the ratio of
bases has order `n` modulo that prime. The inequality prevents truncated subtraction. -/
theorem orderOf_ratio_eq_of_primitive {p : ℕ} (hp : p.Prime)
    {a b n : ℕ} (hba : b ≤ a) (hb : ¬ p ∣ b) (hn : 0 < n)
    (hdiv : p ∣ a ^ n - b ^ n)
    (hprev : ∀ k, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k) :
    orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n := by
  refine (orderOf_eq_iff hn).2 ⟨?_, ?_⟩
  · exact orderOf_dvd_iff_pow_eq_one.mp
      ((hp.dvd_pow_sub_pow_iff_orderOf_dvd hba hb n).mp hdiv)
  · intro k hkn hk hpow
    exact hprev k hk hkn
      ((hp.dvd_pow_sub_pow_iff_orderOf_dvd hba hb k).mpr
        (orderOf_dvd_of_pow_eq_one hpow))

/-- For coprime bases, a prime is primitive at exponent `n` exactly when the ratio of
the bases has order `n` modulo that prime. Primitivity is stated directly, not as a predicate. -/
theorem primitive_divisor_iff_orderOf_eq {p : ℕ} (hp : p.Prime)
    {a b n : ℕ} (hab : a.Coprime b) (hba : b ≤ a) (hn : 0 < n) :
    (p ∣ a ^ n - b ^ n ∧ ∀ k, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k) ↔
      ¬ p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n := by
  constructor
  · rintro ⟨hdiv, hprev⟩
    have hprod := hab.not_dvd_mul_of_dvd_pow_sub_pow hp hba hn hdiv
    have hb : ¬ p ∣ b := fun h => hprod (dvd_mul_of_dvd_right h a)
    exact ⟨hprod, hp.orderOf_ratio_eq_of_primitive hba hb hn hdiv hprev⟩
  · rintro ⟨hprod, horder⟩
    have hb : ¬ p ∣ b := fun h => hprod (dvd_mul_of_dvd_right h a)
    refine ⟨(hp.dvd_pow_sub_pow_iff_orderOf_dvd hba hb n).mpr
      (horder ▸ dvd_refl n), ?_⟩
    intro k hk hkn hdiv
    have hnk : n ∣ k := horder ▸
      (hp.dvd_pow_sub_pow_iff_orderOf_dvd hba hb k).mp hdiv
    exact (not_le_of_gt hkn) (Nat.le_of_dvd hk hnk)

/-- The exponent of a primitive prime divisor divides one less than that prime. -/
theorem dvd_sub_one_of_primitive {p : ℕ} (hp : p.Prime)
    {a b n : ℕ} (hn : 0 < n) (hdiv : p ∣ a ^ n - b ^ n)
    (hprev : ∀ k, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k) : n ∣ p - 1 := by
  by_cases hn1 : n = 1
  · simp [hn1]
  have h1 : ¬ p ∣ a - b := by
    simpa using hprev 1 (by omega) (by omega)
  have hba : b ≤ a := by
    by_contra h
    exact h1 (by simp [Nat.sub_eq_zero_of_le (by omega : a ≤ b)])
  have hprod : ¬ p ∣ a * b := by
    intro hmul
    have h := hp.dvd_gcd_of_dvd_pow_sub_pow_of_dvd_mul hba hn hdiv hmul
    exact h1 (Nat.dvd_sub (h.trans (Nat.gcd_dvd_left a b))
      (h.trans (Nat.gcd_dvd_right a b)))
  have hb : ¬ p ∣ b := fun h => hprod (dvd_mul_of_dvd_right h a)
  have horder := hp.orderOf_ratio_eq_of_primitive hba hb hn hdiv hprev
  simpa only [horder] using hp.orderOf_ratio_dvd_sub_one hprod

/-- A primitive prime divisor is strictly larger than its exponent. -/
theorem exponent_lt_of_primitive {p : ℕ} (hp : p.Prime)
    {a b n : ℕ} (hdiv : p ∣ a ^ n - b ^ n)
    (hprev : ∀ k, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k) : n < p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hp.pos
  have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt)
    (hp.dvd_sub_one_of_primitive hn hdiv hprev)
  omega

end Nat.Prime
