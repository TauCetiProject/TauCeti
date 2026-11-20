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
modulo the prime for the criterion itself; the ratio has positive order modulo `p` iff neither
base vanishes modulo `p`. Both divisibility criteria include exponent zero. At an even exponent
`2 * n` (`0 < n`), `a ^ (2 * n) - b ^ (2 * n) = (a ^ n + b ^ n) * (a ^ n - b ^ n)` identifies
primitive prime divisors of `a ^ (2 * n) - b ^ (2 * n)` with primes dividing `a ^ n + b ^ n` and
no `a ^ k - b ^ k` for `0 < k < 2 * n`, and for `b ≤ a` (without coprimality) with primes not
dividing `a * b` at which `a / b` has order `2 * n`.

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

/-- A prime does not divide the order of the ratio of two bases nonzero modulo it. -/
theorem not_dvd_orderOf_ratio {p : ℕ} (hp : p.Prime)
    {a b : ℕ} (hab : ¬ p ∣ a * b) :
    ¬ p ∣ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) :=
  fun h => Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt)
    (Nat.sub_lt hp.pos one_pos) (h.trans (hp.orderOf_ratio_dvd_sub_one hab))

/-- If neither base vanishes modulo a prime, the order of their ratio is positive. -/
theorem orderOf_ratio_pos {p : ℕ} (hp : p.Prime)
    {a b : ℕ} (hab : ¬ p ∣ a * b) :
    0 < orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) :=
  Nat.pos_of_dvd_of_pos (hp.orderOf_ratio_dvd_sub_one hab)
    (Nat.sub_pos_of_lt hp.one_lt)

/-- Modulo a prime `p`, the ratio `a / b` has positive order iff `p` divides neither base. The
hypothesis `p.Prime` is sharp: `p = 0`, `p = 1` and `p = 10` (at `a = 1`, `b = 4`) each fail one
direction. -/
theorem orderOf_ratio_pos_iff {p : ℕ} (hp : p.Prime) {a b : ℕ} :
    0 < orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ↔ ¬ p ∣ a * b := by
  refine ⟨fun hpos hmul => hpos.ne' ?_, hp.orderOf_ratio_pos⟩
  let : Fact p.Prime := ⟨hp⟩
  rcases hp.dvd_mul.1 hmul with ha | hb
  · rw [(ZMod.natCast_eq_zero_iff a p).2 ha, zero_mul, orderOf_zero]
  · rw [(ZMod.natCast_eq_zero_iff b p).2 hb, inv_zero, mul_zero, orderOf_zero]

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

/-- If `a / b` has order `n` modulo a prime `p` and `b ≤ a`, then `p` divides `a ^ n - b ^ n` and
none of `a ^ k - b ^ k` for `0 < k < n`. Neither coprimality nor `0 < n` is needed: at `n = 0`,
`a ^ 0 - b ^ 0 = 0`, and for `0 < n` positivity of the order forces `¬ p ∣ a * b`. -/
theorem primitive_divisor_of_orderOf_eq {p : ℕ} (hp : p.Prime)
    {a b n : ℕ} (hba : b ≤ a) (horder : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n) :
    p ∣ a ^ n - b ^ n ∧ ∀ k, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hprod : ¬ p ∣ a * b := hp.orderOf_ratio_pos_iff.mp (horder ▸ hn)
  have hb : ¬ p ∣ b := fun hb => hprod (dvd_mul_of_dvd_right hb a)
  refine ⟨(hp.dvd_pow_sub_pow_iff_orderOf_dvd hba hb n).mpr (horder ▸ dvd_rfl), ?_⟩
  intro k hk hkn hdiv
  exact (not_le_of_gt hkn) (Nat.le_of_dvd hk
    (horder ▸ (hp.dvd_pow_sub_pow_iff_orderOf_dvd hba hb k).mp hdiv))

/-- For coprime bases, a prime is primitive at exponent `n` exactly when the ratio of
the bases has order `n` modulo that prime. Primitivity is stated directly, not as a predicate. -/
theorem primitive_divisor_iff_orderOf_eq {p : ℕ} (hp : p.Prime)
    {a b n : ℕ} (hab : a.Coprime b) (hba : b ≤ a) (hn : 0 < n) :
    (p ∣ a ^ n - b ^ n ∧ ∀ k, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k) ↔
      ¬ p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n := by
  refine ⟨?_, fun ⟨_, horder⟩ => hp.primitive_divisor_of_orderOf_eq hba horder⟩
  rintro ⟨hdiv, hprev⟩
  have hprod := hab.not_dvd_mul_of_dvd_pow_sub_pow hp hba hn hdiv
  have hb : ¬ p ∣ b := fun h => hprod (dvd_mul_of_dvd_right h a)
  exact ⟨hprod, hp.orderOf_ratio_eq_of_primitive hba hb hn hdiv hprev⟩

/-- For bases `b ≤ a` and `2 ≤ n` (without coprimality), a prime `p` is primitive for
`a ^ n - b ^ n` iff `p` divides neither base and `a / b` has order `n` modulo `p`. At `n = 1`
coprimality is needed: `3` divides `6 - 3` and `6 * 3`. -/
theorem primitive_divisor_iff_orderOf_eq_of_two_le {p : ℕ} (hp : p.Prime)
    {a b n : ℕ} (hba : b ≤ a) (hn : 2 ≤ n) :
    (p ∣ a ^ n - b ^ n ∧ ∀ k, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k) ↔
      ¬ p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n := by
  refine ⟨?_, fun ⟨_, horder⟩ => hp.primitive_divisor_of_orderOf_eq hba horder⟩
  rintro ⟨hdiv, hprev⟩
  have hprod : ¬ p ∣ a * b := by
    intro hmul
    have hg := hp.dvd_gcd_of_dvd_pow_sub_pow_of_dvd_mul hba (by omega) hdiv hmul
    have h1 : ¬ p ∣ a - b := by simpa using hprev 1 Nat.one_pos (by omega)
    exact h1 (Nat.dvd_sub (hg.trans (Nat.gcd_dvd_left a b))
      (hg.trans (Nat.gcd_dvd_right a b)))
  exact ⟨hprod, hp.orderOf_ratio_eq_of_primitive hba
    (fun hb => hprod (dvd_mul_of_dvd_right hb a)) (by omega) hdiv hprev⟩

/-- The exponent of a primitive prime divisor divides one less than that prime. -/
theorem dvd_sub_one_of_primitive {p : ℕ} (hp : p.Prime)
    {a b n : ℕ} (hn : 0 < n) (hdiv : p ∣ a ^ n - b ^ n)
    (hprev : ∀ k, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k) : n ∣ p - 1 := by
  by_cases hn1 : n = 1
  · simp [hn1]
  have hba : b ≤ a := by
    by_contra h
    have h1 : ¬ p ∣ a - b := by simpa using hprev 1 (by omega) (by omega)
    exact h1 (by simp [Nat.sub_eq_zero_of_le (by omega : a ≤ b)])
  obtain ⟨hprod, horder⟩ :=
    (hp.primitive_divisor_iff_orderOf_eq_of_two_le hba (by omega)).1 ⟨hdiv, hprev⟩
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

/-- For a prime `p` and positive `n`, dividing `a ^ n + b ^ n` and no `a ^ k - b ^ k` with
`0 < k < 2 * n` is equivalent to being a primitive prime divisor of `a ^ (2 * n) - b ^ (2 * n)`.
At `n = 0` this fails for every odd prime `p`: `¬ p ∣ a ^ 0 + b ^ 0 = 2`, while
`p ∣ a ^ 0 - b ^ 0 = 0`. -/
theorem dvd_pow_add_pow_and_not_dvd_iff {p : ℕ} (hp : p.Prime) {a b n : ℕ} (hn : 0 < n) :
    (p ∣ a ^ n + b ^ n ∧ ∀ k, 0 < k → k < 2 * n → ¬ p ∣ a ^ k - b ^ k) ↔
      (p ∣ a ^ (2 * n) - b ^ (2 * n) ∧ ∀ k, 0 < k → k < 2 * n → ¬ p ∣ a ^ k - b ^ k) := by
  have hsq : a ^ (2 * n) - b ^ (2 * n) = (a ^ n + b ^ n) * (a ^ n - b ^ n) := by
    rw [mul_comm 2 n, pow_mul, pow_mul, Nat.pow_two_sub_pow_two]
  refine ⟨fun ⟨hadd, hprev⟩ => ⟨hsq ▸ dvd_mul_of_dvd_left hadd _, hprev⟩,
    fun ⟨hsub, hprev⟩ => ⟨?_, hprev⟩⟩
  exact (hp.dvd_mul.1 (hsq ▸ hsub)).resolve_right (hprev n hn (by omega))

/-- For natural bases `b ≤ a` and `0 < n` (without coprimality), a prime `p` divides `a ^ n + b ^ n`
and no `a ^ k - b ^ k` with `0 < k < 2 * n` iff `p` divides neither base and `a / b` has order
`2 * n` modulo `p`. Divisibility of `a ^ n + b ^ n` alone does not force order `2 * n`:
`3 ∣ 2 ^ 3 + 1`, while `2` has order `2` modulo `3`. -/
theorem dvd_pow_add_pow_and_not_dvd_iff_orderOf_eq {p : ℕ} (hp : p.Prime)
    {a b n : ℕ} (hba : b ≤ a) (hn : 0 < n) :
    (p ∣ a ^ n + b ^ n ∧ ∀ k, 0 < k → k < 2 * n → ¬ p ∣ a ^ k - b ^ k) ↔
      ¬ p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = 2 * n :=
  (hp.dvd_pow_add_pow_and_not_dvd_iff hn).trans
    (hp.primitive_divisor_iff_orderOf_eq_of_two_le hba (by omega))

end Nat.Prime
