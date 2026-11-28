/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Rat.Floor
import TauCeti.Data.Nat.Factorization.Basic
public import TauCeti.Data.ZMod.CubeRootOfUnity
public import TauCeti.Data.ZMod.Thue

/-!
# Integers of the form `a² - ab + b²`

The quadratic form `a ^ 2 - a * b + b ^ 2` is the norm form of the Eisenstein integers `ℤ[ω]`,
`ω ^ 2 + ω + 1 = 0`: it is the norm of `a + b ω`. This file proves the analogue of Fermat's
two-square theorem for it: a natural number `n` is of the form `a ^ 2 - a * b + b ^ 2` with
integers `a` and `b` exactly when every prime `q ≡ 2 (mod 3)` divides `n` to an even power.

The proof is elementary and stays in `ℤ` and `ZMod p`.

* The form is multiplicative, by the identity expressing the product of the norms of `a + b ω`
  and `c + d ω`.
* A prime `q ≡ 2 (mod 3)` dividing `a ^ 2 - a * b + b ^ 2` divides both `a` and `b`: otherwise
  `-a / b` would be a root of `T ^ 2 + T + 1` in `ZMod q`, and there is none
  (`ZMod.exists_sq_add_add_one_eq_zero_iff`). Dividing out `q ^ 2` repeatedly shows that such a
  prime occurs to an even power.
* A prime `p ≢ 2 (mod 3)` is of this form: `ZMod p` contains a root `t` of `T ^ 2 + T + 1`, and
  Thue's lemma (`ZMod.exists_abs_le_sqrt_and_intCast_add_mul_eq_zero`) gives integers `a`, `b`,
  not both zero, of absolute value at most `√p` with `a + t b = 0` in `ZMod p`. Then `p` divides
  `a ^ 2 - a * b + b ^ 2`, which is positive and less than `3 p`, and the value `2 p` is excluded
  by the previous point.
* `q ^ 2` is of this form for every `q`.

## Main results

* `TauCeti.sq_sub_mul_add_sq_mul_sq_sub_mul_add_sq`: the form is multiplicative, over any
  commutative ring; `TauCeti.sq_sub_mul_add_sq_mul`: its values are closed under products.
* `Int.exists_quotient_remainder_sq_sub_mul_add_sq`: Euclidean division, with a remainder of norm
  at most `3 / 4` of the norm of the divisor.
* `Int.exists_four_mul_eq_sq_add_three_mul_sq_iff`: `m` is of the form `a ^ 2 - a * b + b ^ 2`
  exactly when `4 * m` is of the form `u ^ 2 + 3 * v ^ 2`.
* `Nat.Prime.dvd_and_dvd_of_dvd_sq_sub_mul_add_sq`: a prime `q ≡ 2 (mod 3)` dividing
  `a ^ 2 - a * b + b ^ 2` divides `a` and `b`.
* `Nat.Prime.exists_eq_sq_sub_mul_add_sq_iff`: a prime `p` is of the form
  `a ^ 2 - a * b + b ^ 2` if and only if `p % 3 ≠ 2`.
* `Nat.exists_eq_sq_sub_mul_add_sq_iff`: `n` is of the form `a ^ 2 - a * b + b ^ 2` exactly when
  every prime `q ≡ 2 (mod 3)` has even exponent in `n`.
-/

public section

open Finset

namespace TauCeti

section CommRing

variable {R : Type*} [CommRing R]

/-- The form `a ^ 2 - a * b + b ^ 2` is multiplicative: this is the multiplicativity of the norm
of `a + b ω` for a primitive cube root of unity `ω`. -/
theorem sq_sub_mul_add_sq_mul_sq_sub_mul_add_sq (a b c d : R) :
    (a ^ 2 - a * b + b ^ 2) * (c ^ 2 - c * d + d ^ 2) =
      (a * c - b * d) ^ 2 - (a * c - b * d) * (a * d + b * c - b * d) +
        (a * d + b * c - b * d) ^ 2 := by
  ring

/-- A product of two elements of the form `x ^ 2 - x * y + y ^ 2` is again of this form. -/
theorem sq_sub_mul_add_sq_mul {a b x y u v : R} (ha : a = x ^ 2 - x * y + y ^ 2)
    (hb : b = u ^ 2 - u * v + v ^ 2) : ∃ r s : R, a * b = r ^ 2 - r * s + s ^ 2 :=
  ⟨x * u - y * v, x * v + y * u - y * v, by
    rw [ha, hb, sq_sub_mul_add_sq_mul_sq_sub_mul_add_sq]⟩

/-- A power of an element of the form `x ^ 2 - x * y + y ^ 2` is again of this form. -/
theorem sq_sub_mul_add_sq_pow {a x y : R} (ha : a = x ^ 2 - x * y + y ^ 2) (k : ℕ) :
    ∃ r s : R, a ^ k = r ^ 2 - r * s + s ^ 2 := by
  induction k with
  | zero => exact ⟨1, 0, by ring⟩
  | succ k ih =>
    obtain ⟨r, s, hrs⟩ := ih
    rw [pow_succ]
    exact sq_sub_mul_add_sq_mul hrs ha

/-- Completing the square: `4 (a ^ 2 - a * b + b ^ 2) = (2 a - b) ^ 2 + 3 b ^ 2`. -/
theorem four_mul_sq_sub_mul_add_sq (a b : R) :
    4 * (a ^ 2 - a * b + b ^ 2) = (2 * a - b) ^ 2 + 3 * b ^ 2 := by
  ring

end CommRing

section LinearOrder

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The form `a ^ 2 - a * b + b ^ 2` is nonnegative. -/
theorem sq_sub_mul_add_sq_nonneg (a b : R) : 0 ≤ a ^ 2 - a * b + b ^ 2 := by
  nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]

/-- The form `a ^ 2 - a * b + b ^ 2` vanishes only at `a = b = 0`. -/
@[simp]
theorem sq_sub_mul_add_sq_eq_zero_iff {a b : R} : a ^ 2 - a * b + b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hb : b ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
    have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg (2 * b - a), sq_nonneg a]
    exact ⟨pow_eq_zero_iff two_ne_zero |>.1 ha, pow_eq_zero_iff two_ne_zero |>.1 hb⟩
  · rintro ⟨rfl, rfl⟩
    ring

end LinearOrder

end TauCeti

namespace Int

open TauCeti

/-- **Euclidean division for the form `a ^ 2 - a * b + b ^ 2`.** For integers `a`, `b` and
`(c, d) ≠ (0, 0)` there are a quotient `(q₁, q₂)` and a remainder `(r₁, r₂)` with
`a + b ω = (q₁ + q₂ ω) (c + d ω) + (r₁ + r₂ ω)`, written out in coordinates, and
`4 (r₁ ^ 2 - r₁ * r₂ + r₂ ^ 2) ≤ 3 (c ^ 2 - c * d + d ^ 2)`: the norm of the remainder is at most
`3 / 4` of the norm of the divisor. -/
theorem exists_quotient_remainder_sq_sub_mul_add_sq (a b : ℤ) {c d : ℤ} (hcd : c ≠ 0 ∨ d ≠ 0) :
    ∃ q₁ q₂ r₁ r₂ : ℤ, a = q₁ * c - q₂ * d + r₁ ∧ b = q₁ * d + q₂ * c - q₂ * d + r₂ ∧
      4 * (r₁ ^ 2 - r₁ * r₂ + r₂ ^ 2) ≤ 3 * (c ^ 2 - c * d + d ^ 2) := by
  have hN : (0 : ℚ) < (c : ℚ) ^ 2 - c * d + (d : ℚ) ^ 2 := by
    refine lt_of_le_of_ne (sq_sub_mul_add_sq_nonneg _ _) fun h ↦ ?_
    have h0 := sq_sub_mul_add_sq_eq_zero_iff.1 h.symm
    exact hcd.elim (fun hc ↦ hc (by exact_mod_cast h0.1)) fun hd ↦ hd (by exact_mod_cast h0.2)
  -- The exact quotient `x + y ω` in `ℚ(ω)`, rounded coordinatewise.
  obtain ⟨x, hx⟩ : ∃ x : ℚ, x = (a * c - a * d + b * d) / ((c : ℚ) ^ 2 - c * d + (d : ℚ) ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℚ, y = (b * c - a * d) / ((c : ℚ) ^ 2 - c * d + (d : ℚ) ^ 2) := ⟨_, rfl⟩
  have hxN : x * ((c : ℚ) ^ 2 - c * d + (d : ℚ) ^ 2) = a * c - a * d + b * d := by
    rw [hx, div_mul_cancel₀ _ hN.ne']
  have hyN : y * ((c : ℚ) ^ 2 - c * d + (d : ℚ) ^ 2) = b * c - a * d := by
    rw [hy, div_mul_cancel₀ _ hN.ne']
  have ha : (a : ℚ) = x * c - y * d :=
    mul_right_cancel₀ hN.ne' (by linear_combination (-(c : ℚ)) * hxN + (d : ℚ) * hyN)
  have hb : (b : ℚ) = x * d + y * c - y * d :=
    mul_right_cancel₀ hN.ne' (by linear_combination (-(d : ℚ)) * hxN + (-(c : ℚ) + d) * hyN)
  have hu := abs_le.1 (abs_sub_round x)
  have hv := abs_le.1 (abs_sub_round y)
  refine ⟨round x, round y, a - (round x * c - round y * d),
    b - (round x * d + round y * c - round y * d), by ring, by ring, ?_⟩
  -- The remainder is `(u + v ω) (c + d ω)` with `u = x - round x`, `v = y - round y`.
  have hmul := sq_sub_mul_add_sq_mul_sq_sub_mul_add_sq (x - round x) (y - round y) (c : ℚ) (d : ℚ)
  have hnorm : (x - round x) ^ 2 - (x - round x) * (y - round y) + (y - round y) ^ 2 ≤ 3 / 4 := by
    nlinarith [hu.1, hu.2, hv.1, hv.2]
  have hcast : (4 : ℚ) * (((a - (round x * c - round y * d) : ℤ) : ℚ) ^ 2 -
      ((a - (round x * c - round y * d) : ℤ) : ℚ) *
        ((b - (round x * d + round y * c - round y * d) : ℤ) : ℚ) +
      ((b - (round x * d + round y * c - round y * d) : ℤ) : ℚ) ^ 2) ≤
      3 * ((c : ℚ) ^ 2 - c * d + (d : ℚ) ^ 2) := by
    push_cast
    rw [ha, hb]
    nlinarith [mul_le_mul_of_nonneg_right hnorm hN.le, hmul]
  exact_mod_cast hcast

/-- **The shifted-witness criterion.** An integer `m` is of the form `a ^ 2 - a * b + b ^ 2`
exactly when `4 * m` is of the form `u ^ 2 + 3 * v ^ 2`: take `u = 2 a - b` and `v = b`, and
conversely `u` and `v` have the same parity, so `a = (u + v) / 2`, `b = v`. -/
theorem exists_four_mul_eq_sq_add_three_mul_sq_iff {m : ℤ} :
    (∃ u v : ℤ, 4 * m = u ^ 2 + 3 * v ^ 2) ↔ ∃ a b : ℤ, m = a ^ 2 - a * b + b ^ 2 := by
  constructor
  · rintro ⟨u, v, h⟩
    obtain ⟨s, rfl | rfl⟩ := Int.even_or_odd' u <;> obtain ⟨t, rfl | rfl⟩ := Int.even_or_odd' v
    · exact ⟨s + t, 2 * t, by linarith [four_mul_sq_sub_mul_add_sq (s + t) (2 * t)]⟩
    · ring_nf at h
      omega
    · ring_nf at h
      omega
    · exact ⟨s + t + 1, 2 * t + 1, by
        linarith [four_mul_sq_sub_mul_add_sq (s + t + 1) (2 * t + 1)]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨2 * a - b, b, four_mul_sq_sub_mul_add_sq a b⟩

end Int

namespace Nat

open TauCeti

/-- A prime `q ≡ 2 (mod 3)` dividing `a ^ 2 - a * b + b ^ 2` divides both `a` and `b`. -/
theorem Prime.dvd_and_dvd_of_dvd_sq_sub_mul_add_sq {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 2)
    {a b : ℤ} (h : (q : ℤ) ∣ a ^ 2 - a * b + b ^ 2) : (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b := by
  have : Fact q.Prime := ⟨hq⟩
  have hb : (q : ℤ) ∣ b := by
    by_contra hb
    have hb0 : (b : ZMod q) ≠ 0 := fun h0 ↦ hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b q).1 h0)
    have h0 : (a : ZMod q) ^ 2 - a * b + (b : ZMod q) ^ 2 = 0 := by
      have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 h
      push_cast at h'
      exact h'
    -- `t = -a / b` is a root of `T ^ 2 + T + 1`, and there is none for `q ≡ 2 (mod 3)`.
    obtain ⟨t, ht⟩ : ∃ t : ZMod q, t * b = -a := ⟨-a / b, div_mul_cancel₀ _ hb0⟩
    have hmul : (t ^ 2 + t + 1) * (b : ZMod q) ^ 2 = 0 := by
      linear_combination (t * b - a + b) * ht + h0
    exact ZMod.exists_sq_add_add_one_eq_zero_iff.1
      ⟨t, (_root_.mul_eq_zero.1 hmul).resolve_right (_root_.pow_ne_zero 2 hb0)⟩ hq3
  refine ⟨?_, hb⟩
  have ha2 : (q : ℤ) ∣ a ^ 2 := by
    have h' := _root_.dvd_sub h (hb.mul_left (b - a))
    have he : a ^ 2 - a * b + b ^ 2 - (b - a) * b = a ^ 2 := by ring
    rwa [he] at h'
  exact (Nat.prime_iff_prime_int.1 hq).dvd_of_dvd_pow ha2

/-- If `n = a ^ 2 - a * b + b ^ 2`, then every prime `q ≡ 2 (mod 3)` divides `n` to an even
power. Primality of `q` is not assumed, since `n.factorization q = 0` when `q` is not prime. -/
theorem even_factorization_of_eq_sq_sub_mul_add_sq {q : ℕ} (hq3 : q % 3 = 2)
    {n : ℕ} {a b : ℤ} (h : (n : ℤ) = a ^ 2 - a * b + b ^ 2) : Even (n.factorization q) := by
  by_cases hq : q.Prime
  swap
  · rw [Nat.factorization_eq_zero_of_not_prime n hq]
    exact Even.zero
  induction n using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    by_cases hqn : q ∣ n
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      have hdvd : (q : ℤ) ∣ a ^ 2 - a * b + b ^ 2 := by
        rw [← h]
        exact_mod_cast hqn
      obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := hq.dvd_and_dvd_of_dvd_sq_sub_mul_add_sq hq3 hdvd
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sq_sub_mul_add_sq_nonneg a' b')
      have hnm' : (n : ℤ) = ((q ^ 2 * m : ℕ) : ℤ) := by
        push_cast
        rw [h, ← hm]
        ring
      have hnm : n = q ^ 2 * m := by exact_mod_cast hnm'
      have hm0 : m ≠ 0 := by
        rintro rfl
        omega
      have hlt : m < n := by
        have h4 : 4 ≤ q ^ 2 := by nlinarith [hq.two_le]
        have := Nat.mul_le_mul_right m h4
        omega
      rw [hnm, hq.factorization_pow_mul_apply 2 hm0, ite_eq_left rfl]
      exact even_two.add (ih m hlt hm.symm)
    · rw [Nat.factorization_eq_zero_of_not_dvd hqn]
      exact Even.zero

/-- Every prime `p ≢ 2 (mod 3)` is of the form `a ^ 2 - a * b + b ^ 2`. -/
theorem Prime.exists_eq_sq_sub_mul_add_sq {p : ℕ} (hp : p.Prime) (hp3 : p % 3 ≠ 2) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 - a * b + b ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := ZMod.exists_sq_add_add_one_eq_zero_iff.2 hp3
  obtain ⟨a, b, hab, ha1, hb1, hmod⟩ := ZMod.exists_abs_le_sqrt_and_intCast_add_mul_eq_zero p t
  have hk : ((p.sqrt : ℤ)) ^ 2 < p := by
    have hk' : p.sqrt ^ 2 < p := by
      refine lt_of_le_of_ne (Nat.sqrt_le' p) fun hsq ↦ ?_
      exact Nat.Prime.not_prime_pow (le_refl 2) (hsq ▸ hp)
    exact_mod_cast hk'
  -- `p` divides `a ^ 2 - a * b + b ^ 2`, which is positive and less than `3 * p`.
  have hdvd : (p : ℤ) ∣ a ^ 2 - a * b + b ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination ((a : ZMod p) - t * b - b) * hmod + (b : ZMod p) ^ 2 * ht
  have hpos : 0 < a ^ 2 - a * b + b ^ 2 :=
    lt_of_le_of_ne (sq_sub_mul_add_sq_nonneg a b) fun h0 ↦ by
      have h0' := sq_sub_mul_add_sq_eq_zero_iff.1 h0.symm
      exact hab.elim (fun ha0 ↦ ha0 h0'.1) fun hb0 ↦ hb0 h0'.2
  have hlt : a ^ 2 - a * b + b ^ 2 < 3 * p := by
    have h1 : a ^ 2 ≤ (p.sqrt : ℤ) ^ 2 := sq_le_sq' (abs_le.1 ha1).1 (abs_le.1 ha1).2
    have h2 : b ^ 2 ≤ (p.sqrt : ℤ) ^ 2 := sq_le_sq' (abs_le.1 hb1).1 (abs_le.1 hb1).2
    have h3 : -(a * b) ≤ (p.sqrt : ℤ) ^ 2 := by
      have := abs_mul a b
      nlinarith [neg_abs_le (a * b), mul_le_mul ha1 hb1 (abs_nonneg b) (Int.natCast_nonneg _)]
    linarith [hk, h1, h2, h3]
  obtain ⟨c, hc⟩ := hdvd
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hc0 : 0 < c := by
    by_contra hc0
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hp0.le (not_lt.1 hc0)]
  have hc3 : c < 3 := by
    by_contra hc3
    nlinarith [mul_le_mul_of_nonneg_left (not_lt.1 hc3) hp0.le]
  interval_cases c
  · exact ⟨a, b, by rw [hc, mul_one]⟩
  · -- The value `2 * p` is impossible, since `2 ≡ 2 (mod 3)` would divide both `a` and `b`.
    exfalso
    have h2 : ((2 : ℕ) : ℤ) ∣ a ^ 2 - a * b + b ^ 2 := ⟨p, by rw [hc]; push_cast; ring⟩
    obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ :=
      Nat.prime_two.dvd_and_dvd_of_dvd_sq_sub_mul_add_sq (by norm_num) h2
    have h2p : (2 : ℤ) ∣ p := ⟨a' ^ 2 - a' * b' + b' ^ 2, by
      rw [ha', hb'] at hc
      push_cast at hc
      linarith⟩
    have h2p' : 2 ∣ p := by exact_mod_cast h2p
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2p'
    omega

/-- A prime `p` is of the form `a ^ 2 - a * b + b ^ 2` if and only if `p` is not congruent to
`2` modulo `3`. -/
theorem Prime.exists_eq_sq_sub_mul_add_sq_iff {p : ℕ} (hp : p.Prime) :
    (∃ a b : ℤ, (p : ℤ) = a ^ 2 - a * b + b ^ 2) ↔ p % 3 ≠ 2 := by
  refine ⟨fun ⟨a, b, h⟩ hp3 ↦ ?_, hp.exists_eq_sq_sub_mul_add_sq⟩
  have heven := even_factorization_of_eq_sq_sub_mul_add_sq hp3 h
  rw [hp.factorization_self] at heven
  exact Nat.not_even_one heven

/-- If every prime `q ≡ 2 (mod 3)` divides `n` to an even power, then `n` is of the form
`a ^ 2 - a * b + b ^ 2`: each prime power in the factorization of `n` is of this form, and the
form is closed under products. -/
theorem exists_eq_sq_sub_mul_add_sq_of_even_factorization {n : ℕ}
    (h : ∀ q : ℕ, q.Prime → q % 3 = 2 → Even (n.factorization q)) :
    ∃ a b : ℤ, (n : ℤ) = a ^ 2 - a * b + b ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨0, 0, by norm_num⟩
  have hpow : ∀ p ∈ n.primeFactors,
      ∃ a b : ℤ, (p : ℤ) ^ n.factorization p = a ^ 2 - a * b + b ^ 2 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    by_cases hp3 : p % 3 = 2
    · -- An even power `p ^ (j + j)` is the value of the form at `(p ^ j, 0)`.
      obtain ⟨j, hj⟩ := h p hprime hp3
      exact ⟨(p : ℤ) ^ j, 0, by rw [hj, pow_add]; ring⟩
    · obtain ⟨c, d, hcd⟩ := hprime.exists_eq_sq_sub_mul_add_sq hp3
      exact sq_sub_mul_add_sq_pow hcd _
  have hn' : (n : ℤ) = ∏ p ∈ n.primeFactors, (p : ℤ) ^ n.factorization p := by
    have hprod := Nat.prod_factorization_pow_eq_self hn
    rw [Finsupp.prod, Nat.support_factorization] at hprod
    exact_mod_cast hprod.symm
  rw [hn']
  exact Finset.prod_induction _ (fun x : ℤ ↦ ∃ a b : ℤ, x = a ^ 2 - a * b + b ^ 2)
    (fun _ _ ⟨_, _, hx⟩ ⟨_, _, hy⟩ ↦ sq_sub_mul_add_sq_mul hx hy) ⟨1, 0, by ring⟩ hpow

/-- **The Eisenstein norm criterion.** A natural number `n` is of the form
`a ^ 2 - a * b + b ^ 2` with integers `a` and `b` if and only if every prime `q ≡ 2 (mod 3)`
divides `n` to an even power. For `n = 0` both sides hold. -/
theorem exists_eq_sq_sub_mul_add_sq_iff {n : ℕ} :
    (∃ a b : ℤ, (n : ℤ) = a ^ 2 - a * b + b ^ 2) ↔
      ∀ q : ℕ, q.Prime → q % 3 = 2 → Even (n.factorization q) :=
  ⟨fun ⟨_, _, h⟩ _ _ hq3 ↦ even_factorization_of_eq_sq_sub_mul_add_sq hq3 h,
    exists_eq_sq_sub_mul_add_sq_of_even_factorization⟩

/-- The shifted form of the criterion: `4 * n` is of the form `u ^ 2 + 3 * v ^ 2` with integers
`u` and `v` if and only if every prime `q ≡ 2 (mod 3)` divides `n` to an even power. -/
theorem exists_four_mul_eq_sq_add_three_mul_sq_iff {n : ℕ} :
    (∃ u v : ℤ, 4 * (n : ℤ) = u ^ 2 + 3 * v ^ 2) ↔
      ∀ q : ℕ, q.Prime → q % 3 = 2 → Even (n.factorization q) :=
  Int.exists_four_mul_eq_sq_add_three_mul_sq_iff.trans exists_eq_sq_sub_mul_add_sq_iff

/-! ### Examples -/

example : ∃ a b : ℤ, ((0 : ℕ) : ℤ) = a ^ 2 - a * b + b ^ 2 := ⟨0, 0, by norm_num⟩

example : ∃ a b : ℤ, ((3 : ℕ) : ℤ) = a ^ 2 - a * b + b ^ 2 := ⟨2, 1, by norm_num⟩

example : ∃ a b : ℤ, ((7 : ℕ) : ℤ) = a ^ 2 - a * b + b ^ 2 := ⟨3, 1, by norm_num⟩

example : ∃ a b : ℤ, ((4 : ℕ) : ℤ) = a ^ 2 - a * b + b ^ 2 := ⟨2, 0, by norm_num⟩

example : ¬∃ a b : ℤ, ((2 : ℕ) : ℤ) = a ^ 2 - a * b + b ^ 2 := by
  rw [Nat.prime_two.exists_eq_sq_sub_mul_add_sq_iff]
  decide

end Nat
