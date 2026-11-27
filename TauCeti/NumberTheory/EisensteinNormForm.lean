/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
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

* `Int.sq_sub_mul_add_sq_mul`: the form is multiplicative.
* `Nat.Prime.dvd_and_dvd_of_dvd_sq_sub_mul_add_sq`: a prime `q ≡ 2 (mod 3)` dividing
  `a ^ 2 - a * b + b ^ 2` divides `a` and `b`.
* `Nat.Prime.exists_eq_sq_sub_mul_add_sq_iff`: a prime `p` is of the form
  `a ^ 2 - a * b + b ^ 2` if and only if `p % 3 ≠ 2`.
* `Nat.exists_eq_sq_sub_mul_add_sq_iff`: `n` is of the form `a ^ 2 - a * b + b ^ 2` exactly when
  every prime `q ≡ 2 (mod 3)` has even exponent in `n`.
-/

public section

open Finset

namespace Int

/-- The form `a ^ 2 - a * b + b ^ 2` is nonnegative. -/
theorem sq_sub_mul_add_sq_nonneg (a b : ℤ) : 0 ≤ a ^ 2 - a * b + b ^ 2 := by
  nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]

/-- The form `a ^ 2 - a * b + b ^ 2` vanishes only at `a = b = 0`. -/
theorem sq_sub_mul_add_sq_eq_zero_iff {a b : ℤ} : a ^ 2 - a * b + b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hb : b ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
    have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg (2 * b - a), sq_nonneg a]
    exact ⟨pow_eq_zero_iff two_ne_zero |>.1 ha, pow_eq_zero_iff two_ne_zero |>.1 hb⟩
  · rintro ⟨rfl, rfl⟩
    ring

/-- The form `a ^ 2 - a * b + b ^ 2` is multiplicative: this is the multiplicativity of the norm
of `a + b ω` for a primitive cube root of unity `ω`. -/
theorem sq_sub_mul_add_sq_mul (a b c d : ℤ) :
    (a ^ 2 - a * b + b ^ 2) * (c ^ 2 - c * d + d ^ 2) =
      (a * c - b * d) ^ 2 - (a * c - b * d) * (a * d + b * c - b * d) +
        (a * d + b * c - b * d) ^ 2 := by
  ring

/-- A product of two integers of the form `a ^ 2 - a * b + b ^ 2` is again of this form. -/
theorem exists_eq_sq_sub_mul_add_sq_mul {m n : ℤ} (hm : ∃ a b : ℤ, m = a ^ 2 - a * b + b ^ 2)
    (hn : ∃ c d : ℤ, n = c ^ 2 - c * d + d ^ 2) :
    ∃ e f : ℤ, m * n = e ^ 2 - e * f + f ^ 2 := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  exact ⟨_, _, sq_sub_mul_add_sq_mul a b c d⟩

end Int

namespace Nat

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
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (Int.sq_sub_mul_add_sq_nonneg a' b')
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
      rw [hnm, Nat.factorization_mul (pow_ne_zero 2 hq.ne_zero) hm0, Finsupp.add_apply,
        Nat.factorization_pow_self hq]
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
    lt_of_le_of_ne (Int.sq_sub_mul_add_sq_nonneg a b) fun h0 ↦ by
      have h0' := Int.sq_sub_mul_add_sq_eq_zero_iff.1 h0.symm
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
`a ^ 2 - a * b + b ^ 2`. -/
theorem exists_eq_sq_sub_mul_add_sq_of_even_factorization {n : ℕ}
    (h : ∀ q : ℕ, q.Prime → q % 3 = 2 → Even (n.factorization q)) :
    ∃ a b : ℤ, (n : ℤ) = a ^ 2 - a * b + b ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact ⟨0, 0, by norm_num⟩
      · exact ⟨1, 0, by norm_num⟩
    have hn0 : n ≠ 0 := by omega
    have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
    by_cases hp3 : n.minFac % 3 = 2
    · -- A prime `p ≡ 2 (mod 3)` dividing `n` divides it at least twice; split off `p ^ 2`.
      have h1 := hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
      have h2 : 2 ≤ n.factorization n.minFac := by
        obtain ⟨r, hr⟩ := h _ hp hp3
        omega
      obtain ⟨m, hm⟩ := (hp.pow_dvd_iff_le_factorization hn0).2 h2
      have hm0 : m ≠ 0 := by
        rintro rfl
        omega
      have hlt : m < n := by
        have h4 : 4 ≤ n.minFac ^ 2 := by nlinarith [hp.two_le]
        have := Nat.mul_le_mul_right m h4
        omega
      have hfac : ∀ q : ℕ, q.Prime → q % 3 = 2 → Even (m.factorization q) := by
        intro q hq hq3
        have hq' := h q hq hq3
        rw [hm, Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) hm0, Finsupp.add_apply,
          Nat.factorization_pow, Finsupp.smul_apply, hp.factorization, Finsupp.single_apply,
          Nat.even_add] at hq'
        exact hq'.1 (by split_ifs <;> simp)
      have hcast : (n : ℤ) = (n.minFac : ℤ) ^ 2 * m := by exact_mod_cast hm
      rw [hcast]
      exact Int.exists_eq_sq_sub_mul_add_sq_mul ⟨n.minFac, 0, by ring⟩ (ih m hlt hfac)
    · -- A prime `p ≢ 2 (mod 3)` is of the required form; split off `p`.
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hm0 : m ≠ 0 := by
        rintro rfl
        omega
      have hlt : m < n := by
        have := Nat.mul_le_mul_right m hp.two_le
        omega
      have hfac : ∀ q : ℕ, q.Prime → q % 3 = 2 → Even (m.factorization q) := by
        intro q hq hq3
        have hq' := h q hq hq3
        have hpq : n.minFac ≠ q := fun hpq ↦ hp3 (hpq ▸ hq3)
        rwa [hm, Nat.factorization_mul hp.ne_zero hm0, Finsupp.add_apply, hp.factorization,
          Finsupp.single_eq_of_ne hpq.symm, zero_add] at hq'
      have hcast : (n : ℤ) = (n.minFac : ℤ) * m := by exact_mod_cast hm
      rw [hcast]
      exact Int.exists_eq_sq_sub_mul_add_sq_mul (hp.exists_eq_sq_sub_mul_add_sq hp3)
        (ih m hlt hfac)

/-- **The Eisenstein norm criterion.** A natural number `n` is of the form
`a ^ 2 - a * b + b ^ 2` with integers `a` and `b` if and only if every prime `q ≡ 2 (mod 3)`
divides `n` to an even power. For `n = 0` both sides hold. -/
theorem exists_eq_sq_sub_mul_add_sq_iff {n : ℕ} :
    (∃ a b : ℤ, (n : ℤ) = a ^ 2 - a * b + b ^ 2) ↔
      ∀ q : ℕ, q.Prime → q % 3 = 2 → Even (n.factorization q) :=
  ⟨fun ⟨_, _, h⟩ _ _ hq3 ↦ even_factorization_of_eq_sq_sub_mul_add_sq hq3 h,
    exists_eq_sq_sub_mul_add_sq_of_even_factorization⟩

/-! ### Examples -/

example : ∃ a b : ℤ, ((0 : ℕ) : ℤ) = a ^ 2 - a * b + b ^ 2 := ⟨0, 0, by norm_num⟩

example : ∃ a b : ℤ, ((3 : ℕ) : ℤ) = a ^ 2 - a * b + b ^ 2 := ⟨2, 1, by norm_num⟩

example : ∃ a b : ℤ, ((7 : ℕ) : ℤ) = a ^ 2 - a * b + b ^ 2 := ⟨3, 1, by norm_num⟩

example : ∃ a b : ℤ, ((4 : ℕ) : ℤ) = a ^ 2 - a * b + b ^ 2 := ⟨2, 0, by norm_num⟩

example : ¬∃ a b : ℤ, ((2 : ℕ) : ℤ) = a ^ 2 - a * b + b ^ 2 := by
  rw [Nat.prime_two.exists_eq_sq_sub_mul_add_sq_iff]
  decide

end Nat
