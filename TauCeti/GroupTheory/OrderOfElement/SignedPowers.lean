/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement

/-!
# Modular relations between exponents of signed powers

If two powers of a finite-order element are signed powers of `x` times a common base point,
eliminating the signs and `x` gives a congruence among the three exponents. This applies even
when some of the points coincide.
-/

public section

/-- Two signed-power relations with a common base point give a modular weighted mean among the
exponents. The signs can be any elements with square one. -/
theorem IsOfFinOrder.add_mul_modEq_of_eq_mul_pow_mul {G : Type*} [CommMonoid G] {g x ε ε' : G}
    (hg : IsOfFinOrder g) {a b c i j : ℕ} (hij : i ≤ j) (hε : ε ^ 2 = 1) (hε' : ε' ^ 2 = 1)
    (hb : g ^ b = ε * x ^ i * g ^ a) (hc : g ^ c = ε' * x ^ j * g ^ a) :
    2 * j * b ≡ 2 * (j - i) * a + 2 * i * c [MOD orderOf g] := by
  have hb' : g ^ (2 * j * b) = x ^ (i * 2 * j) * g ^ (2 * j * a) := by
    have he := congrArg (fun y => (y ^ 2) ^ j) hb
    simpa only [mul_pow, hε, one_mul, ← pow_mul, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using he
  have hc' : g ^ (2 * i * c) = x ^ (j * 2 * i) * g ^ (2 * i * a) := by
    have he := congrArg (fun y => (y ^ 2) ^ i) hc
    simpa only [mul_pow, hε', one_mul, ← pow_mul, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using he
  have hpow : g ^ (2 * j * b + 2 * i * a) = g ^ (2 * i * c + 2 * j * a) := by
    rw [pow_add, pow_add, hb', hc', (by ac_rfl : i * 2 * j = j * 2 * i)]
    ac_rfl
  have hs := hg.pow_eq_pow_iff_modEq.1 hpow
  have hsplit : 2 * i * c + 2 * j * a = (2 * (j - i) * a + 2 * i * c) + 2 * i * a := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
    have hle : 2 * i * a ≤ 2 * j * a := by gcongr
    omega
  rw [hsplit] at hs
  exact Nat.ModEq.add_right_cancel' _ hs
