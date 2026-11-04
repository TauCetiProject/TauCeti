/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Gcd detection by reduction of residues

For a divisor `d ∣ n`, reduction of a residue `t : ZMod n` modulo `d` vanishes exactly
when `d ∣ gcd(t.val, n)`. This holds even for `n = 0`, where `t.val` is an absolute value.
For positive `n`, vanishing modulo one prime divisor and nonvanishing modulo another
therefore certify a proper factor of `n`. The positivity restriction matters: a gcd
with `0` cannot be strictly smaller than `0`.

These statements distinguish detection of a prime divisor from detection of a proper
factor. They apply, in particular, to denominators in elliptic-curve factorization.
-/

public section

namespace ZMod

/-- Reduction modulo a divisor `d` of `n` vanishes exactly when `d` divides the gcd of
the natural representative with `n`. Neither modulus needs to be positive or prime. -/
theorem dvd_gcd_val_iff_castHom_eq_zero {n : ℕ} (t : ZMod n) {d : ℕ} (hd : d ∣ n) :
    d ∣ Nat.gcd t.val n ↔ castHom hd (ZMod d) t = 0 := by
  rw [Nat.dvd_gcd_iff, and_iff_left hd, castHom_apply]
  cases n with
  | zero =>
    exact Int.natCast_dvd.symm.trans (intCast_zmod_eq_zero_iff_dvd t d).symm
  | succ n =>
    rw [cast_eq_val, natCast_eq_zero_iff]

/-- A residue vanishing modulo a divisor greater than one of a positive modulus, but not
modulo another divisor, gives a proper gcd. Neither divisor needs to be prime. -/
theorem one_lt_gcd_val_and_gcd_val_lt_of_castHom {n : ℕ} [NeZero n] (t : ZMod n)
    {p q : ℕ} (hp : 1 < p) (hpn : p ∣ n) (hqn : q ∣ n)
    (hp0 : castHom hpn (ZMod p) t = 0) (hq0 : castHom hqn (ZMod q) t ≠ 0) :
    1 < Nat.gcd t.val n ∧ Nat.gcd t.val n < n := by
  have hpg := (t.dvd_gcd_val_iff_castHom_eq_zero hpn).mpr hp0
  have hqg := (t.dvd_gcd_val_iff_castHom_eq_zero hqn).not.mpr hq0
  have hgpos := Nat.gcd_pos_of_pos_right t.val (NeZero.pos n)
  refine ⟨lt_of_lt_of_le hp (Nat.le_of_dvd hgpos hpg), ?_⟩
  exact lt_of_le_of_ne (Nat.le_of_dvd (NeZero.pos n) (Nat.gcd_dvd_right t.val n))
    (fun h => hqg (h.symm ▸ hqn))

end ZMod
