/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Coprimality and nonzero least common multiples

For `q > 1` and `N > 0`, the natural numbers `q` and `q ^ N - 1` are coprime, because any common
divisor of `q` and `q ^ N - 1` also divides `q ^ N - (q ^ N - 1) = 1`.

The least common multiple of two nonzero naturals is nonzero, also as a `NeZero` instance.
For coprime natural bases `b ≤ a`, a prime dividing `a ^ n - b ^ n` with `n > 0` divides
neither base; this ensures that their ratio modulo the prime is a unit.

## Main results

* `Nat.coprime_pow_sub_one`: `q` is coprime to `q ^ N - 1`. Its consumers are the order
  computation `TauCeti.ZMod.orderOf_unitOfCoprime_pow_sub_one` in
  `TauCeti/Data/ZMod/Units.lean` and the cyclotomic normalization of the local Artin map in
  `TauCeti/NumberTheory/ClassFieldTheory/Local/ExplicitCyclotomicSymbol/ArtinMap.lean`.
* `Nat.Coprime.not_dvd_mul_of_dvd_pow_sub_pow`: for coprime natural bases `b ≤ a`, prime
  divisors of `a ^ n - b ^ n` with `n > 0` do not divide the product of the bases.
-/

public section

namespace Nat

/-- The least common multiple of two nonzero natural numbers is nonzero. -/
instance neZero_lcm (m n : ℕ) [NeZero m] [NeZero n] : NeZero (lcm m n) :=
  ⟨lcm_ne_zero (NeZero.ne m) (NeZero.ne n)⟩

/-- If `q > 1` and `N > 0`, then `q` is coprime to `q ^ N - 1`. -/
theorem coprime_pow_sub_one (q N : ℕ) (hq : 1 < q) (hN : N ≠ 0) :
    q.Coprime (q ^ N - 1) := by
  have hpow : 1 ≤ q ^ N := Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero N (Nat.ne_zero_of_lt hq))
  apply Nat.Coprime.of_dvd_left (dvd_pow_self q hN)
  exact (Nat.coprime_self_sub_right hpow).2 (Nat.coprime_one_right _)

/-- A prime divisor of a positive-index difference of powers of coprime bases divides
neither base. The inequality prevents truncation of natural subtraction. -/
theorem Coprime.not_dvd_mul_of_dvd_pow_sub_pow {a b n p : ℕ} (hab : a.Coprime b)
    (hp : p.Prime) (hba : b ≤ a) (hn : 0 < n) (hdiv : p ∣ a ^ n - b ^ n) :
    ¬ p ∣ a * b := by
  have hle := Nat.pow_le_pow_left hba n
  have hcop := hab.pow n n
  intro hmul
  have hboth : p ∣ a ^ n ∧ p ∣ b ^ n := by
    rcases hp.dvd_mul.mp hmul with ha | hb
    · have ha' := ha.pow hn.ne'
      exact ⟨ha', (Nat.dvd_sub_iff_right hle ha').mp hdiv⟩
    · have hb' := hb.pow hn.ne'
      exact ⟨(Nat.dvd_sub_iff_left hle hb').mp hdiv, hb'⟩
  have := (Nat.dvd_gcd hboth.1 hboth.2).trans (by rw [hcop.gcd_eq_one])
  exact hp.not_dvd_one this

end Nat
