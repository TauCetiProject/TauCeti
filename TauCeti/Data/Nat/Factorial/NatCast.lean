/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.Cast.Basic

/-!
# Factorials vanishing in a semiring and falling-factorial casts

If a positive natural number `m` vanishes in a semiring `R`, then so does the factorial of every
natural number `k ≥ m`, since `m ∣ k !`. Conversely, if `d !` is nonzero in a ring, then the
integers `0, …, d` are distinct in it, since their differences are positive and at most `d`.

In a commutative semiring `R`, factoring `y ^ n` out of `(k.descFactorial n : R) * y ^ k` gives
`y ^ n * ((k.descFactorial n : R) * y ^ (k - n))` for all `k` and `n`
(`Nat.cast_descFactorial_mul_pow`), since `k.descFactorial n = 0` when `k < n`.

## Main results

* `Nat.cast_factorial_eq_zero_of_le`: `(m : R) = 0` with `0 < m ≤ k` gives `(k ! : R) = 0`.
* `Nat.cast_descFactorial_mul_pow`:
  `(k.descFactorial n : R) * y ^ k = y ^ n * ((k.descFactorial n : R) * y ^ (k - n))`.
* `TauCeti.injective_natCast_fin_of_factorial_ne_zero`: if `d !` is nonzero in a ring, the
  integers `0, …, d` are distinct in it.
-/

public section

namespace Nat

variable {R : Type*} [Semiring R]

/-- If `m` is positive and vanishes in `R`, so does the factorial of every `k ≥ m`. -/
theorem cast_factorial_eq_zero_of_le {m k : ℕ} (hm : 0 < m) (hmR : (m : R) = 0) (hk : m ≤ k) :
    (k.factorial : R) = 0 := by
  simpa only [hmR, zero_dvd_iff] using
    (Nat.cast_dvd_cast (Nat.dvd_factorial hm hk) : (m : R) ∣ (k.factorial : R))

/-- In a commutative semiring `S`, factoring `y ^ n` out of `(k.descFactorial n : S) * y ^ k`
gives `y ^ n * ((k.descFactorial n : S) * y ^ (k - n))`, even when `k < n` (as
`k.descFactorial n = 0`). -/
theorem cast_descFactorial_mul_pow {S : Type*} [CommSemiring S] (y : S) (k n : ℕ) :
    (k.descFactorial n : S) * y ^ k = y ^ n * ((k.descFactorial n : S) * y ^ (k - n)) := by
  rcases lt_or_ge k n with hkn | hnk
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hkn]
  · rw [mul_left_comm, ← pow_add, Nat.add_sub_of_le hnk]

end Nat

namespace TauCeti

/-- **The integers `0, …, d` are distinct in a ring where `d !` is nonzero**: their differences are
positive integers at most `d`, which would otherwise make `d !` vanish. In particular this holds
in a field of characteristic zero or greater than `d`. -/
theorem injective_natCast_fin_of_factorial_ne_zero {R : Type*} [Ring R] {d : ℕ}
    (hd : (d.factorial : R) ≠ 0) : Function.Injective fun i : Fin (d + 1) ↦ (i : R) := by
  intro a b hab
  dsimp only at hab
  by_contra hne
  have := a.is_le
  have := b.is_le
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h <;>
  · exact hd (Nat.cast_factorial_eq_zero_of_le (Nat.sub_pos_of_lt h)
      (by rw [Nat.cast_sub (Nat.le_of_lt h), hab, sub_self]) (by omega))

end TauCeti
