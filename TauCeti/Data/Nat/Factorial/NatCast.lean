/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.NatCast

/-!
# Factorials vanishing in a semiring

If a positive natural number `m` vanishes in a semiring `R`, then so does the factorial of every
natural number `k ≥ m`, since `m ∣ k !`. Conversely, if `d !` is nonzero in a ring, then the
integers `0, …, d` are distinct in it, since their differences are positive and at most `d`.
When `n !` is a unit in a ring, the alternating sum of the products of the inverse
factorials `1 / (i ! (n - i)!)` over `i ≤ n` vanishes for `n ≠ 0`, being `(1 - 1) ^ n / n !`.

## Main results

* `Nat.cast_factorial_eq_zero_of_le`: `(m : R) = 0` with `0 < m ≤ k` gives `(k ! : R) = 0`.
* `TauCeti.injective_natCast_fin_of_factorial_ne_zero`: if `d !` is nonzero in a ring, the
  integers `0, …, d` are distinct in it.
* `TauCeti.sum_range_neg_one_pow_mul_ringInverse_factorial`: if `n !` is a unit,
  `∑_{i ≤ n} (-1) ^ (n - i) / (i ! (n - i)!)` is `1` for `n = 0` and `0` otherwise.
-/

public section

namespace Nat

variable {R : Type*} [Semiring R]

/-- If `m` is positive and vanishes in `R`, so does the factorial of every `k ≥ m`. -/
theorem cast_factorial_eq_zero_of_le {m k : ℕ} (hm : 0 < m) (hmR : (m : R) = 0) (hk : m ≤ k) :
    (k.factorial : R) = 0 := by
  simpa only [hmR, zero_dvd_iff] using
    (Nat.cast_dvd_cast (Nat.dvd_factorial hm hk) : (m : R) ∣ (k.factorial : R))

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

open Finset in
/-- **The alternating sum of inverse factorials.** If `n !` is a unit in a ring `A`, then
`∑_{i ≤ n} (-1) ^ (n - i) / (i ! (n - i)!)` is `1` for `n = 0` and `0` otherwise: multiplied
by `n !` it is the binomial expansion of `(1 - 1) ^ n`. -/
theorem sum_range_neg_one_pow_mul_ringInverse_factorial {A : Type*} [Ring A] {n : ℕ}
    (hn : IsUnit (n.factorial : A)) :
    ∑ i ∈ range (n + 1), (-1) ^ (n - i) *
        (Ring.inverse (i.factorial : A) * Ring.inverse ((n - i).factorial : A)) =
      if n = 0 then 1 else 0 := by
  -- Multiply by the unit `n !`: the summands become `(-1) ^ (n - i) * n.choose i`.
  have hchoose (i : ℕ) (hi : i ∈ range (n + 1)) :
      (n.factorial : A) * ((-1) ^ (n - i) *
          (Ring.inverse (i.factorial : A) * Ring.inverse ((n - i).factorial : A))) =
        1 ^ i * (-1) ^ (n - i) * (n.choose i : A) := by
    have hi : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    -- The sign `(-1) ^ (n - i)` is central and the casts commute, so the factorials cancel.
    rw [← Nat.choose_mul_factorial_mul_factorial hi, Nat.cast_mul, Nat.cast_mul, one_pow, one_mul,
      mul_assoc (n.choose i : A), (Nat.cast_commute (α := A) i.factorial (n - i).factorial).eq,
      ((Commute.neg_one_right _).pow_right _).left_comm]
    simp only [mul_assoc]
    rw [Ring.mul_inverse_cancel_left _ _ (hn.natCast_factorial_of_le hi),
      Ring.mul_inverse_cancel _ (hn.natCast_factorial_of_le (Nat.sub_le n i)), mul_one]
  apply hn.mul_left_cancel
  rw [mul_sum, sum_congr rfl hchoose, ← (Commute.one_left (-1 : A)).add_pow, add_neg_cancel,
    zero_pow_eq]
  split_ifs with h
  · simp [h]
  · simp

end TauCeti
