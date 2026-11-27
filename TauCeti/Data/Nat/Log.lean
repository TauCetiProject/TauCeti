/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log

/-!
# Integer logarithms and rounding to powers

Appending a base-`b` digit `e < b` to a positive natural number `n` raises its integer logarithm
by one: `Nat.log b (b * n + e) = Nat.log b n + 1`. This complements Mathlib's `Nat.log_mul_base`,
which is the case `e = 0` with the factors in the other order.

## Main results

* `TauCeti.Nat.log_mul_add`: `Nat.log b (b * n + e) = Nat.log b n + 1` for `n ≠ 0` and `e < b`.
* `Nat.pow_clog_lt_mul_self`: rounding a positive natural number up to a power of `b > 1`
  increases it by a factor strictly less than `b`.
-/

public section

namespace TauCeti.Nat

/-- Appending a base-`b` digit to a positive number raises its integer logarithm by one. -/
theorem log_mul_add {b n e : ℕ} (hb : 1 < b) (hn : n ≠ 0) (he : e < b) :
    Nat.log b (b * n + e) = Nat.log b n + 1 := by
  have hle : b ≤ b * n + e :=
    (Nat.le_mul_of_pos_right b (Nat.pos_of_ne_zero hn)).trans (Nat.le_add_right _ _)
  rw [Nat.log_of_one_lt_of_le hb hle, Nat.mul_add_div (by omega), Nat.div_eq_of_lt he]
  simp

end TauCeti.Nat

namespace Nat

/-- The smallest power of `b > 1` above a positive `n` is strictly less than `b * n`. -/
theorem pow_clog_lt_mul_self {b n : ℕ} (hb : 1 < b) (hn : 0 < n) :
    b ^ clog b n < b * n := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn.ne') with h | h
  · simp [← h, hb]
  have hp : 0 < clog b n := clog_pos hb h
  calc
    b ^ clog b n = b ^ (clog b n).pred * b := by
      rw [← Nat.pow_succ, Nat.succ_pred_eq_of_pos hp]
    _ < b * n := by
      simpa only [Nat.mul_comm] using
        Nat.mul_lt_mul_of_pos_right (pow_pred_clog_lt_self b h) (by omega : 0 < b)

end Nat
