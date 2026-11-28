/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.GroupWithZero.Nat
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
* `Nat.add_log_le_log_mul`: `Nat.log b m + Nat.log b n ≤ Nat.log b (m * n)` for `m, n ≠ 0`.
* `Nat.sum_map_log_le_log_prod`: the integer logarithms of the members of a list of positive
  natural numbers add up to at most the integer logarithm of their product.
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

/-- The integer logarithm of a product of positive numbers is at least the sum of their integer
logarithms. -/
theorem add_log_le_log_mul (b : ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    log b m + log b n ≤ log b (m * n) := by
  rcases le_or_gt b 1 with hb | hb
  · simp [log_of_left_le_one hb]
  exact le_log_of_pow_le hb (Nat.pow_add b _ _ ▸ Nat.mul_le_mul (pow_log_le_self b hm)
    (pow_log_le_self b hn))

/-- The integer logarithms of the members of a list of positive numbers add up to at most the
integer logarithm of their product. -/
theorem sum_map_log_le_log_prod (b : ℕ) {l : List ℕ} (hl : 0 ∉ l) :
    (l.map (log b)).sum ≤ log b l.prod := by
  induction l with
  | nil => simp
  | cons n l ih =>
    simp only [List.mem_cons, not_or] at hl
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    exact (Nat.add_le_add_left (ih hl.2) _).trans <| add_log_le_log_mul b (Ne.symm hl.1)
      (List.prod_ne_zero hl.2)

end Nat
