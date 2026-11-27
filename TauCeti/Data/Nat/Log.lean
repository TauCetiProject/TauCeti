/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Find

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

/-- The first integer halving of `n` that goes below `K` stays positive and occurs in at most
`log₂ n` steps, provided `n ≥ 1` and `K ≥ 2`. -/
theorem exists_div_pow_two_lt {n K : ℕ} (hn : 1 ≤ n) (hK : 2 ≤ K) :
    ∃ J : ℕ, J ≤ log 2 n ∧ (∀ j < J, K ≤ n / 2 ^ j) ∧ 1 ≤ n / 2 ^ J ∧ n / 2 ^ J < K := by
  have hpow := pow_log_le_self 2 (by omega : n ≠ 0)
  have hlast : n / 2 ^ log 2 n < K := by
    apply (div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    calc
      n < 2 ^ (log 2 n + 1) := lt_pow_succ_log_self (by decide) n
      _ ≤ K * 2 ^ log 2 n := by rw [pow_succ']; exact Nat.mul_le_mul_right _ hK
  have hex : ∃ J : ℕ, n / 2 ^ J < K := ⟨log 2 n, hlast⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hlast, fun j hj ↦ ?_, ?_, Nat.find_spec hex⟩
  · exact le_of_not_gt (Nat.find_min hex hj)
  · apply (le_div_iff_mul_le (Nat.two_pow_pos _)).2
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.find_min' hex hlast)).trans hpow

end Nat
