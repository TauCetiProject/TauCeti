/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Real.Sign

/-!
# Signs of real numbers

For `a < b`, the function `t ↦ (sign (b - t) - sign (a - t)) / 2` is the indicator of the open
interval `(a, b)` with half weight at each endpoint (`Real.sign_sub_sub_sign_sub_div_two`). The
sign itself is bounded by one in absolute value (`Real.abs_sign_le_one`), as are its powers
(`Real.abs_sign_pow_le_one`), with absolute value one away from zero (`Real.abs_sign_of_ne_zero`),
and `|r| sign r = r` (`Real.abs_mul_sign`).

For `|x| < c`, the sign of `x` is the count `⌊x / c⌋ + ⌈x / c⌉`
(`TauCeti.floor_add_ceil_div_eq_sign_of_abs_lt`).
-/

public section

open Set

namespace Real

/-- The real sign function is bounded by one in absolute value. -/
theorem abs_sign_le_one (r : ℝ) : |sign r| ≤ 1 := by
  rcases sign_apply_eq r with h | h | h <;> simp [h]

/-- The powers of the real sign function are bounded by one in absolute value. -/
theorem abs_sign_pow_le_one (r : ℝ) (j : ℕ) : |sign r ^ j| ≤ 1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (abs_sign_le_one r)

/-- The real sign of a nonzero number has absolute value one. -/
@[simp]
theorem abs_sign_of_ne_zero {r : ℝ} (hr : r ≠ 0) : |sign r| = 1 := by
  rcases sign_apply_eq_of_ne_zero r hr with h | h <;> simp [h]

/-- A real number is its absolute value times its sign. -/
@[simp]
theorem abs_mul_sign (r : ℝ) : |r| * sign r = r := by
  rcases lt_trichotomy r 0 with h | rfl | h
  · rw [abs_of_neg h, sign_of_neg h]
    ring
  · simp
  · rw [abs_of_pos h, sign_of_pos h, mul_one]

/-- For `a < b`, half the difference `sign (b - t) - sign (a - t)` is the indicator of `(a, b)`
with half weight at the endpoints `a` and `b`. -/
theorem sign_sub_sub_sign_sub_div_two {a b : ℝ} (hab : a < b) (t : ℝ) :
    (sign (b - t) - sign (a - t)) / 2 =
      (Ioo a b).indicator 1 t +
        (({a} : Set ℝ).indicator 1 t + ({b} : Set ℝ).indicator 1 t) / 2 := by
  rcases lt_trichotomy t a with h | rfl | h
  · simp [sign_of_pos (sub_pos.2 h), sign_of_pos (sub_pos.2 (h.trans hab)),
      h.ne, (h.trans hab).ne, h.not_gt]
  · simp [sign_of_pos (sub_pos.2 hab), hab.ne]
  rcases lt_trichotomy t b with h' | rfl | h'
  · simp [sign_of_pos (sub_pos.2 h'), sign_of_neg (sub_neg.2 h), h, h', h.ne', h'.ne]
  · simp [sign_of_neg (sub_neg.2 h), hab.ne']
  · simp [sign_of_neg (sub_neg.2 h'), sign_of_neg (sub_neg.2 h), h.ne', h'.ne', h'.not_gt]

end Real

namespace TauCeti

/-- For `|x| < c`, the count `⌊x / c⌋ + ⌈x / c⌉` is the sign of `x`. -/
theorem floor_add_ceil_div_eq_sign_of_abs_lt {x c : ℝ} (h : |x| < c) :
    ((⌊x / c⌋ + ⌈x / c⌉ : ℤ) : ℝ) = Real.sign x := by
  have hc : 0 < c := (abs_nonneg x).trans_lt h
  have hlo : -1 < x / c := by rw [lt_div_iff₀ hc]; linarith [neg_abs_le x]
  have hhi : x / c < 1 := by rw [div_lt_iff₀ hc]; linarith [le_abs_self x]
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · have hneg' : x / c < 0 := div_neg_of_neg_of_pos hneg hc
    rw [(Int.floor_eq_iff (z := -1)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
      (Int.ceil_eq_iff (z := 0)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
      Real.sign_of_neg hneg]
    norm_num
  · simp
  · have hpos' : 0 < x / c := div_pos hpos hc
    rw [(Int.floor_eq_iff (z := 0)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
      (Int.ceil_eq_iff (z := 1)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
      Real.sign_of_pos hpos]
    norm_num

end TauCeti
