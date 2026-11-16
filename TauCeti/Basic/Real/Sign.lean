/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Real.Sign
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Differences of signs as interval indicators

For `a < b`, the function `t ↦ (sign (b - t) - sign (a - t)) / 2` is the indicator of the open
interval `(a, b)` with half weight at each endpoint (`Real.sign_sub_sub_sign_sub_div_two`).

For `|x| < c`, the sum `⌊x / c⌋ + ⌈x / c⌉` is the sign of `x`
(`Real.floor_add_ceil_div_eq_sign`).
-/

public section

open Set

namespace Real

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

/-- For `|x| < c`, the sum `⌊x / c⌋ + ⌈x / c⌉` is the sign of `x`. -/
theorem floor_add_ceil_div_eq_sign {x c : ℝ} (hc : 0 < c) (hx : |x| < c) :
    ((⌊x / c⌋ + ⌈x / c⌉ : ℤ) : ℝ) = sign x := by
  rw [abs_lt] at hx
  have h1 : -1 < x / c := by rw [lt_div_iff₀ hc]; linarith
  have h2 : x / c < 1 := by rw [div_lt_iff₀ hc]; linarith
  rcases lt_trichotomy x 0 with h | rfl | h
  · have h0 : x / c < 0 := div_neg_of_neg_of_pos h hc
    rw [(Int.floor_eq_iff (z := -1)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
      (Int.ceil_eq_iff (z := 0)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
      sign_of_neg h]
    norm_num
  · simp
  · have h0 : 0 < x / c := div_pos h hc
    rw [(Int.floor_eq_iff (z := 0)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
      (Int.ceil_eq_iff (z := 1)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
      sign_of_pos h]
    norm_num

end Real
