/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Data.Int.Round

/-!
# Examples of nearest integer multiples

For step `w = 6`, the integers `13 = 2 · 6 + 1` and `17 = 3 · 6 - 1` lie at distance `1` from a
multiple of `6`, whereas the midpoint `15 = 2 · 6 + 3 = 3 · 6 - 3` achieves the half-step bound
`2 · |t - c w| = 6` and admits no integer `c` with `2 · |15 - c · 6| < 6`. For any nearest
multiple, the remainder vanishes if and only if `6 ∣ t`, illustrated at `t = 12` and `t = 15`.
The final examples check sharpness of `|t - c μ| < |μ|` and the degenerate step `μ = 0`.
-/

namespace Int

-- `13 = 2 · 6 + 1` and `17 = 3 · 6 - 1` lie strictly inside the half-step bound for `w = 6`.
example : (13 : ℤ) = 2 * 6 + 1 ∧ 2 * |(13 : ℤ) - 2 * 6| ≤ |(6 : ℤ)| ∧
    (17 : ℤ) = 3 * 6 - 1 ∧ 2 * |(17 : ℤ) - 3 * 6| ≤ |(6 : ℤ)| := by
  decide

-- At the midpoint `15 = 2 · 6 + 3 = 3 · 6 - 3`, the half-step bound is attained by both `2` and
-- `3`, and no integer satisfies the strict inequality `2 * |15 - i * 6| < 6`.
example : (15 : ℤ) = 2 * 6 + 3 ∧ (15 : ℤ) = 3 * 6 - 3 ∧
    2 * |(15 : ℤ) - 2 * 6| ≤ |(6 : ℤ)| ∧ 2 * |(15 : ℤ) - 3 * 6| ≤ |(6 : ℤ)| ∧
    ∀ i : ℤ, ¬ 2 * |(15 : ℤ) - i * 6| < 6 := by
  refine ⟨by decide, by decide, by decide, by decide, fun i h ↦ ?_⟩
  rw [abs_eq_natAbs] at h
  omega

-- For `t = 12` (`6 ∣ 12`), every nearest multiple of `6` has zero remainder (`c = 2`).
example {c : ℤ} (hc : 2 * |(12 : ℤ) - c * 6| ≤ |(6 : ℤ)|) :
    |(12 : ℤ) - c * 6| = 0 ∧ c = 2 := by
  have heq : (12 : ℤ) = c * 6 :=
    (eq_mul_iff_dvd_of_two_mul_abs_sub_mul_le hc).mpr (by decide)
  exact ⟨by simp [heq], by omega⟩

-- For `t = 15` (`6 ∤ 15`), no nearest multiple of `6` has zero remainder.
example {c : ℤ} (hc : 2 * |(15 : ℤ) - c * 6| ≤ |(6 : ℤ)|) :
    |(15 : ℤ) - c * 6| ≠ 0 := by
  rw [ne_eq, abs_eq_zero, sub_eq_zero, eq_mul_iff_dvd_of_two_mul_abs_sub_mul_le hc]
  decide

-- Sharpness of `eq_mul_iff_dvd_of_abs_sub_mul_lt`: at `|t - c * μ| = |μ|`, `μ ∣ t` does not
-- force `t = c * μ`.
example : |(12 : ℤ) - 1 * 6| = |(6 : ℤ)| ∧ (6 : ℤ) ∣ 12 ∧ (12 : ℤ) ≠ 1 * 6 := by
  decide

-- `eq_mul_iff_dvd_of_two_mul_abs_sub_mul_le` also covers `μ = 0`.
example (c : ℤ) : (0 : ℤ) = c * 0 ↔ (0 : ℤ) ∣ 0 :=
  eq_mul_iff_dvd_of_two_mul_abs_sub_mul_le (by simp)

-- Direct existence of a nearest multiple for positive and negative steps.
example (t : ℤ) : (∃ c : ℤ, 2 * |t - c * 6| ≤ 6) ∧ (∃ c : ℤ, 2 * |t - c * (-6)| ≤ 6) :=
  ⟨exists_two_mul_abs_sub_mul_le t (by decide),
    exists_two_mul_abs_sub_mul_le t (by decide)⟩

end Int
