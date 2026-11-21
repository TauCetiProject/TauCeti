/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary bounds on the Japanese bracket

The Japanese bracket of a real number `t` is `(1 + t ^ 2) ^ (1 / 2)`. This file compares its real
powers with powers of `t`, for scalar `t`; applied to `t = ‖ξ‖`, these compare homogeneous growth
`‖ξ‖ ^ r` with symbol growth `⟨ξ⟩ ^ r`.

For `t > 0` and every natural `k`, `(1 + t ^ 2) ^ (-k / 2) ≤ 1 / t ^ k`: the inverse `k`-th
power of the Japanese bracket is at most `t ^ (-k)`. This converts symbol estimates of order `0`
into Mihlin's condition.

For `t ≥ 1` and an exponent `r` of either sign, `t ^ r` and `(1 + t ^ 2) ^ (r / 2)` are
comparable: each is at most `2 ^ (|r| / 2)` times the other. For `|t| ≤ R`, the Japanese bracket
power `(1 + t ^ 2) ^ (r / 2)` times `(1 + R ^ 2) ^ (|r| / 2)` is at least `1`, so every constant
is at most a multiple of `(1 + t ^ 2) ^ (r / 2)` for `|t| ≤ R`. These turn homogeneous estimates
at large frequencies, and bounds on compact sets, into symbol estimates.

## Main results

* `Real.one_add_sq_rpow_neg_le`: `(1 + t ^ 2) ^ (-k / 2) ≤ 1 / t ^ k` for `0 < t`.
* `Real.rpow_le_two_rpow_mul_one_add_sq_rpow` and `Real.one_add_sq_rpow_le_two_rpow_mul_rpow`:
  `t ^ r ≤ 2 ^ (|r| / 2) (1 + t ^ 2) ^ (r / 2)` and `(1 + t ^ 2) ^ (r / 2) ≤ 2 ^ (|r| / 2) t ^ r`
  for `1 ≤ t`.
* `Real.one_le_one_add_sq_rpow_abs_mul_one_add_sq_rpow`:
  `1 ≤ (1 + R ^ 2) ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2)` for `|t| ≤ R`.
* `Real.exists_le_mul_one_add_sq_rpow_of_abs_le`: for `|t| ≤ R`, every constant is at most a
  multiple of `(1 + t ^ 2) ^ (r / 2)`.
-/

public section

namespace Real

/-- For `t > 0`, `(1 + t ^ 2) ^ (-k / 2) ≤ 1 / t ^ k`. -/
theorem one_add_sq_rpow_neg_le {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (1 + t ^ 2) ^ (-(k : ℝ) / 2) ≤ 1 / t ^ k := by
  have hpow : t ^ k ≤ (1 + t ^ 2) ^ ((k : ℝ) / 2) := by
    calc t ^ k = (t ^ 2) ^ ((k : ℝ) / 2) := by rw [sq_rpow_div_two ht.le, rpow_natCast]
      _ ≤ _ := rpow_le_rpow (by positivity) (by linarith) (by positivity)
  rw [neg_div, rpow_neg (by positivity), ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hpow

/-- For `t ≥ 1` and an exponent `r` of either sign, `t ^ r ≤ 2 ^ (|r| / 2) (1 + t²) ^ (r / 2)`. -/
theorem rpow_le_two_rpow_mul_one_add_sq_rpow {t : ℝ} (ht : 1 ≤ t) (r : ℝ) :
    t ^ r ≤ 2 ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := by
  have hu : 0 < t ^ 2 := by positivity
  have hs : 0 < 1 + t ^ 2 := by positivity
  rw [← sq_rpow_div_two (a := t) (by linarith) r]
  rcases le_total 0 r with hr | hr
  · calc (t ^ 2) ^ (r / 2) ≤ (1 + t ^ 2) ^ (r / 2) :=
          rpow_le_rpow hu.le (by linarith) (by linarith)
      _ ≤ 2 ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) :=
          le_mul_of_one_le_left (by positivity) (one_le_rpow (by norm_num) (by positivity))
  · -- For a nonpositive exponent use `(1 + t²) / 2 ≤ t²`, and `2 ^ (|r| / 2) = 2 ^ (-(r / 2))`.
    have h2 : (1 + t ^ 2) / 2 ≤ t ^ 2 := by nlinarith
    calc (t ^ 2) ^ (r / 2) ≤ ((1 + t ^ 2) / 2) ^ (r / 2) :=
          rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
      _ = (1 + t ^ 2) ^ (r / 2) / 2 ^ (r / 2) := div_rpow hs.le zero_le_two _
      _ = 2 ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := by
          rw [abs_of_nonpos hr, neg_div, rpow_neg zero_le_two, inv_mul_eq_div]

/-- For `t ≥ 1` and an exponent `r` of either sign, `(1 + t²) ^ (r / 2) ≤ 2 ^ (|r| / 2) t ^ r`. -/
theorem one_add_sq_rpow_le_two_rpow_mul_rpow {t : ℝ} (ht : 1 ≤ t) (r : ℝ) :
    (1 + t ^ 2) ^ (r / 2) ≤ 2 ^ (|r| / 2) * t ^ r := by
  have ht0 : 0 < t := by linarith
  have h := rpow_le_two_rpow_mul_one_add_sq_rpow ht (-r)
  -- `h` reads `1 / t ^ r ≤ 2 ^ (|r| / 2) / (1 + t ^ 2) ^ (r / 2)`; clear the denominators.
  simp only [abs_neg, neg_div, rpow_neg ht0.le, rpow_neg (by positivity : (0 : ℝ) ≤ 1 + t ^ 2),
    ← one_div, mul_one_div] at h
  rwa [div_le_div_iff₀ (rpow_pos_of_pos ht0 r) (by positivity), one_mul] at h

/-- For `|t| ≤ R` and an exponent `r` of either sign, the Japanese bracket power
`(1 + t ^ 2) ^ (r / 2)` is at least `(1 + R ^ 2) ^ (-|r| / 2)`, in the multiplicative form
`1 ≤ (1 + R ^ 2) ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2)`. -/
theorem one_le_one_add_sq_rpow_abs_mul_one_add_sq_rpow (t : ℝ) {R : ℝ} (ht : |t| ≤ R) (r : ℝ) :
    1 ≤ (1 + R ^ 2) ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := by
  have hR : 1 + t ^ 2 ≤ 1 + R ^ 2 := by
    have := sq_le_sq' (abs_le.1 ht).1 (abs_le.1 ht).2
    linarith
  have ht1 : 1 ≤ 1 + t ^ 2 := le_add_of_nonneg_right (sq_nonneg t)
  rcases le_or_gt 0 r with hr | hr
  · exact one_le_mul_of_one_le_of_one_le (one_le_rpow (ht1.trans hR) (by positivity))
      (one_le_rpow ht1 (by linarith))
  · calc (1 : ℝ) = (1 + t ^ 2) ^ (|r| / 2 + r / 2) := by
          rw [abs_of_neg hr, neg_div, neg_add_cancel, rpow_zero]
      _ = (1 + t ^ 2) ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := rpow_add (by positivity) _ _
      _ ≤ _ := by gcongr

/-- For `|t| ≤ R`, every constant is at most a multiple of each power of the Japanese bracket:
`M ≤ C (1 + t ^ 2) ^ (r / 2)`. -/
theorem exists_le_mul_one_add_sq_rpow_of_abs_le (M R r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ R → M ≤ C * (1 + t ^ 2) ^ (r / 2) := by
  refine ⟨max M 0 * (1 + R ^ 2) ^ (|r| / 2), by positivity, fun t ht ↦ ?_⟩
  calc M ≤ max M 0 * 1 := by rw [mul_one]; exact le_max_left _ _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (one_le_one_add_sq_rpow_abs_mul_one_add_sq_rpow t ht r)
        (le_max_right _ _)

end Real
