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

For `t > 0` and every natural `k`, `(1 + t ^ 2) ^ (-k / 2) ≤ 1 / t ^ k`: the Japanese bracket
decays at least as fast as `t ^ (-1)`. This converts symbol estimates of order `0` into Mihlin's
condition.

For `t ≥ 1` and an exponent `r` of either sign, `t ^ r` and `(1 + t ^ 2) ^ (r / 2)` are
comparable: each is at most `2 ^ (|r| / 2)` times the other. For `|t| ≤ R`, the Japanese bracket
power `(1 + t ^ 2) ^ (r / 2)` is at least `(1 + R ^ 2) ^ (-|r| / 2)`, so on a ball of a
seminormed group every constant is at most a multiple of `(1 + ‖ξ‖ ^ 2) ^ (r / 2)`. These turn
homogeneous estimates at large frequencies, and bounds on compact sets, into symbol estimates.

## Main results

* `Real.one_add_sq_rpow_neg_le`: `(1 + t ^ 2) ^ (-k / 2) ≤ 1 / t ^ k` for `0 < t`.
* `Real.rpow_le_two_rpow_mul_one_add_sq_rpow` and `Real.one_add_sq_rpow_le_two_rpow_mul_rpow`:
  `t ^ r ≤ 2 ^ (|r| / 2) (1 + t ^ 2) ^ (r / 2)` and `(1 + t ^ 2) ^ (r / 2) ≤ 2 ^ (|r| / 2) t ^ r`
  for `1 ≤ t`.
* `Real.one_add_sq_rpow_neg_abs_le_one_add_sq_rpow`:
  `(1 + R ^ 2) ^ (-|r| / 2) ≤ (1 + t ^ 2) ^ (r / 2)` for `|t| ≤ R`.
* `TauCeti.exists_le_mul_one_add_norm_sq_rpow_of_norm_le`: on a ball, every constant is at most
  a multiple of `(1 + ‖ξ‖ ^ 2) ^ (r / 2)`.
-/

public section

namespace Real

/-- For `t > 0`, `(1 + t ^ 2) ^ (-k / 2) ≤ 1 / t ^ k`. -/
theorem one_add_sq_rpow_neg_le {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (1 + t ^ 2) ^ (-(k : ℝ) / 2) ≤ 1 / t ^ k := by
  have hpow : t ^ k ≤ (1 + t ^ 2) ^ ((k : ℝ) / 2) := by
    calc t ^ k = (t ^ 2) ^ ((k : ℝ) / 2) := by
          rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul ht.le]
          ring_nf
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
      _ = 2 ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := by
          rw [div_rpow hs.le (by norm_num), abs_of_nonpos hr, neg_div, rpow_neg (by norm_num),
            div_eq_inv_mul]

/-- For `t ≥ 1` and an exponent `r` of either sign, `(1 + t²) ^ (r / 2) ≤ 2 ^ (|r| / 2) t ^ r`. -/
theorem one_add_sq_rpow_le_two_rpow_mul_rpow {t : ℝ} (ht : 1 ≤ t) (r : ℝ) :
    (1 + t ^ 2) ^ (r / 2) ≤ 2 ^ (|r| / 2) * t ^ r := by
  have hu : 0 < t ^ 2 := by positivity
  rw [← sq_rpow_div_two (a := t) (by linarith) r]
  rcases le_total 0 r with hr | hr
  · -- For a nonnegative exponent use `1 + t² ≤ 2 t²`.
    calc (1 + t ^ 2) ^ (r / 2) ≤ (2 * t ^ 2) ^ (r / 2) :=
          rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
      _ = 2 ^ (|r| / 2) * (t ^ 2) ^ (r / 2) := by
          rw [mul_rpow (by norm_num) hu.le, abs_of_nonneg hr]
  · calc (1 + t ^ 2) ^ (r / 2) ≤ (t ^ 2) ^ (r / 2) :=
          rpow_le_rpow_of_nonpos hu (by linarith) (by linarith)
      _ ≤ 2 ^ (|r| / 2) * (t ^ 2) ^ (r / 2) :=
          le_mul_of_one_le_left (by positivity) (one_le_rpow (by norm_num) (by positivity))

/-- For `|t| ≤ R` and an exponent `r` of either sign, the Japanese bracket power
`(1 + t ^ 2) ^ (r / 2)` is at least `(1 + R ^ 2) ^ (-|r| / 2)`. -/
theorem one_add_sq_rpow_neg_abs_le_one_add_sq_rpow (t : ℝ) {R : ℝ} (ht : |t| ≤ R) (r : ℝ) :
    (1 + R ^ 2) ^ (-|r| / 2) ≤ (1 + t ^ 2) ^ (r / 2) := by
  have hR : 1 + t ^ 2 ≤ 1 + R ^ 2 := by
    have := sq_le_sq' (abs_le.1 ht).1 (abs_le.1 ht).2
    linarith
  rcases le_or_gt 0 r with hr | hr
  · exact (rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by linarith [abs_nonneg r])).trans
      (one_le_rpow (by nlinarith) (by linarith))
  · rw [abs_of_neg hr, neg_neg]
    exact rpow_le_rpow_of_nonpos (by positivity) hR (by linarith)

end Real

namespace TauCeti

/-- On a ball, every constant is at most a multiple of each power of the Japanese bracket: for
`‖ξ‖ ≤ R`, `M ≤ C (1 + ‖ξ‖ ^ 2) ^ (r / 2)`. -/
theorem exists_le_mul_one_add_norm_sq_rpow_of_norm_le {E : Type*} [SeminormedAddGroup E]
    (M R r : ℝ) : ∃ C, 0 ≤ C ∧ ∀ ξ : E, ‖ξ‖ ≤ R → M ≤ C * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  refine ⟨max M 0 / (1 + R ^ 2) ^ (-|r| / 2), by positivity, fun ξ hξ ↦ ?_⟩
  calc M ≤ max M 0 := le_max_left _ _
    _ = max M 0 / (1 + R ^ 2) ^ (-|r| / 2) * (1 + R ^ 2) ^ (-|r| / 2) := by field_simp
    _ ≤ _ := by
      gcongr
      exact Real.one_add_sq_rpow_neg_abs_le_one_add_sq_rpow ‖ξ‖ ((abs_norm ξ).trans_le hξ) r

end TauCeti
