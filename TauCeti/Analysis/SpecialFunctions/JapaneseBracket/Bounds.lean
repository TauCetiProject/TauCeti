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

The Japanese bracket of a real number `t` is `(1 + t ^ 2) ^ (1 / 2)`. The bounds in the `Real`
namespace compare its real powers with powers of `t`, for scalar `t`; applied to `t = ‖ξ‖`, these
compare homogeneous growth `‖ξ‖ ^ r` with symbol growth `⟨ξ⟩ ^ r`.

For `t ≥ 1` and an exponent `r` of either sign, `t ^ r` and `(1 + t ^ 2) ^ (r / 2)` are
comparable: each is at most `2 ^ (|r| / 2)` times the other. For `|t| ≤ R`, the Japanese bracket
power `(1 + t ^ 2) ^ (r / 2)` times `(1 + R ^ 2) ^ (|r| / 2)` is at least `1`, so every constant
is at most a multiple of `(1 + t ^ 2) ^ (r / 2)` for `|t| ≤ R`. These turn homogeneous estimates
at large frequencies, and bounds on compact sets, into symbol estimates.

For a vector `x` of a normed group, with `⟨x⟩ = (1 + ‖x‖ ^ 2) ^ (1 / 2)`, one power of `‖x‖` costs
one order of the bracket, `⟨x⟩ ^ m ‖x‖ ≤ ⟨x⟩ ^ (m + 1)`, and a linear weight `(1 + c ‖x‖) ^ i`
with `c ≥ 0` is at most `(1 + c) ^ i ⟨x⟩ ^ i`. Bounds on `F` and on `‖v‖ ^ (2N) F` combine to a
bound on `F` with the weight `(1 + ‖v‖ ^ 2) ^ (-N)`.

## Main results

* `Real.rpow_le_two_rpow_mul_one_add_sq_rpow` and `Real.one_add_sq_rpow_le_two_rpow_mul_rpow`:
  `t ^ r ≤ 2 ^ (|r| / 2) (1 + t ^ 2) ^ (r / 2)` and `(1 + t ^ 2) ^ (r / 2) ≤ 2 ^ (|r| / 2) t ^ r`
  for `1 ≤ t`.
* `Real.one_le_one_add_sq_rpow_abs_mul_one_add_sq_rpow`:
  `1 ≤ (1 + R ^ 2) ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2)` for `|t| ≤ R`.
* `Real.exists_le_mul_one_add_sq_rpow_of_abs_le`: for `|t| ≤ R`, every constant is at most a
  multiple of `(1 + t ^ 2) ^ (r / 2)`.
* `TauCeti.one_add_norm_sq_rpow_mul_norm_le`: `⟨x⟩ ^ m ‖x‖ ≤ ⟨x⟩ ^ (m + 1)`.
* `TauCeti.one_add_mul_norm_pow_le`: `(1 + c ‖x‖) ^ i ≤ (1 + c) ^ i ⟨x⟩ ^ i` for `c ≥ 0`.
* `TauCeti.le_mul_one_add_norm_sq_pow_inv`: bounds on `F` and on `‖v‖ ^ (2N) F` combine to a
  bound on `F` with the weight `((1 + ‖v‖ ^ 2) ^ N)⁻¹`.
-/

public section

namespace Real

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

namespace TauCeti

/-- One power of `‖x‖` costs one order of the Japanese bracket `⟨x⟩ = (1 + ‖x‖ ^ 2) ^ (1 / 2)`:
`⟨x⟩ ^ m ‖x‖ ≤ ⟨x⟩ ^ (m + 1)` for every real `m`. -/
theorem one_add_norm_sq_rpow_mul_norm_le {E : Type*} [NormedAddCommGroup E] (x : E) (m : ℝ) :
    (1 + ‖x‖ ^ 2) ^ (m / 2) * ‖x‖ ≤ (1 + ‖x‖ ^ 2) ^ ((m + 1) / 2) := by
  rw [add_div, Real.rpow_add (by positivity), ← Real.sqrt_eq_rpow]
  gcongr
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- A linear weight is dominated by the Japanese bracket `⟨x⟩ = (1 + ‖x‖ ^ 2) ^ (1 / 2)`:
`(1 + c ‖x‖) ^ i ≤ (1 + c) ^ i ⟨x⟩ ^ i` for `c ≥ 0`. -/
theorem one_add_mul_norm_pow_le {E : Type*} [NormedAddCommGroup E] {c : ℝ} (hc : 0 ≤ c) (x : E)
    (i : ℕ) : (1 + c * ‖x‖) ^ i ≤ (1 + c) ^ i * (1 + ‖x‖ ^ 2) ^ ((i : ℝ) / 2) := by
  have hle : 1 + c * ‖x‖ ≤ (1 + c) * √(1 + ‖x‖ ^ 2) := by
    have h1 : 1 ≤ √(1 + ‖x‖ ^ 2) := Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ‖x‖])
    have h2 : ‖x‖ ≤ √(1 + ‖x‖ ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
    nlinarith
  have hsqrt : (1 + ‖x‖ ^ 2) ^ ((i : ℝ) / 2) = √(1 + ‖x‖ ^ 2) ^ i := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
    ring_nf
  rw [hsqrt, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hle i

/-- Bounds `F ≤ C₀ w` and `‖v‖ ^ (2N) F ≤ C₁ w` combine to the weighted bound
`F ≤ 2 ^ (N - 1) (C₀ + C₁) w ((1 + ‖v‖²) ^ N)⁻¹`. -/
theorem le_mul_one_add_norm_sq_pow_inv {E : Type*} [SeminormedAddCommGroup E] {v : E} {N : ℕ}
    {F C₀ C₁ w : ℝ} (hF : 0 ≤ F) (h₀ : F ≤ C₀ * w) (h₁ : ‖v‖ ^ (2 * N) * F ≤ C₁ * w) :
    F ≤ 2 ^ (N - 1) * (C₀ + C₁) * w * ((1 + ‖v‖ ^ 2) ^ N)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm F]
  calc (1 + ‖v‖ ^ 2) ^ N * F ≤ 2 ^ (N - 1) * (1 ^ N + (‖v‖ ^ 2) ^ N) * F :=
        mul_le_mul_of_nonneg_right (add_pow_le zero_le_one (by positivity) N) hF
    _ = 2 ^ (N - 1) * (F + ‖v‖ ^ (2 * N) * F) := by rw [one_pow, ← pow_mul]; ring
    _ ≤ 2 ^ (N - 1) * (C₀ * w + C₁ * w) :=
        mul_le_mul_of_nonneg_left (add_le_add h₀ h₁) (by positivity)
    _ = 2 ^ (N - 1) * (C₀ + C₁) * w := by ring

end TauCeti
