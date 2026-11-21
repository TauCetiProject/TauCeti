/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Sqrt

/-!
# Elementary bounds on the Japanese bracket

The Japanese bracket of a real number `t` is `⟨t⟩ = (1 + t ^ 2) ^ (1 / 2)`. The bounds here
compare its real powers with powers of `t`, for scalar `t`; applied to `t = ‖ξ‖`, these compare
homogeneous growth `‖ξ‖ ^ r` with symbol growth `⟨ξ⟩ ^ r`.

For `|t| ≥ 1` and an exponent `r` of either sign, `|t| ^ r` and `(1 + t ^ 2) ^ (r / 2)` are
comparable: each is at most `2 ^ (|r| / 2)` times the other. For `|t| ≤ R`, the Japanese bracket
power `(1 + t ^ 2) ^ (r / 2)` times `(1 + R ^ 2) ^ (|r| / 2)` is at least `1`. So for fixed `M`,
`R` and `r`, a single constant `C ≥ 0` gives `M ≤ C (1 + t ^ 2) ^ (r / 2)` for every `t` with
`|t| ≤ R`. These turn homogeneous estimates at large frequencies, and bounds on compact sets,
into symbol estimates.

One power of `|t|` costs one order of the bracket, `⟨t⟩ ^ m |t| ≤ ⟨t⟩ ^ (m + 1)`, and a linear
weight `(1 + c |t|) ^ p` with `c ≥ 0` and `p ≥ 0` is at most `(1 + c) ^ p ⟨t⟩ ^ p`. For `F ≥ 0`,
bounds on `F` and on `t ^ (2N) F` combine to a bound on `F` with the weight `(1 + t ^ 2) ^ (-N)`.

## Main results

* `Real.rpow_le_two_rpow_mul_one_add_sq_rpow` and `Real.one_add_sq_rpow_le_two_rpow_mul_rpow`:
  `|t| ^ r ≤ 2 ^ (|r| / 2) (1 + t ^ 2) ^ (r / 2)` and
  `(1 + t ^ 2) ^ (r / 2) ≤ 2 ^ (|r| / 2) |t| ^ r` for `1 ≤ |t|`.
* `Real.one_le_one_add_sq_rpow_abs_mul_one_add_sq_rpow`:
  `1 ≤ (1 + R ^ 2) ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2)` for `|t| ≤ R`.
* `Real.exists_le_mul_one_add_sq_rpow_of_abs_le`: for fixed `M`, `R` and `r`, a single `C ≥ 0`
  gives `M ≤ C (1 + t ^ 2) ^ (r / 2)` for every `t` with `|t| ≤ R`.
* `Real.one_add_sq_rpow_mul_abs_le`: `⟨t⟩ ^ m |t| ≤ ⟨t⟩ ^ (m + 1)`.
* `Real.one_add_mul_abs_rpow_le`: `(1 + c |t|) ^ p ≤ (1 + c) ^ p ⟨t⟩ ^ p` for `c ≥ 0` and
  `p ≥ 0`.
* `Real.le_mul_one_add_sq_pow_inv`: for `F ≥ 0`, bounds on `F` and on `t ^ (2N) F` combine to a
  bound on `F` with the weight `((1 + t ^ 2) ^ N)⁻¹`.
-/

public section

namespace Real

/-- For `|t| ≥ 1` and an exponent `r` of either sign,
`|t| ^ r ≤ 2 ^ (|r| / 2) (1 + t²) ^ (r / 2)`. -/
theorem rpow_le_two_rpow_mul_one_add_sq_rpow {t : ℝ} (ht : 1 ≤ |t|) (r : ℝ) :
    |t| ^ r ≤ 2 ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := by
  have ht2 : 1 ≤ t ^ 2 := one_le_sq_iff_one_le_abs t |>.2 ht
  have hs : 0 < 1 + t ^ 2 := by positivity
  -- The ratio `t ^ 2 / (1 + t ^ 2)` and its reciprocal are both at most `2`.
  have h := rpow_le_rpow_abs (x := t ^ 2 / (1 + t ^ 2)) (R := 2) (by positivity)
    (((div_le_one hs).2 (by linarith)).trans one_le_two)
    (by rw [inv_div, div_le_iff₀ (by positivity)]; linarith) (r / 2)
  calc |t| ^ r = (t ^ 2 / (1 + t ^ 2)) ^ (r / 2) * (1 + t ^ 2) ^ (r / 2) := by
        rw [div_rpow (sq_nonneg t) hs.le, div_mul_cancel₀ _ (by positivity), ← sq_abs t,
          sq_rpow_div_two (abs_nonneg t)]
    _ ≤ 2 ^ |r / 2| * (1 + t ^ 2) ^ (r / 2) := by gcongr
    _ = 2 ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := by simp [abs_div]

/-- For `|t| ≥ 1` and an exponent `r` of either sign,
`(1 + t²) ^ (r / 2) ≤ 2 ^ (|r| / 2) |t| ^ r`. -/
theorem one_add_sq_rpow_le_two_rpow_mul_rpow {t : ℝ} (ht : 1 ≤ |t|) (r : ℝ) :
    (1 + t ^ 2) ^ (r / 2) ≤ 2 ^ (|r| / 2) * |t| ^ r := by
  have ht0 : 0 < |t| := by linarith
  have hs : 0 < (1 + t ^ 2) ^ (r / 2) := by positivity
  -- Multiply the bound at `-r` by `(1 + t ^ 2) ^ (r / 2) |t| ^ r`.
  have h := rpow_le_two_rpow_mul_one_add_sq_rpow ht (-r)
  rw [abs_neg, neg_div, rpow_neg ht0.le, rpow_neg (by positivity)] at h
  calc (1 + t ^ 2) ^ (r / 2) = (1 + t ^ 2) ^ (r / 2) * (|t| ^ r)⁻¹ * |t| ^ r :=
        (inv_mul_cancel_right₀ (rpow_pos_of_pos ht0 r).ne' _).symm
    _ ≤ (1 + t ^ 2) ^ (r / 2) * (2 ^ (|r| / 2) * ((1 + t ^ 2) ^ (r / 2))⁻¹) * |t| ^ r := by
        gcongr
    _ = 2 ^ (|r| / 2) * |t| ^ r := by field_simp [hs.ne']

/-- For `|t| ≤ R` and an exponent `r` of either sign, the Japanese bracket power
`(1 + t ^ 2) ^ (r / 2)` is at least `(1 + R ^ 2) ^ (-|r| / 2)`, in the multiplicative form
`1 ≤ (1 + R ^ 2) ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2)`. -/
theorem one_le_one_add_sq_rpow_abs_mul_one_add_sq_rpow (t : ℝ) {R : ℝ} (ht : |t| ≤ R) (r : ℝ) :
    1 ≤ (1 + R ^ 2) ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := by
  have hR : 1 + t ^ 2 ≤ 1 + R ^ 2 := by
    have := sq_le_sq' (abs_le.1 ht).1 (abs_le.1 ht).2
    linarith
  have ht1 : 1 ≤ 1 + t ^ 2 := le_add_of_nonneg_right (sq_nonneg t)
  -- Both `1 + t ^ 2` and its reciprocal are at most `1 + R ^ 2`.
  have h := rpow_le_rpow_abs (by positivity) hR ((inv_le_one_of_one_le₀ ht1).trans (ht1.trans hR))
    (-(r / 2))
  -- `h` reads `((1 + t ^ 2) ^ (r / 2))⁻¹ ≤ (1 + R ^ 2) ^ |-(r / 2)|`.
  rw [rpow_neg (by positivity), show |-(r / 2)| = |r| / 2 by simp [abs_div]] at h
  exact (inv_le_iff_one_le_mul₀ (by positivity)).1 h

/-- For fixed `M`, `R` and `r`, a single constant `C ≥ 0` bounds `M` by a multiple of the
Japanese bracket power uniformly on `|t| ≤ R`: `M ≤ C (1 + t ^ 2) ^ (r / 2)` for every such `t`.
-/
theorem exists_le_mul_one_add_sq_rpow_of_abs_le (M R r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ R → M ≤ C * (1 + t ^ 2) ^ (r / 2) := by
  refine ⟨max M 0 * (1 + R ^ 2) ^ (|r| / 2), by positivity, fun t ht ↦ ?_⟩
  calc M ≤ max M 0 * 1 := by rw [mul_one]; exact le_max_left _ _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (one_le_one_add_sq_rpow_abs_mul_one_add_sq_rpow t ht r)
        (le_max_right _ _)

/-- One power of `|t|` costs one order of the Japanese bracket `⟨t⟩ = (1 + t ^ 2) ^ (1 / 2)`:
`⟨t⟩ ^ m |t| ≤ ⟨t⟩ ^ (m + 1)` for every real `m`. -/
theorem one_add_sq_rpow_mul_abs_le (t m : ℝ) :
    (1 + t ^ 2) ^ (m / 2) * |t| ≤ (1 + t ^ 2) ^ ((m + 1) / 2) := by
  rw [add_div, rpow_add (by positivity), ← sqrt_eq_rpow]
  gcongr
  exact abs_le_sqrt (by linarith)

/-- A linear weight is dominated by the Japanese bracket `⟨t⟩ = (1 + t ^ 2) ^ (1 / 2)`:
`(1 + c |t|) ^ p ≤ (1 + c) ^ p ⟨t⟩ ^ p` for `c ≥ 0` and `p ≥ 0`. -/
theorem one_add_mul_abs_rpow_le (t : ℝ) {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) :
    (1 + c * |t|) ^ p ≤ (1 + c) ^ p * (1 + t ^ 2) ^ (p / 2) := by
  have hle : 1 + c * |t| ≤ (1 + c) * √(1 + t ^ 2) := by
    have h1 := one_le_sqrt_one_add_sq t
    have h2 : |t| ≤ √(1 + t ^ 2) := by
      simpa only [zero_div, rpow_zero, one_mul, zero_add, ← sqrt_eq_rpow] using
        one_add_sq_rpow_mul_abs_le t 0
    nlinarith
  rw [rpow_div_two_eq_sqrt p (by positivity), ← mul_rpow (by positivity) (sqrt_nonneg _)]
  exact rpow_le_rpow (by positivity) hle hp

/-- For `0 ≤ F`, bounds `F ≤ C₀ w` and `t ^ (2N) F ≤ C₁ w` combine to the weighted bound
`F ≤ 2 ^ (N - 1) (C₀ + C₁) w ((1 + t²) ^ N)⁻¹`. -/
theorem le_mul_one_add_sq_pow_inv {t : ℝ} {N : ℕ} {F C₀ C₁ w : ℝ} (hF : 0 ≤ F)
    (h₀ : F ≤ C₀ * w) (h₁ : t ^ (2 * N) * F ≤ C₁ * w) :
    F ≤ 2 ^ (N - 1) * (C₀ + C₁) * w * ((1 + t ^ 2) ^ N)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm F]
  calc (1 + t ^ 2) ^ N * F ≤ 2 ^ (N - 1) * (1 ^ N + (t ^ 2) ^ N) * F :=
        mul_le_mul_of_nonneg_right (add_pow_le zero_le_one (sq_nonneg t) N) hF
    _ = 2 ^ (N - 1) * (F + t ^ (2 * N) * F) := by rw [one_pow, ← pow_mul]; ring
    _ ≤ 2 ^ (N - 1) * (C₀ * w + C₁ * w) :=
        mul_le_mul_of_nonneg_left (add_le_add h₀ h₁) (by positivity)
    _ = 2 ^ (N - 1) * (C₀ + C₁) * w := by ring

end Real
