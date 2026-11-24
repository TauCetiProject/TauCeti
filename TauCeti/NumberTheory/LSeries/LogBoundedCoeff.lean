/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds

/-!
# Dirichlet series with logarithmically bounded coefficients

Let `f : ℕ → ℂ` satisfy `‖f n‖ ≤ B log (n + 1)` for `n ≥ 1`. Then the `L`-series of `f`
converges absolutely on `Re s > 1`. For `0 < ε ≤ 1` the coefficients are at most
`(B / ε) n ^ ε`, so on `Re s > 1 + ε` the `L`-series is dominated by `B / ε` times
`ζ(Re s - ε) < 1 + 1 / (Re s - ε - 1)`. With `ε = (Re s - 1) / 2` this gives
`‖L(f, s)‖ ≤ 8 B / (Re s - 1) ^ 2` for `1 < Re s ≤ 3`.

## Main results

* `TauCeti.LSeries.LSeriesSummable_of_norm_le_mul_log`: absolute convergence on `Re s > 1`.
* `TauCeti.LSeries.norm_LSeries_le_of_norm_le_mul_log_of_lt`:
  `‖L(f, s)‖ ≤ (B / ε) (1 + 1 / (Re s - ε - 1))` for `0 < ε ≤ 1` and `1 + ε < Re s`.
* `TauCeti.LSeries.norm_LSeries_le_of_norm_le_mul_log`:
  `‖L(f, s)‖ ≤ 8 B / (Re s - 1) ^ 2` for `1 < Re s ≤ 3`.
-/

public section

open Complex

namespace TauCeti.LSeries

variable {f : ℕ → ℂ} {B : ℝ}

private theorem nonneg_of_norm_le_mul_log (hf : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ B * Real.log (n + 1)) :
    0 ≤ B := by
  have h1 := hf 1 le_rfl
  norm_num at h1
  exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h1) (Real.log_pos one_lt_two)

private theorem norm_term_le_of_norm_le_mul_log
    (hf : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ B * Real.log (n + 1)) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (s : ℂ) (n : ℕ) :
    ‖LSeries.term f s n‖ ≤ B / ε * ‖LSeries.term 1 ((s.re - ε : ℝ) : ℂ) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by positivity
  have hB := nonneg_of_norm_le_mul_log hf
  simp only [LSeries.norm_term_eq, hn, ↓reduceIte, Pi.one_apply, norm_one, ofReal_re]
  rw [Real.rpow_sub hn', one_div_div, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc ‖f n‖ ≤ B * Real.log (n + 1) := hf n (Nat.one_le_iff_ne_zero.mpr hn)
    _ ≤ B * ((n : ℝ) ^ ε / ε) :=
        mul_le_mul_of_nonneg_left (Real.log_add_one_le_rpow_div hn'.le hε hε₁) hB
    _ = B / ε * (n : ℝ) ^ ε := by ring

/-- If `‖f n‖ ≤ B log (n + 1)` for `n ≥ 1`, then the `L`-series of `f` converges absolutely
on `Re s > 1`. -/
theorem LSeriesSummable_of_norm_le_mul_log
    (hf : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ B * Real.log (n + 1)) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable f s := by
  have hε : 0 < min 1 ((s.re - 1) / 2) := lt_min one_pos (by linarith)
  have hσ : 1 < ((s.re - min 1 ((s.re - 1) / 2) : ℝ) : ℂ).re := by
    rw [ofReal_re]
    linarith [min_le_right 1 ((s.re - 1) / 2)]
  exact ((LSeriesSummable_one_iff.mpr hσ).norm.mul_left _).of_norm_bounded
    (norm_term_le_of_norm_le_mul_log hf hε (min_le_left _ _) s)

/-- If `‖f n‖ ≤ B log (n + 1)` for `n ≥ 1`, `0 < ε ≤ 1` and `1 + ε < Re s`, then
`‖L(f, s)‖ ≤ (B / ε) (1 + 1 / (Re s - ε - 1))`. -/
theorem norm_LSeries_le_of_norm_le_mul_log_of_lt
    (hf : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ B * Real.log (n + 1)) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    {s : ℂ} (hs : 1 + ε < s.re) :
    ‖LSeries f s‖ ≤ B / ε * (1 + 1 / (s.re - ε - 1)) := by
  set τ : ℂ := ((s.re - ε : ℝ) : ℂ)
  have hτ : 1 < τ.re := by simp only [τ, ofReal_re]; linarith
  have hsum := (LSeriesSummable_one_iff.mpr hτ).norm
  have hreal (n : ℕ) : LSeries.term 1 τ n = ((‖LSeries.term 1 τ n‖ : ℝ) : ℂ) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn, Pi.one_apply, ← ofReal_natCast,
      ← ofReal_cpow (Nat.cast_nonneg n), ← ofReal_one, ← ofReal_div, norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hζ : ∑' n, ‖LSeries.term 1 τ n‖ < 1 + 1 / (s.re - ε - 1) := by
    have h := norm_riemannZeta_lt_one_add_one_div_sub_one hτ
    rwa [← LSeries_one_eq_riemannZeta hτ, LSeries, tsum_congr hreal, ← ofReal_tsum, norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _), ofReal_re] at h
  have hB : 0 ≤ B / ε := div_nonneg (nonneg_of_norm_le_mul_log hf) hε.le
  calc ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f s n‖ :=
        norm_tsum_le_tsum_norm (LSeriesSummable_of_norm_le_mul_log hf (by linarith)).norm
    _ ≤ ∑' n, B / ε * ‖LSeries.term 1 τ n‖ :=
        (LSeriesSummable_of_norm_le_mul_log hf (by linarith)).norm.tsum_le_tsum
          (norm_term_le_of_norm_le_mul_log hf hε hε₁ s) (hsum.mul_left _)
    _ = B / ε * ∑' n, ‖LSeries.term 1 τ n‖ := tsum_mul_left
    _ ≤ B / ε * (1 + 1 / (s.re - ε - 1)) := mul_le_mul_of_nonneg_left hζ.le hB

/-- If `‖f n‖ ≤ B log (n + 1)` for `n ≥ 1` and `1 < Re s ≤ 3`, then
`‖L(f, s)‖ ≤ 8 B / (Re s - 1) ^ 2`. -/
theorem norm_LSeries_le_of_norm_le_mul_log
    (hf : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ B * Real.log (n + 1)) {s : ℂ} (hs : 1 < s.re)
    (hs₃ : s.re ≤ 3) :
    ‖LSeries f s‖ ≤ 8 * B / (s.re - 1) ^ 2 := by
  have hB := nonneg_of_norm_le_mul_log hf
  calc ‖LSeries f s‖ ≤ B / ((s.re - 1) / 2) * (1 + 1 / (s.re - (s.re - 1) / 2 - 1)) :=
        norm_LSeries_le_of_norm_le_mul_log_of_lt hf (by linarith) (by linarith) (by linarith)
    _ = 2 * B * (s.re + 1) / (s.re - 1) ^ 2 := by
        rw [show s.re - (s.re - 1) / 2 - 1 = (s.re - 1) / 2 by ring]
        field_simp [(by linarith : s.re - 1 ≠ 0)]
        ring
    _ ≤ 8 * B / (s.re - 1) ^ 2 := div_le_div_of_nonneg_right (by nlinarith) (by positivity)

end TauCeti.LSeries
