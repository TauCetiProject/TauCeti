/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# Exponential integrability from a series of moments

Let `g : ℝ → ℝ` be nonnegative at almost every `u > u₀`. The functions
`G n u = (t * u) ^ n / n ! * g u` sum pointwise to `exp (t * u) * g u`. This file shows that if
each `G n` is integrable on `(0, ∞)` and the integrals of the `G n` are summable, then so are the
integrals of their absolute values, and `u ↦ exp (t * u) * g u` is integrable on `(0, ∞)`.

The sign condition is what makes this work: right of `u₀` the terms `G n` have the constant sign
of `t ^ n`, so there `∫ |G n|` is controlled by `|∫ G n|`, while on `(0, u₀]` the weight
`(t * u) ^ n / n !` is at most `(|t| * |u₀|) ^ n / n !`, a summable sequence. Without it the
statement fails: Stieltjes' function `g u = exp (-u ^ (1 / 4)) * sin (u ^ (1 / 4))` has all moments
`∫ u ^ n * g u` equal to zero, while `exp u * g u` is not integrable.

This is the measure-theoretic step of Landau's theorem for Laplace transforms,
`TauCeti.integrableOn_cexp_neg_mul_smul_ofReal_of_ae_nonneg`, where the integrals of the `G n` are
the terms of a Taylor series.

## Main results

* `TauCeti.summable_integral_norm_pow_div_factorial_mul`: summability of the integrals of
  `|G n|`.
* `TauCeti.integrable_exp_mul_of_summable_integral`: integrability of `u ↦ exp (t * u) * g u` on
  `(0, ∞)`.
-/

public section

open MeasureTheory Set
open scoped Nat

namespace TauCeti

variable {g : ℝ → ℝ} {t u₀ : ℝ}

/-- If `g` is nonnegative at almost every `u > u₀`, then on `(0, ∞)` the absolute value of
`(t * u) ^ n / n ! * g u` is at most `ε * ((t * u) ^ n / n ! * g u) + 2 * C * |g u|`, where
`ε * t ^ n = |t| ^ n` and `C = (|t| * |u₀|) ^ n / n !`. -/
private theorem norm_pow_div_factorial_mul_le {ε : ℝ} {n : ℕ}
    (hε : ∀ u, ε * (t * u) ^ n = (|t| * u) ^ n)
    (hg : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), u₀ < u → 0 ≤ g u) :
    ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ‖(t * u) ^ n / (n ! : ℝ) * g u‖ ≤
      ε * ((t * u) ^ n / (n ! : ℝ) * g u) + 2 * ((|t| * |u₀|) ^ n / (n ! : ℝ)) * ‖g u‖ := by
  filter_upwards [hg, ae_restrict_mem measurableSet_Ioi] with u hu (hu0 : 0 < u)
  have hc : 0 ≤ (|t| * u) ^ n / (n ! : ℝ) := by positivity
  have hC : 0 ≤ (|t| * |u₀|) ^ n / (n ! : ℝ) := by positivity
  have hsign : ε * ((t * u) ^ n / (n ! : ℝ) * g u) = (|t| * u) ^ n / (n ! : ℝ) * g u := by
    rw [← hε u]
    ring
  have hnorm : ‖(t * u) ^ n / (n ! : ℝ) * g u‖ = (|t| * u) ^ n / (n ! : ℝ) * |g u| := by
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_mul, abs_of_pos hu0, Nat.abs_cast]
  rw [hsign, hnorm, Real.norm_eq_abs]
  rcases lt_or_ge u₀ u with h | h
  · rw [abs_of_nonneg (hu h)]
    linarith [mul_nonneg (mul_nonneg zero_le_two hC) (hu h)]
  · have hcC : (|t| * u) ^ n / (n ! : ℝ) ≤ (|t| * |u₀|) ^ n / (n ! : ℝ) := by
      gcongr
      exact h.trans (le_abs_self _)
    nlinarith [mul_le_mul_of_nonneg_right hcC (abs_nonneg (g u)),
      mul_le_mul_of_nonneg_left (neg_abs_le (g u)) hc]

/-- If `g` is nonnegative at almost every `u > u₀`, the functions
`u ↦ (t * u) ^ n / n ! * g u` are integrable on `(0, ∞)` and their integrals are summable, then the
integrals of their absolute values are summable. -/
theorem summable_integral_norm_pow_div_factorial_mul
    (hg : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), u₀ < u → 0 ≤ g u)
    (hint : ∀ n : ℕ, Integrable (fun u ↦ (t * u) ^ n / (n ! : ℝ) * g u) (volume.restrict (Ioi 0)))
    (hsum : Summable fun n : ℕ ↦ ∫ u in Ioi 0, (t * u) ^ n / (n ! : ℝ) * g u) :
    Summable fun n : ℕ ↦ ∫ u in Ioi 0, ‖(t * u) ^ n / (n ! : ℝ) * g u‖ := by
  have hg0 : Integrable g (volume.restrict (Ioi 0)) := by simpa using hint 0
  have hbound : ∀ n : ℕ, ∫ u in Ioi 0, ‖(t * u) ^ n / (n ! : ℝ) * g u‖ ≤
      ‖∫ u in Ioi 0, (t * u) ^ n / (n ! : ℝ) * g u‖ +
        2 * ((|t| * |u₀|) ^ n / (n ! : ℝ)) * ∫ u in Ioi 0, ‖g u‖ := by
    intro n
    -- `ε = ±1` turns `(t * u) ^ n` into `(|t| * u) ^ n`.
    obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℝ, |ε| ≤ 1 ∧ ∀ u, ε * (t * u) ^ n = (|t| * u) ^ n := by
      rcases le_or_gt 0 t with ht | ht
      · exact ⟨1, by simp, fun u ↦ by rw [abs_of_nonneg ht, one_mul]⟩
      · exact ⟨(-1) ^ n, by simp, fun u ↦ by rw [abs_of_neg ht, neg_mul, neg_pow (t * u)]⟩
    calc ∫ u in Ioi 0, ‖(t * u) ^ n / (n ! : ℝ) * g u‖
        ≤ ∫ u in Ioi 0, (ε * ((t * u) ^ n / (n ! : ℝ) * g u) +
            2 * ((|t| * |u₀|) ^ n / (n ! : ℝ)) * ‖g u‖) :=
          integral_mono_ae (hint n).norm (((hint n).const_mul ε).add (hg0.norm.const_mul _))
            (norm_pow_div_factorial_mul_le hε hg)
      _ = ε * (∫ u in Ioi 0, (t * u) ^ n / (n ! : ℝ) * g u) +
            2 * ((|t| * |u₀|) ^ n / (n ! : ℝ)) * ∫ u in Ioi 0, ‖g u‖ := by
          rw [integral_add ((hint n).const_mul ε) (hg0.norm.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by
          gcongr
          rw [Real.norm_eq_abs]
          refine (le_abs_self _).trans ?_
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) hε1
  exact Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) hbound
    (hsum.norm.add (((Real.summable_pow_div_factorial (|t| * |u₀|)).mul_left 2).mul_right _))

/-- If `g` is nonnegative at almost every `u > u₀`, the functions
`u ↦ (t * u) ^ n / n ! * g u` are integrable on `(0, ∞)` and their integrals are summable, then
`u ↦ exp (t * u) * g u` is integrable on `(0, ∞)`. -/
theorem integrable_exp_mul_of_summable_integral
    (hg : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), u₀ < u → 0 ≤ g u)
    (hint : ∀ n : ℕ, Integrable (fun u ↦ (t * u) ^ n / (n ! : ℝ) * g u) (volume.restrict (Ioi 0)))
    (hsum : Summable fun n : ℕ ↦ ∫ u in Ioi 0, (t * u) ^ n / (n ! : ℝ) * g u) :
    Integrable (fun u ↦ Real.exp (t * u) * g u) (volume.restrict (Ioi 0)) := by
  refine integrable_of_hasSum_of_summable_integral_norm hint
    (summable_integral_norm_pow_div_factorial_mul hg hint hsum) (.of_forall fun u ↦ ?_)
  have h0 : HasSum (fun n : ℕ ↦ (t * u) ^ n / (n ! : ℝ)) (Real.exp (t * u)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (t * u)
  exact h0.mul_right (g u)

end TauCeti
