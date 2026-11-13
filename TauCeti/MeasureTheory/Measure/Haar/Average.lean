/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Integral.Average

/-!
# Averages over balls for an additive Haar measure

For an additive Haar measure on a finite-dimensional real normed space, the measure of a ball of
radius `R` is `(R / ρ) ^ dim E` times the measure of a ball of radius `ρ`. Consequently the average
of a nonnegative function over a ball `B(x, ρ) ⊆ B(x₀, R)` is at most `(R / ρ) ^ dim E` times its
average over `B(x₀, R)`: the integral can only grow on the larger ball, and the ratio of the
volumes is explicit. This comparison is the basic step of stopping-time arguments with balls.

## Main statements

* `TauCeti.setLAverage_ball_le`: the average over `B(x, ρ) ⊆ B(x₀, R)` is at most
  `(R / ρ) ^ dim E` times the average over `B(x₀, R)`.
* `TauCeti.ofReal_mul_div_pow_le_setLAverage_enorm_sub`: if `‖f - a‖ ≥ δ` on `B(z, ρ) ⊆ B(c, r)`,
  the average of `‖f - a‖` over `B(c, r)` is at least `δ (ρ / r) ^ dim E`.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The average over a ball `B(x, ρ) ⊆ B(x₀, R)` is at most `(R / ρ) ^ dim E` times the average over
`B(x₀, R)`. -/
theorem setLAverage_ball_le (g : E → ℝ≥0∞) {x x₀ : E} {ρ R : ℝ} (hρ : 0 < ρ)
    (hsub : ball x ρ ⊆ ball x₀ R) :
    ⨍⁻ y in ball x ρ, g y ∂μ ≤
      ENNReal.ofReal ((R / ρ) ^ finrank ℝ E) * ⨍⁻ y in ball x₀ R, g y ∂μ := by
  have hR : 0 < R := by
    have := hsub (mem_ball_self hρ)
    exact dist_nonneg.trans_lt (mem_ball.1 this)
  refine (setLAverage_le_div_mul_setLAverage_of_subset hsub measure_ball_lt_top.ne).trans_eq ?_
  congr 1
  have hball : μ (ball x₀ R) = ENNReal.ofReal ((R / ρ) ^ finrank ℝ E) * μ (ball x ρ) := by
    conv_lhs => rw [← div_mul_cancel₀ R hρ.ne']
    rw [Measure.addHaar_ball_mul_of_pos μ x₀ (div_pos hR hρ), Measure.addHaar_ball_center μ x]
  rw [hball, ENNReal.mul_div_cancel_right (measure_ball_pos μ x hρ).ne' measure_ball_lt_top.ne]

/-- **A lower bound from a sub-ball.** If `‖f - a‖ ≥ δ` on a ball `B(z, ρ) ⊆ B(c, r)`, then the
mean of `‖f - a‖` over `B(c, r)` is at least `δ (ρ / r) ^ dim E`. With `a` the average of `f` over
`B(c, r)`, this bounds the mean oscillation of `f` on `B(c, r)` from below. -/
theorem ofReal_mul_div_pow_le_setLAverage_enorm_sub {F : Type*} [NormedAddCommGroup F]
    {f : E → F} {a : F} {c z : E} {r ρ δ : ℝ} (hρ : 0 < ρ) (hsub : ball z ρ ⊆ ball c r)
    (h : ∀ y ∈ ball z ρ, ENNReal.ofReal δ ≤ ‖f y - a‖ₑ) :
    ENNReal.ofReal (δ * (ρ / r) ^ finrank ℝ E) ≤ ⨍⁻ y in ball c r, ‖f y - a‖ₑ ∂μ := by
  have hr : 0 < r := pos_of_mem_ball (hsub (mem_ball_self hρ))
  have hpos : μ (ball c r) ≠ 0 := (measure_ball_pos μ c hr).ne'
  have htop : μ (ball c r) ≠ ∞ := measure_ball_lt_top.ne
  have hball : μ (ball z ρ) = ENNReal.ofReal ((ρ / r) ^ finrank ℝ E) * μ (ball c r) := by
    rw [μ.addHaar_ball_of_pos z hρ, μ.addHaar_ball_of_pos c hr, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), div_pow, div_mul_cancel₀ _ (by positivity)]
  rw [setLAverage_eq, ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl htop)]
  calc ENNReal.ofReal (δ * (ρ / r) ^ finrank ℝ E) * μ (ball c r)
      = ENNReal.ofReal δ * μ (ball z ρ) := by
        rw [hball, ← mul_assoc, ← ENNReal.ofReal_mul' (by positivity)]
    _ = ∫⁻ _ in ball z ρ, ENNReal.ofReal δ ∂μ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ y in ball z ρ, ‖f y - a‖ₑ ∂μ := setLIntegral_mono' measurableSet_ball h
    _ ≤ ∫⁻ y in ball c r, ‖f y - a‖ₑ ∂μ := lintegral_mono_set hsub

end TauCeti
