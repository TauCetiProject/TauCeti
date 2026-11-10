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

end TauCeti
