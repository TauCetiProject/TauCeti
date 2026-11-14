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
* `TauCeti.mul_ofReal_div_pow_le_setLAverage_ball`: if `g ≥ δ` on `B(z, ρ) ⊆ B(c, r)`, the
  average of `g` over `B(c, r)` is at least `δ (ρ / r) ^ dim E`.
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

/-- **A lower bound from a sub-ball.** If `g ≥ δ` on a ball `B(z, ρ) ⊆ B(c, r)`, then the average
of `g` over `B(c, r)` is at least `δ (ρ / r) ^ dim E`. With `g = ‖f - a‖ₑ` and `a` the average of
`f` over `B(c, r)`, this bounds the mean oscillation of `f` on `B(c, r)` from below. -/
theorem mul_ofReal_div_pow_le_setLAverage_ball {g : E → ℝ≥0∞} {c z : E} {r ρ : ℝ} {δ : ℝ≥0∞}
    (hρ : 0 < ρ) (hsub : ball z ρ ⊆ ball c r) (h : ∀ y ∈ ball z ρ, δ ≤ g y) :
    δ * ENNReal.ofReal ((ρ / r) ^ finrank ℝ E) ≤ ⨍⁻ y in ball c r, g y ∂μ := by
  have hr : 0 < r := pos_of_mem_ball (hsub (mem_ball_self hρ))
  have hδ : δ ≤ ⨍⁻ y in ball z ρ, g y ∂μ := by
    rw [← setLAverage_const (μ := μ) (measure_ball_pos μ z hρ).ne' measure_ball_lt_top.ne δ]
    exact laverage_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ h))
  calc δ * ENNReal.ofReal ((ρ / r) ^ finrank ℝ E)
      ≤ ENNReal.ofReal ((r / ρ) ^ finrank ℝ E) * (⨍⁻ y in ball c r, g y ∂μ) *
          ENNReal.ofReal ((ρ / r) ^ finrank ℝ E) := by
        gcongr
        exact hδ.trans (setLAverage_ball_le g hρ hsub)
    _ = ⨍⁻ y in ball c r, g y ∂μ := by
        rw [mul_comm, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
          div_mul_div_comm, mul_comm ρ r, div_self (by positivity), one_pow, ENNReal.ofReal_one,
          one_mul]

end TauCeti
