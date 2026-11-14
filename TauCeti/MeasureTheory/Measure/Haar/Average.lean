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
* `TauCeti.measure_ball_le_ofReal_mul_measure_ball_sdiff`: if `B(x, ρ) ⊆ B(x₀, R)` and a set `S`
  misses the proportion `θ` of `B(x, ρ)`, then it misses the proportion `θ (ρ / R) ^ dim E` of
  `B(x₀, R)`.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module
open scoped ENNReal NNReal

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

/-- A set missing a fixed proportion of a ball misses a proportion of every larger ball: if
`B(x, ρ) ⊆ B(x₀, R)` and `θ μ(B(x, ρ)) ≤ μ(B(x, ρ) \ S)` with `θ ≠ 0`, then

`μ(B(x₀, R)) ≤ (R / ρ) ^ dim E θ⁻¹ μ(B(x₀, R) \ S)`.

This transfers an exterior measure density condition at a point `x ∉ Ω` to the balls around
nearby centres. -/
theorem measure_ball_le_ofReal_mul_measure_ball_sdiff {S : Set E} {x x₀ : E} {ρ R : ℝ}
    {θ : ℝ≥0} (hθ : θ ≠ 0) (hρ : 0 < ρ) (hsub : ball x ρ ⊆ ball x₀ R)
    (hdens : (θ : ℝ≥0∞) * μ (ball x ρ) ≤ μ (ball x ρ \ S)) :
    μ (ball x₀ R) ≤ ENNReal.ofReal ((R / ρ) ^ finrank ℝ E * (θ : ℝ)⁻¹) * μ (ball x₀ R \ S) := by
  have hR : 0 < R := dist_nonneg.trans_lt (mem_ball.1 (hsub (mem_ball_self hρ)))
  have hball : μ (ball x₀ R) = ENNReal.ofReal ((R / ρ) ^ finrank ℝ E) * μ (ball x ρ) := by
    conv_lhs => rw [← div_mul_cancel₀ R hρ.ne']
    rw [Measure.addHaar_ball_mul_of_pos μ x₀ (div_pos hR hρ), Measure.addHaar_ball_center μ x]
  have hθ0 : (θ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hθ
  have hx : μ (ball x ρ) ≤ (θ : ℝ≥0∞)⁻¹ * μ (ball x₀ R \ S) :=
    calc μ (ball x ρ) = (θ : ℝ≥0∞)⁻¹ * ((θ : ℝ≥0∞) * μ (ball x ρ)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hθ0 ENNReal.coe_ne_top, one_mul]
      _ ≤ (θ : ℝ≥0∞)⁻¹ * μ (ball x₀ R \ S) := by
          gcongr
          exact hdens.trans (measure_mono (Set.sdiff_subset_sdiff_left hsub))
  rw [hball, ENNReal.ofReal_mul (by positivity), mul_assoc,
    ENNReal.ofReal_inv_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hθ)),
    ENNReal.ofReal_coe_nnreal]
  gcongr

end TauCeti
