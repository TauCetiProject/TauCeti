/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Additive Haar measures on real normed spaces

In a finite-dimensional real normed space, the real measure of a positive-radius ball is its
radius raised to the dimension times the real measure of the unit ball, independently of its
centre. Consequently the ratio of the measures of two closed balls is controlled by the ratio of
their radii raised to the dimension.

## Main results

* `MeasureTheory.Measure.addHaar_real_ball_of_pos`: the real measure of a positive-radius ball.
* `MeasureTheory.Measure.addHaar_real_closedBall_div_le`: a closed ball of radius `R ≤ c r` has
  at most `cⁿ` times the measure of a closed ball of radius `r`.
-/

public section

open MeasureTheory MeasureTheory.Measure Metric Module

namespace TauCeti

/-- The real measure of a ball of positive radius is the corresponding power of the radius times
the real measure of the unit ball. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_ball_of_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {r : ℝ} (hr : 0 < r) :
    mu.real (ball x r) = r ^ finrank ℝ E * mu.real (ball 0 1) := by
  rw [measureReal_def, mu.addHaar_ball_of_pos x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ← measureReal_def]

/-- A closed ball of radius `R ≤ c r` has at most `cⁿ` times the real measure of a closed ball of
radius `r > 0`, whatever their centres, where `n` is the dimension. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_closedBall_div_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x y : E) {c r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hRr : R ≤ c * r) :
    mu.real (closedBall x R) / mu.real (closedBall y r) ≤ c ^ finrank ℝ E := by
  have hball : 0 < mu.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne
  rw [mu.addHaar_real_closedBall x hR, mu.addHaar_real_closedBall y hr.le,
    mul_div_mul_right _ _ hball.ne', div_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ hR hRr _

end TauCeti

end
