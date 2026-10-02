/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Identities for additive Haar measures

This file records real-valued forms of standard scaling identities for additive Haar measures,
and the translation of an integral over a ball to the corresponding ball about the origin.

## Main declarations

* `MeasureTheory.Measure.addHaar_real_ball_of_pos`: the real measure of a positive-radius ball.
* `TauCeti.setIntegral_ball_eq_setIntegral_ball_zero_add`: translating a ball integral to the
  origin.
-/

public section

open MeasureTheory Metric Module Set

namespace TauCeti

/-- The real measure of a ball of positive radius is the corresponding power of the radius times
the real measure of the unit ball. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_ball_of_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {r : ℝ} (hr : 0 < r) :
    mu.real (ball x r) = r ^ finrank ℝ E * mu.real (ball 0 1) := by
  rw [measureReal_def, mu.addHaar_ball_of_pos x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ← measureReal_def]

/-- The integral over the ball `ball x₀ R` is the integral over `ball 0 R` of the translate
`y ↦ f (y + x₀)`. -/
theorem setIntegral_ball_eq_setIntegral_ball_zero_add
    {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x₀ : E) (R : ℝ) :
    ∫ x in ball x₀ R, f x ∂μ = ∫ y in ball (0 : E) R, f (y + x₀) ∂μ := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
    ← integral_add_right_eq_self _ x₀]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  beta_reduce
  classical
  rw [indicator_apply, indicator_apply]
  simp only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]

end TauCeti
