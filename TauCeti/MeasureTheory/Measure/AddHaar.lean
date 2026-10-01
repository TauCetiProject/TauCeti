/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Real-valued identities for additive Haar measures

This file records real-valued forms of standard scaling identities for additive Haar measures.

## Main declarations

* `MeasureTheory.Measure.addHaar_real_ball_of_pos`: the real measure of a positive-radius ball.
-/

public section

open MeasureTheory Metric Module

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

end TauCeti
