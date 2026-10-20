/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Real measures of balls under a measure positive on open sets

Mathlib's `Metric.measure_ball_pos` says that a measure positive on nonempty open sets gives
positive measure to every ball of positive radius. In a proper space, where balls are bounded and
so have finite measure under a measure finite on compact sets, the same holds for the real-valued
measure `μ.real`, and likewise for closed balls.

## Main results

* `Metric.measureReal_ball_pos`: a ball of positive radius has positive real measure.
* `Metric.measureReal_closedBall_pos`: a closed ball of positive radius has positive real
  measure.
-/

public section

open MeasureTheory

namespace TauCeti

/-- In a proper space, a measure that is positive on nonempty open sets and finite on compact sets
gives every ball of positive radius positive real measure. -/
theorem _root_.Metric.measureReal_ball_pos {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ.real (Metric.ball x r) :=
  ENNReal.toReal_pos (Metric.measure_ball_pos μ x hr).ne' measure_ball_lt_top.ne

/-- In a proper space, a measure that is positive on nonempty open sets and finite on compact sets
gives every closed ball of positive radius positive real measure. -/
theorem _root_.Metric.measureReal_closedBall_pos {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ.real (Metric.closedBall x r) :=
  ENNReal.toReal_pos (Metric.measure_closedBall_pos μ x hr).ne' measure_closedBall_lt_top.ne

end TauCeti

end
