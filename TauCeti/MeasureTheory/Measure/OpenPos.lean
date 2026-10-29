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
measure `μ.real`. For a locally finite measure, closed balls of small positive radius around a
point have positive finite measure, so proportions of sets in shrinking balls are well behaved.

## Main results

* `Metric.measureReal_ball_pos`: a ball of positive radius has positive real measure.
* `Metric.eventually_measure_closedBall_ne_zero_ne_top`: closed balls of small positive radius
  have positive finite measure.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace TauCeti

/-- In a proper space, a measure that is positive on nonempty open sets and finite on compact sets
gives every ball of positive radius positive real measure. -/
theorem _root_.Metric.measureReal_ball_pos {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ.real (Metric.ball x r) :=
  ENNReal.toReal_pos (Metric.measure_ball_pos μ x hr).ne' measure_ball_lt_top.ne

/-- For a locally finite measure that is positive on nonempty open sets, closed balls of small
positive radius around a point have positive finite measure. -/
theorem _root_.Metric.eventually_measure_closedBall_ne_zero_ne_top {X : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (x : X) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (Metric.closedBall x r) ≠ 0 ∧ μ (Metric.closedBall x r) ≠ ∞ := by
  obtain ⟨U, hU, hUμ⟩ := μ.finiteAt_nhds x
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  exact ⟨(Metric.measure_closedBall_pos μ x hr.1).ne',
    ((measure_mono ((Metric.closedBall_subset_ball hr.2).trans hεU)).trans_lt hUμ).ne⟩

end TauCeti

end
