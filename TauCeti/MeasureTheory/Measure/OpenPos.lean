/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Measures of balls under a measure positive on open sets

Mathlib's `Metric.measure_ball_pos` says that a measure positive on nonempty open sets gives
positive measure to every ball of positive radius. In a proper space, where balls are bounded and
so have finite measure under a measure finite on compact sets, the same holds for the real-valued
measure `μ.real`. Without properness, a locally finite measure still gives finite measure to
small balls, so small closed balls of positive radius have positive finite measure; this is the
standing condition for ratios `μ (s ∩ closedBall x r) / μ (closedBall x r)` to behave as
proportions.

## Main results

* `Metric.measureReal_ball_pos`: a ball of positive radius has positive real measure.
* `Metric.eventually_measure_closedBall_ne_zero_ne_top`: for a locally finite measure positive
  on open sets, closed balls of small positive radius have positive finite measure.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace TauCeti

/-- In a proper space, a measure that is positive on nonempty open sets and finite on compact sets
gives every ball of positive radius positive real measure. -/
theorem _root_.Metric.measureReal_ball_pos {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ.real (Metric.ball x r) :=
  ENNReal.toReal_pos (Metric.measure_ball_pos μ x hr).ne' measure_ball_lt_top.ne

/-- For a locally finite measure that is positive on nonempty open sets, closed balls around `x`
of small positive radius have positive finite measure. -/
theorem _root_.Metric.eventually_measure_closedBall_ne_zero_ne_top {X : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (x : X) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (Metric.closedBall x r) ≠ 0 ∧ μ (Metric.closedBall x r) ≠ ∞ := by
  obtain ⟨u, hu, hμu⟩ := μ.finiteAt_nhds x
  obtain ⟨ε, hε, hεu⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hu
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  exact ⟨(Metric.measure_closedBall_pos μ x hr.1).ne',
    ((measure_mono ((Metric.closedBall_subset_closedBall hr.2.le).trans hεu)).trans_lt hμu).ne⟩

end TauCeti

end
