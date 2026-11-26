/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The `Lᵖ` norm of a smooth bump

A smooth bump `f` centred at `c` in a finite-dimensional real normed space is continuous with
compact support and equals `1` at `c`. So it lies in every `Lᵖ` of a measure that is finite on
compact sets, and its `Lᵖ` norm is positive when the measure charges every nonempty open set and
`p ≠ 0` (`ContDiffBump.lpNorm_pos`).
-/

public section

open MeasureTheory

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] {c : E}

/-- A smooth bump has positive `Lᵖ` norm, for `p ≠ 0` and a measure that is finite on compact
sets and positive on nonempty open sets. -/
theorem lpNorm_pos (f : ContDiffBump c) {p : ENNReal} (hp : p ≠ 0) (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] : 0 < lpNorm f p μ := by
  refine lpNorm_nonneg.lt_of_ne fun h => ?_
  have hf : MemLp f p μ := f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have h0 : (f : E → ℝ) = 0 := (Continuous.ae_eq_iff_eq μ f.continuous continuous_const).1
    ((lpNorm_eq_zero hf hp).1 h.symm)
  have hc : f c = 1 := f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)
  exact one_ne_zero (hc.symm.trans (congrFun h0 c))

end ContDiffBump
