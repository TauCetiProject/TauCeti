/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Continuity of the measure of a ball in its radius

For a finite measure for which every sphere about `x` is null, the measure of the open ball
`B(x, r)` is a continuous function of the radius `r`
(`MeasureTheory.Measure.continuous_measure_ball_of_measure_sphere_eq_zero`). This applies, for
instance, to every finite measure absolutely continuous with respect to an additive Haar measure on
a nontrivial finite-dimensional real normed space.

## Main statements

* `MeasureTheory.Measure.continuous_measure_ball_of_measure_sphere_eq_zero`: for a finite measure
  with null spheres about `x`, the measure of `ball x r` is continuous in `r`.
-/

public section

namespace MeasureTheory.Measure

open Metric Filter Set

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- **The measure of a ball is continuous in the radius.** For a finite measure for which every
sphere about `x` is null, the measure of the open ball `B(x, r)` is continuous in `r`: as `r → r₀`,
the indicators of the balls converge to that of `B(x, r₀)` off the sphere of radius `r₀`. -/
theorem continuous_measure_ball_of_measure_sphere_eq_zero [OpensMeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (x : X) (h : ∀ r, μ (sphere x r) = 0) :
    Continuous fun r : ℝ => μ (ball x r) := by
  refine continuous_iff_continuousAt.2 fun r₀ => ?_
  refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure _ measurableSet_ball
    (fun _ => measurableSet_ball) ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h r₀)] with y hy
  rw [mem_sphere] at hy
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · filter_upwards [lt_mem_nhds hlt] with r hr
    simp [hlt, hr]
  · filter_upwards [gt_mem_nhds hgt] with r hr
    simp [not_lt.2 hgt.le, not_lt.2 hr.le]

end MeasureTheory.Measure
