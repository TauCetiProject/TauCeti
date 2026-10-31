/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Diameters of balls in metric spaces

A closed ball of radius `r` has extended diameter at most `2 r`
(`Metric.ediam_closedBall_le`). This is the extended-diameter counterpart of Mathlib's
`Metric.diam_closedBall`, stated for every real radius: a ball of negative radius is empty.
-/

public section

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A closed ball of radius `r` has extended diameter at most `2 r`. -/
theorem ediam_closedBall_le (x : X) (r : ℝ) :
    ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) :=
  ediam_le_of_forall_dist_le fun y hy z hz => (dist_triangle_right y z x).trans <| by
    linarith [mem_closedBall.1 hy, mem_closedBall.1 hz]

end Metric
