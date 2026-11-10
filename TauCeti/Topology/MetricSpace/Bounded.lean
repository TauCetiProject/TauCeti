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

In a bounded space any two points are within the diameter of the whole space
(`Metric.edist_le_diam_univ`), in the extended form used by Mathlib's Hölder bounds.
-/

public section

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A closed ball of radius `r` has extended diameter at most `2 r`. -/
theorem ediam_closedBall_le (x : X) (r : ℝ) :
    ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) :=
  ediam_le_of_forall_dist_le fun y hy z hz => (dist_triangle_right y z x).trans <| by
    linarith [mem_closedBall.1 hy, mem_closedBall.1 hz]

/-- In a bounded space any two points are within the diameter of the whole space. -/
theorem edist_le_diam_univ [BoundedSpace X] (x y : X) :
    edist x y ≤ ((diam (Set.univ : Set X)).toNNReal : ENNReal) := by
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (dist_le_diam_of_mem (Bornology.isBounded_univ.2 inferInstance)
    (Set.mem_univ x) (Set.mem_univ y))

end Metric
