/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Balls of extended radius in ultrametric spaces

In an ultrametric pseudometric space the extended distance satisfies the strong triangle
inequality `edist x z ≤ max (edist x y) (edist y z)`. Consequently every point of an open ball
`Metric.eball x r` of extended radius `r : ℝ≥0∞` is a centre of it, and the ball of any radius
`r' ≤ r` about such a point lies inside it. These are the extended-radius forms of Mathlib's
`IsUltrametricDist.ball_eq_of_mem`. They allow radius `⊤`, as needed for entire functions.
-/

public section

open Metric
open scoped ENNReal

namespace IsUltrametricDist

variable {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]

/-- The strong triangle inequality for the extended distance of an ultrametric space. -/
lemma edist_triangle_max (x y z : X) : edist x z ≤ max (edist x y) (edist y z) := by
  simp only [edist_dist, ← ENNReal.ofReal_max]
  exact ENNReal.ofReal_le_ofReal (dist_triangle_max x y z)

/-- In an ultrametric space, the open ball of radius `r' ≤ r` about a point of the open ball
`Metric.eball x r` lies inside `Metric.eball x r`. -/
lemma eball_subset_eball_of_mem {x y : X} {r r' : ℝ≥0∞} (h : y ∈ eball x r) (hr : r' ≤ r) :
    eball y r' ⊆ eball x r :=
  fun _ hz ↦ (edist_triangle_max _ y x).trans_lt (max_lt (lt_of_lt_of_le hz hr) h)

/-- In an ultrametric space, every point of an open ball of extended radius is a centre of it. -/
lemma eball_eq_of_mem {x y : X} {r : ℝ≥0∞} (h : y ∈ eball x r) : eball x r = eball y r :=
  (eball_subset_eball_of_mem (mem_eball_comm.mp h) le_rfl).antisymm
    (eball_subset_eball_of_mem h le_rfl)

end IsUltrametricDist
