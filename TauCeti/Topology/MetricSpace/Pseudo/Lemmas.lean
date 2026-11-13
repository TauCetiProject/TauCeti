/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Frontiers of annuli in pseudo-metric spaces

The frontiers of the closed annulus `closedBall y R \ ball y r` and of the open annulus
`ball y R \ closedBall y r` lie on their two boundary spheres
(`TauCeti.frontier_closedBall_sdiff_ball_subset`, `TauCeti.frontier_ball_sdiff_closedBall_subset`).
-/

public section

namespace TauCeti

open Metric Set

variable {X : Type*} [PseudoMetricSpace X]

/-- The frontier of the closed annulus `closedBall y R \ ball y r` lies on its two boundary
spheres. -/
theorem frontier_closedBall_sdiff_ball_subset (y : X) (r R : ℝ) :
    frontier (closedBall y R \ ball y r) ⊆ sphere y R ∪ sphere y r := by
  rw [sdiff_eq]
  refine (frontier_inter_subset _ _).trans (union_subset_union ?_ ?_)
  · exact inter_subset_left.trans frontier_closedBall_subset_sphere
  · rw [frontier_compl]
    exact inter_subset_right.trans frontier_ball_subset_sphere

/-- The frontier of the open annulus `ball y R \ closedBall y r` lies on its two boundary
spheres. -/
theorem frontier_ball_sdiff_closedBall_subset (y : X) (r R : ℝ) :
    frontier (ball y R \ closedBall y r) ⊆ sphere y R ∪ sphere y r := by
  rw [sdiff_eq]
  refine (frontier_inter_subset _ _).trans (union_subset_union ?_ ?_)
  · exact inter_subset_left.trans frontier_ball_subset_sphere
  · rw [frontier_compl]
    exact inter_subset_right.trans frontier_closedBall_subset_sphere

end TauCeti
