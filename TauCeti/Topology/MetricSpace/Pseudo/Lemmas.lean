/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Frontiers of annuli and half-balls in pseudo-metric spaces

The frontier of the closed annulus `closedBall y R \ ball y r` lies on its two boundary spheres
(`TauCeti.frontier_closedBall_sdiff_ball_subset`). For a continuous real function `t`, the
frontier of the half-ball `closedBall y R ∩ {x | 0 ≤ t x}` lies on the sphere and the zero set
of `t` (`Continuous.frontier_closedBall_inter_setOf_nonneg_subset`).
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

/-- For a continuous real function `t`, the frontier of the half-ball
`closedBall y R ∩ {x | 0 ≤ t x}` lies on the sphere and the zero set of `t`. -/
theorem _root_.Continuous.frontier_closedBall_inter_setOf_nonneg_subset {t : X → ℝ}
    (ht : Continuous t) (y : X) (R : ℝ) :
    frontier (closedBall y R ∩ {x | 0 ≤ t x}) ⊆ sphere y R ∪ {x | t x = 0} :=
  (frontier_inter_subset _ _).trans (union_subset_union
    (inter_subset_left.trans frontier_closedBall_subset_sphere)
    (inter_subset_right.trans ((frontier_le_subset_eq continuous_const ht).trans
      fun _ hx ↦ Eq.symm hx)))

end TauCeti
