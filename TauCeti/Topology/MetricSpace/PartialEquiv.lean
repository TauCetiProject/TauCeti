/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Logic.Equiv.PartialEquiv

/-!
# Ball control for radial partial equivalences

A partial equivalence preserving distance from distinguished centers maps every source
closed ball in its domain into the corresponding target closed ball. If its target contains
an open ball, its inverse lifts that ball into the corresponding source closed ball.
-/

public section

open Set Metric

namespace PartialEquiv

variable {E X : Type*} [PseudoMetricSpace E] [PseudoMetricSpace X]

/-- A radial partial equivalence maps a source closed ball in its domain into the target
closed ball of the same radius. -/
theorem mapsTo_closedBall_of_dist_eq (Φ : PartialEquiv E X) {a : E} {q : X} {r : ℝ}
    (hsource : closedBall a r ⊆ Φ.source)
    (hradial : ∀ x ∈ Φ.source, dist (Φ x) q = dist x a) :
    MapsTo Φ (closedBall a r) (closedBall q r) := by
  intro x hx
  rw [Metric.mem_closedBall, hradial x (hsource hx)]
  exact Metric.mem_closedBall.mp hx

/-- If the target of a radial partial equivalence contains a ball, that ball is covered by
the image of the source closed ball of the same radius. -/
theorem ball_subset_image_closedBall_of_dist_eq (Φ : PartialEquiv E X)
    {a : E} {q : X} {r : ℝ} (htarget : ball q r ⊆ Φ.target)
    (hradial : ∀ x ∈ Φ.source, dist (Φ x) q = dist x a) :
    ball q r ⊆ Φ '' closedBall a r := by
  intro y hy
  have hyt := htarget hy
  refine ⟨Φ.symm y, ?_, Φ.right_inv hyt⟩
  rw [Metric.mem_closedBall, ← hradial _ (Φ.map_target hyt), Φ.right_inv hyt]
  exact (Metric.mem_ball.mp hy).le

end PartialEquiv
