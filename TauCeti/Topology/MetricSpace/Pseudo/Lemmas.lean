/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Algebra.Support

/-!
# Balls and annuli in pseudo-metric spaces

Open balls in locally compact pseudometric spaces are locally compact. The frontier of the closed
annulus `closedBall y R \ ball y r` lies on its two boundary spheres
(`TauCeti.frontier_closedBall_sdiff_ball_subset`). A point outside a closed ball containing the
support of a function lies outside its closed support
(`TauCeti.notMem_tsupport_of_support_subset_closedBall`).
-/

public section

namespace TauCeti

open Metric Set

variable {X : Type*} [PseudoMetricSpace X]

/-- Open balls in a locally compact pseudometric space are locally compact. -/
instance instLocallyCompactSpaceBall [LocallyCompactSpace X] (c : X) (r : ℝ) :
    LocallyCompactSpace (Metric.ball c r) := Metric.isOpen_ball.locallyCompactSpace

/-- The frontier of the closed annulus `closedBall y R \ ball y r` lies on its two boundary
spheres. -/
theorem frontier_closedBall_sdiff_ball_subset (y : X) (r R : ℝ) :
    frontier (closedBall y R \ ball y r) ⊆ sphere y R ∪ sphere y r := by
  rw [sdiff_eq]
  refine (frontier_inter_subset _ _).trans (union_subset_union ?_ ?_)
  · exact inter_subset_left.trans frontier_closedBall_subset_sphere
  · rw [frontier_compl]
    exact inter_subset_right.trans frontier_ball_subset_sphere

/-- A point outside a closed ball containing the support of `f` lies outside its closed
support. -/
theorem notMem_tsupport_of_support_subset_closedBall {β : Type*} [Zero β] {f : X → β} {c w : X}
    {r : ℝ} (hsupp : Function.support f ⊆ closedBall c r) (hw : r < dist w c) :
    w ∉ tsupport f := fun h ↦
  (mem_closedBall.mp (closure_minimal hsupp isClosed_closedBall h)).not_gt hw

end TauCeti
