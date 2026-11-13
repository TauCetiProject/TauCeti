/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Algebra.Support

/-!
# Closed balls and annuli in pseudo-metric spaces

Every neighbourhood of a point contains a closed ball about it of arbitrarily small positive
radius (`TauCeti.exists_pos_lt_closedBall_subset`).

The frontier of the closed annulus `closedBall y R \ ball y r` lies on its two boundary spheres
(`TauCeti.frontier_closedBall_sdiff_ball_subset`). A point outside a closed ball containing the
support of a function lies outside its closed support
(`TauCeti.notMem_tsupport_of_support_subset_closedBall`).
-/

public section

namespace TauCeti

open Metric Set Topology

variable {X : Type*} [PseudoMetricSpace X]

/-- Every neighbourhood of `x` contains a closed ball about `x` of positive radius less than any
given `ε > 0`. -/
theorem exists_pos_lt_closedBall_subset {U : Set X} {x : X} (hU : U ∈ 𝓝 x) {ε : ℝ}
    (hε : 0 < ε) : ∃ r, 0 < r ∧ r < ε ∧ closedBall x r ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact ⟨min δ (ε / 2), lt_min hδ (half_pos hε), (min_le_right _ _).trans_lt (half_lt_self hε),
    (closedBall_subset_closedBall (min_le_left _ _)).trans hδU⟩

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
