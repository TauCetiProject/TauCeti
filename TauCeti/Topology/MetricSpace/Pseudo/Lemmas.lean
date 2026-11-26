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

Open balls in locally compact pseudometric spaces are locally compact. Every neighbourhood of a
point contains a closed ball about it of arbitrarily small positive radius
(`TauCeti.exists_pos_lt_closedBall_subset`).

The frontier of the closed annulus `closedBall y R \ ball y r` lies on its two boundary spheres
(`TauCeti.frontier_closedBall_sdiff_ball_subset`). A point outside a closed ball containing the
support of a function lies outside its closed support
(`TauCeti.notMem_tsupport_of_support_subset_closedBall`).

Of pairwise disjoint balls, a point of one of them lying in the union of their shrunk concentric
balls lies in its own shrunk ball (`Metric.mem_ball_mul_of_mem_iUnion`).
-/

public section

namespace TauCeti

open Metric Set Topology

variable {X : Type*} [PseudoMetricSpace X]

/-- Open balls in a locally compact pseudometric space are locally compact. -/
instance instLocallyCompactSpaceBall [LocallyCompactSpace X] (c : X) (r : ℝ) :
    LocallyCompactSpace (Metric.ball c r) := Metric.isOpen_ball.locallyCompactSpace

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

/-- Of pairwise disjoint balls `B(cᵢ, rᵢ)`, a point of `B(cᵢ, rᵢ)` lying in the union of the
smaller concentric balls `B(cⱼ, rⱼ tⱼ)`, `tⱼ ≤ 1`, lies in `B(cᵢ, rᵢ tᵢ)`. -/
theorem _root_.Metric.mem_ball_mul_of_mem_iUnion {ι : Type*} {c : ι → X} {r : ι → ℝ}
    (hr : ∀ i, 0 ≤ r i)
    (hdisj : Pairwise fun i j ↦ Disjoint (ball (c i) (r i)) (ball (c j) (r j))) {t : ι → ℝ}
    (ht : ∀ i, t i ≤ 1) {w : X} (hw : w ∈ ⋃ j, ball (c j) (r j * t j)) {i : ι}
    (hwi : w ∈ ball (c i) (r i)) : w ∈ ball (c i) (r i * t i) := by
  obtain ⟨j, hj⟩ := mem_iUnion.1 hw
  obtain rfl | hij := eq_or_ne j i
  · exact hj
  · exact absurd hwi (Set.disjoint_left.1 (hdisj hij)
      (ball_subset_ball (mul_le_of_le_one_right (hr j) (ht j)) hj))

end TauCeti
