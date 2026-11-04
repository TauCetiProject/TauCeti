/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Boundary spheres of a closed ball with round holes

Let the closed balls `closedBall (c i) (ρ i)` lie in the open ball `ball z₀ r` and be pairwise
disjoint. Removing the open balls `ball (c i) (ρ i)` from `closedBall z₀ r` leaves a closed ball
with round holes, the shape of a truncated punctured sphere. Its outer boundary sphere
`sphere z₀ r` (`TauCeti.sphere_subset_closedBall_diff_iUnion_ball`) and each hole's boundary sphere
`sphere (c i) (ρ i)` (`TauCeti.sphere_subset_closedBall_diff_iUnion_ball_of_disjoint`) lie in the
region. These are the boundary circles along which Stokes' formula on a disc with holes is
evaluated.
-/

public section

open Set Metric

namespace TauCeti

variable {X ι : Type*} [PseudoMetricSpace X] {z₀ : X} {r : ℝ} {c : ι → X} {ρ : ι → ℝ}

/-- If every closed ball `closedBall (c i) (ρ i)` lies in `ball z₀ r`, the outer sphere
`sphere z₀ r` lies in the closed ball with holes `closedBall z₀ r \ ⋃ i, ball (c i) (ρ i)`. -/
theorem sphere_subset_closedBall_diff_iUnion_ball
    (hsub : ∀ i, closedBall (c i) (ρ i) ⊆ ball z₀ r) :
    sphere z₀ r ⊆ closedBall z₀ r \ ⋃ i, ball (c i) (ρ i) := by
  intro z hz
  refine ⟨sphere_subset_closedBall hz, ?_⟩
  simp only [mem_iUnion, not_exists]
  intro j hj
  have h := hsub j (ball_subset_closedBall hj)
  rw [mem_ball, mem_sphere.1 hz] at h
  exact lt_irrefl _ h

/-- If the closed balls `closedBall (c i) (ρ i)` lie in `ball z₀ r` and are pairwise disjoint, the
boundary sphere `sphere (c i) (ρ i)` of each hole lies in the closed ball with holes
`closedBall z₀ r \ ⋃ j, ball (c j) (ρ j)`. -/
theorem sphere_subset_closedBall_diff_iUnion_ball_of_disjoint
    (hsub : ∀ i, closedBall (c i) (ρ i) ⊆ ball z₀ r)
    (hdisj : Pairwise fun i j ↦ Disjoint (closedBall (c i) (ρ i)) (closedBall (c j) (ρ j)))
    (i : ι) :
    sphere (c i) (ρ i) ⊆ closedBall z₀ r \ ⋃ j, ball (c j) (ρ j) := by
  intro z hz
  have hzi := sphere_subset_closedBall hz
  refine ⟨ball_subset_closedBall (hsub i hzi), ?_⟩
  simp only [mem_iUnion, not_exists]
  intro j hj
  rcases eq_or_ne i j with rfl | hij
  · rw [mem_ball, mem_sphere.1 hz] at hj
    exact lt_irrefl _ hj
  · exact (hdisj hij).ne_of_mem hzi (ball_subset_closedBall hj) rfl

end TauCeti
