/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Uniform approximation by finite partitions of unity

A continuous map `F` from a compact normal space `X` to a real normed space is uniformly
approximated by the finite convex combinations `x ↦ ∑ᶠ k, ρ k x • F k` of its own values at
finitely many points, with weights given by a partition of unity `ρ` indexed by those points.
This reduces statements about the uniform norm on `C(X, E)` to statements about finitely many
values. It is used, for example, to pass from Grothendieck's inequality for matrices to bounded
bilinear forms on spaces of continuous functions.
-/

public section

open Set Metric

namespace ContinuousMap

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [NormalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous map on a compact normal space is uniformly within `ε > 0` of the convex
combinations of its values at the points of a finite set `s`, weighted by a partition of unity
indexed by `s`. -/
theorem exists_partitionOfUnity_dist_finsum_smul_le (F : C(X, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset X) (ρ : PartitionOfUnity s X),
      ∀ x, dist (∑ᶠ k, ρ k x • F k) (F x) ≤ ε := by
  -- Cover `X` by the open sets where `F` is within `ε` of its value at a point.
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun k : X ↦ F ⁻¹' ball (F k) ε)
    (fun k ↦ isOpen_ball.preimage F.continuous)
    (fun x _ ↦ mem_iUnion.2 ⟨x, mem_ball_self hε⟩)
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite isClosed_univ
    (fun k : s ↦ F ⁻¹' ball (F k) ε) (fun k ↦ isOpen_ball.preimage F.continuous)
    (locallyFinite_of_finite _) fun x hx ↦ by
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 (hs hx)
      exact mem_iUnion.2 ⟨⟨k, hk⟩, hxk⟩
  refine ⟨s, ρ, fun x ↦ ?_⟩
  rw [← mem_closedBall]
  refine ρ.finsum_smul_mem_convex (g := fun k _ ↦ F k) (mem_univ x) (fun k hk ↦ ?_)
    (convex_closedBall (F x) ε)
  have hx : x ∈ F ⁻¹' ball (F k) ε := hρ k (subset_closure hk)
  exact mem_closedBall_comm.1 (ball_subset_closedBall hx)

end ContinuousMap
