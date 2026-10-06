/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.LocalInvariantManifold
public import TauCeti.Analysis.Calculus.ProjectionGraph

/-!
# Ambient charts for local Morse stable and unstable disks

The local stable and unstable sets of a negative-gradient equation are `C¹` graphs over the
positive and negative spectral subspaces of the Hessian. An explicit triangular change of
ambient coordinates straightens each graph to its spectral subspace. The charts fix the
critical displacement `0` and have identity derivative there, expressing tangency without a
choice of basis.

The source and target are open cylinders over the parameter disk. The projection cutoff is
strict inside these cylinders, so the statements describe the interiors of the local disks,
not their boundaries. These are embedded local submanifold normal forms; no embeddedness of
the entire global stable or unstable set is asserted. Displacements are centered at the
critical point, as in `IsNondegenerateCriticalPoint.localStableSet`.

## Main results

* `IsNondegenerateCriticalPoint.exists_localStableSet_chart`: a `C¹` ambient chart whose
  stable-set slice is exactly the stable Hessian subspace.
* `IsNondegenerateCriticalPoint.exists_localUnstableSet_chart`: the backward-time counterpart.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Metric Set Topology

namespace TauCeti
namespace IsNondegenerateCriticalPoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}

/-- The interior of a local stable disk admits a `C¹` ambient straightening chart. The chart
and its inverse are defined on the open cylinder over a positive-radius disk in the stable
spectral subspace; the chart fixes zero and has identity derivative there. -/
theorem exists_localStableSet_chart (h : IsNondegenerateCriticalPoint f x) :
    ∃ r > 0, ∃ ρ > 0, ∃ q : OpenPartialHomeomorph E E,
      q.source = h.stableProjection ⁻¹' ball 0 ρ ∧
      q.target = h.stableProjection ⁻¹' ball 0 ρ ∧
      q 0 = 0 ∧ HasFDerivAt q (ContinuousLinearMap.id ℝ E) 0 ∧
      (∀ z ∈ q.source, ContDiffAt ℝ 1 q z) ∧
      (∀ z ∈ q.target, ContDiffAt ℝ 1 q.symm z) ∧
      (∀ z ∈ q.source, z ∈ h.localStableSet r ρ ↔
        q z ∈ h.contDiffAt.stableLinearSubspace) := by
  obtain ⟨r, hr, ρ, hρ, g, hg, hg0, hgd, hgs, hPg, _, hset, _⟩ :=
    h.exists_localStableSet_eq_lipschitzGraph 1 one_pos
  let q := h.stableProjection.projectionGraphChart g (U := ball 0 ρ)
    isOpen_ball hg.continuous.continuousOn
    (fun v _ ↦ hPg v)
  have hsource : q.source = h.stableProjection ⁻¹' ball 0 ρ :=
    ContinuousLinearMap.projectionGraphChart_source ..
  have htarget : q.target = h.stableProjection ⁻¹' ball 0 ρ :=
    ContinuousLinearMap.projectionGraphChart_target ..
  have hformula (z : E) : q z = z - g (h.stableProjection z) :=
    ContinuousLinearMap.projectionGraphChart_apply ..
  refine ⟨r, hr, ρ, hρ, q, hsource, htarget, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hformula, hg0]
  · have hd := h.stableProjection.hasFDerivAt_projectionGraphChart g (U := ball 0 ρ)
      isOpen_ball hg.continuous.continuousOn (fun v _ ↦ hPg v)
      (z := 0) (D := 0) (by simpa using hgd)
    simpa using hd
  · intro z hz
    rw [hsource] at hz
    exact h.stableProjection.contDiffAt_projectionGraphChart g isOpen_ball
      hg.continuous.continuousOn (fun v _ ↦ hPg v) (hgs _ (ball_subset_closedBall hz))
  · intro z hz
    rw [htarget] at hz
    exact h.stableProjection.contDiffAt_projectionGraphChart_symm g isOpen_ball
      hg.continuous.continuousOn (fun v _ ↦ hPg v) (hgs _ (ball_subset_closedBall hz))
  · intro z hz
    rw [hsource] at hz
    rw [hset, ← h.range_stableProjection]
    exact (h.stableProjection.projectionGraphChart_mem_range_iff g isOpen_ball
      hg.continuous.continuousOn (fun v _ ↦ hPg v) h.isIdempotentElem_stableProjection
      ball_subset_closedBall (fun v _ ↦ hPg v) hz).symm

/-- The interior of a local unstable disk admits a `C¹` ambient straightening chart onto the
unstable Hessian subspace, fixing zero with identity derivative. Its parameter dimension is
the Morse index. -/
theorem exists_localUnstableSet_chart (h : IsNondegenerateCriticalPoint f x) :
    ∃ r > 0, ∃ ρ > 0, ∃ q : OpenPartialHomeomorph E E,
      q.source = h.unstableProjection ⁻¹' ball 0 ρ ∧
      q.target = h.unstableProjection ⁻¹' ball 0 ρ ∧
      q 0 = 0 ∧ HasFDerivAt q (ContinuousLinearMap.id ℝ E) 0 ∧
      (∀ z ∈ q.source, ContDiffAt ℝ 1 q z) ∧
      (∀ z ∈ q.target, ContDiffAt ℝ 1 q.symm z) ∧
      (∀ z ∈ q.source, z ∈ h.localUnstableSet r ρ ↔
        q z ∈ h.contDiffAt.unstableLinearSubspace) := by
  obtain ⟨r, hr, ρ, hρ, g, hg, hg0, hgd, hgs, hPg, _, hset, _⟩ :=
    h.exists_localUnstableSet_eq_lipschitzGraph 1 one_pos
  let q := h.unstableProjection.projectionGraphChart g (U := ball 0 ρ)
    isOpen_ball hg.continuous.continuousOn
    (fun v _ ↦ hPg v)
  have hsource : q.source = h.unstableProjection ⁻¹' ball 0 ρ :=
    ContinuousLinearMap.projectionGraphChart_source ..
  have htarget : q.target = h.unstableProjection ⁻¹' ball 0 ρ :=
    ContinuousLinearMap.projectionGraphChart_target ..
  have hformula (z : E) : q z = z - g (h.unstableProjection z) :=
    ContinuousLinearMap.projectionGraphChart_apply ..
  refine ⟨r, hr, ρ, hρ, q, hsource, htarget, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hformula, hg0]
  · have hd := h.unstableProjection.hasFDerivAt_projectionGraphChart g (U := ball 0 ρ)
      isOpen_ball hg.continuous.continuousOn (fun v _ ↦ hPg v)
      (z := 0) (D := 0) (by simpa using hgd)
    simpa using hd
  · intro z hz
    rw [hsource] at hz
    exact h.unstableProjection.contDiffAt_projectionGraphChart g isOpen_ball
      hg.continuous.continuousOn (fun v _ ↦ hPg v) (hgs _ (ball_subset_closedBall hz))
  · intro z hz
    rw [htarget] at hz
    exact h.unstableProjection.contDiffAt_projectionGraphChart_symm g isOpen_ball
      hg.continuous.continuousOn (fun v _ ↦ hPg v) (hgs _ (ball_subset_closedBall hz))
  · intro z hz
    rw [hsource] at hz
    rw [hset, ← h.range_unstableProjection]
    exact (h.unstableProjection.projectionGraphChart_mem_range_iff g isOpen_ball
      hg.continuous.continuousOn (fun v _ ↦ hPg v) h.isIdempotentElem_unstableProjection
      ball_subset_closedBall (fun v _ ↦ hPg v) hz).symm

end IsNondegenerateCriticalPoint
end TauCeti
