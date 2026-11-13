/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.Boundary.EmbeddedDomain
public import TauCeti.Topology.JordanCurve.Basic
public import TauCeti.Analysis.Complex.PlaneSeparation.Inside
/-!
# The actual Jordan frontier and filled region of an embedded disk

A homeomorphism from an embedded surface domain to a closed complex disk constructs a genuine
homeomorphism from its ambient frontier to the circle. Native invariance of domain identifies
the frontier points, and compactness makes the original domain closed. No boundary
parametrization, Jordan certificate, or smooth disk identification is assumed.

For a planar embedded disk, its actual frontier fills precisely that disk. The actual interior
is the bounded inside, and the point mapped to the origin lies there. These identify the region
and center used by local Jordan degree computations in a surface chart.
-/

public section
noncomputable section
open Set Metric TauCeti
open scoped Manifold
namespace Homeomorph
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] {D : Set M}
include I in
/-- The ambient frontier of an actual embedded topological disk in a boundaryless surface
is a genuine Jordan curve, without a supplied boundary parametrization. -/
theorem isJordanCurve_frontier_of_closed_disk
    (e : D ≃ₜ closedBall (0 : ℂ) 1) (hdim : Module.finrank ℝ E = 2) :
    IsJordanCurve (frontier D) := by
  let : CompactSpace D := e.symm.compactSpace
  have hD : IsClosed D := (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  let f : frontier D → Circle := fun x =>
    ⟨(e ⟨x.val, hD.frontier_subset x.property⟩).val, by
      exact mem_sphere_zero_iff_norm.mpr
        ((e.norm_apply_eq_one_iff_mem_frontier_closed_disk I hdim _).mpr x.property)⟩
  let g : Circle → frontier D := fun z =>
    ⟨(e.symm ⟨z.val, mem_closedBall_zero_iff.mpr z.norm_coe.le⟩).val, by
      apply (e.norm_apply_eq_one_iff_mem_frontier_closed_disk I hdim _).mp
      simpa only [Homeomorph.apply_symm_apply] using z.norm_coe⟩
  apply isJordanCurve_iff.mpr
  refine ⟨{
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }⟩
  · intro x
    apply Subtype.ext
    exact congrArg (Subtype.val : D → M) (e.symm_apply_apply ⟨x.val, hD.frontier_subset x.property⟩)
  · intro z
    apply Subtype.ext
    exact congrArg (Subtype.val : closedBall (0 : ℂ) 1 → ℂ)
      (e.apply_symm_apply ⟨z.val, mem_closedBall_zero_iff.mpr z.norm_coe.le⟩)
  · exact ((continuous_subtype_val.comp e.continuous).comp
      (continuous_subtype_val.subtype_mk (fun x => hD.frontier_subset x.property))).subtype_mk _
  · exact ((continuous_subtype_val.comp e.symm.continuous).comp
      (continuous_subtype_val.subtype_mk
        (fun z : Circle => mem_closedBall_zero_iff.mpr z.norm_coe.le))).subtype_mk _
end Homeomorph
namespace Homeomorph
/-- An actual embedded planar topological disk is the filled hull of its actual frontier. -/
theorem filledHull_frontier_eq_of_closed_disk
    {D : Set ℂ} (e : D ≃ₜ closedBall (0 : ℂ) 1) : filledHull (frontier D) = D := by
  let : CompactSpace D := e.symm.compactSpace
  have hD : IsCompact D := isCompact_iff_compactSpace.mpr inferInstance
  let p := e.symm ⟨0, mem_closedBall_self zero_le_one⟩
  have hp : p.val ∈ interior D :=
    (e.norm_apply_lt_one_iff_mem_interior_closed_disk 𝓘(ℝ, ℂ) (by simp) p).mp (by
      simp [p])
  exact (e.isJordanCurve_frontier_of_closed_disk 𝓘(ℝ, ℂ) (by simp)).filledHull_frontier_eq
    hD ⟨p.val, hp⟩
/-- The actual interior of an embedded planar topological disk is the bounded inside of its
actual Jordan frontier. -/
theorem interior_eq_filledHull_sdiff_frontier_of_closed_disk
    {D : Set ℂ} (e : D ≃ₜ closedBall (0 : ℂ) 1) :
    interior D = filledHull (frontier D) \ frontier D := by
  rw [e.filledHull_frontier_eq_of_closed_disk, self_sdiff_frontier]
/-- The center selected by a mere disk homeomorphism belongs to the bounded inside of the
actual planar Jordan frontier. -/
theorem center_mem_filledHull_sdiff_frontier_of_closed_disk
    {D : Set ℂ} (e : D ≃ₜ closedBall (0 : ℂ) 1) :
    (e.symm ⟨0, mem_closedBall_self zero_le_one⟩).val ∈ filledHull (frontier D) \ frontier D := by
  rw [← e.interior_eq_filledHull_sdiff_frontier_of_closed_disk]
  apply (e.norm_apply_lt_one_iff_mem_interior_closed_disk 𝓘(ℝ, ℂ) (by simp) _).mp
  simp
end Homeomorph
