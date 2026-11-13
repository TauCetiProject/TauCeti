/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
public import TauCeti.Topology.JordanCurve.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Jordan frontiers of subsets homeomorphic to closed balls

A subset of a Hausdorff charted space over a two-dimensional real boundaryless model,
homeomorphic to the closed complex unit ball, has a frontier homeomorphic to `Circle`.
In particular, its frontier is a Jordan curve. The planar recognition theorem requires only
the homeomorphism to the closed unit ball.
-/

public section

open Set Metric TauCeti
open scoped Manifold

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] {D : Set M}

include I in
/-- The frontier of a subset of a Hausdorff charted space over a two-dimensional real
boundaryless model is homeomorphic to the circle if the subset is homeomorphic to the
closed complex unit ball. -/
noncomputable def frontierHomeomorphCircleOfClosedBall
    (e : D ≃ₜ closedBall (0 : ℂ) 1) (hdim : Module.finrank ℝ E = 2) : frontier D ≃ₜ Circle := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hdim
  have hD : IsClosed D := (isCompact_iff_compactSpace.mpr e.symm.compactSpace).isClosed
  exact (e.frontierOfBoundaryless I 𝓘(ℝ, ℂ) (by simpa using hdim) hD isClosed_closedBall).trans
    ((Homeomorph.setCongr (frontier_closedBall (0 : ℂ) one_ne_zero)).trans
      Circle.homeomorphSphere.symm)

include I in
/-- The frontier-to-circle homeomorphism agrees with the given closed-ball homeomorphism
on underlying points. -/
@[simp]
theorem frontierHomeomorphCircleOfClosedBall_apply_coe
    (e : D ≃ₜ closedBall (0 : ℂ) 1) (hdim : Module.finrank ℝ E = 2) (x : frontier D) :
    (e.frontierHomeomorphCircleOfClosedBall I hdim x : ℂ) =
      (e ⟨x.val, (isCompact_iff_compactSpace.mpr e.symm.compactSpace).isClosed.frontier_subset
        x.property⟩).val := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hdim
  simp [frontierHomeomorphCircleOfClosedBall, Homeomorph.setCongr]

include I in
/-- The inverse frontier-to-circle homeomorphism agrees with the inverse closed-ball
homeomorphism on underlying points. -/
@[simp]
theorem frontierHomeomorphCircleOfClosedBall_symm_apply_coe
    (e : D ≃ₜ closedBall (0 : ℂ) 1) (hdim : Module.finrank ℝ E = 2) (z : Circle) :
    ((e.frontierHomeomorphCircleOfClosedBall I hdim).symm z).val =
      (e.symm ⟨(z : ℂ), mem_closedBall_zero_iff.mpr z.norm_coe.le⟩).val := by
  have h := congrArg (fun w : Circle => (w : ℂ))
    ((e.frontierHomeomorphCircleOfClosedBall I hdim).apply_symm_apply z)
  rw [frontierHomeomorphCircleOfClosedBall_apply_coe] at h
  simpa only [symm_apply_apply] using
    congrArg (fun y : closedBall (0 : ℂ) 1 => (e.symm y).val)
      (Subtype.ext h : e ⟨_, _⟩ = ⟨(z : ℂ), _⟩)

include I in
/-- The frontier of a subset of a Hausdorff charted space over a two-dimensional real
boundaryless model is a Jordan curve if the subset is homeomorphic to the closed complex unit
ball. -/
theorem isJordanCurve_frontier_of_closedBall_of_boundaryless
    (e : D ≃ₜ closedBall (0 : ℂ) 1) (hdim : Module.finrank ℝ E = 2) :
    IsJordanCurve (frontier D) :=
  isJordanCurve_iff.mpr ⟨e.frontierHomeomorphCircleOfClosedBall I hdim⟩

/-- The frontier of a planar subset homeomorphic to the closed complex unit ball is a Jordan
curve. -/
theorem isJordanCurve_frontier_of_closedBall {D : Set ℂ} (e : D ≃ₜ closedBall (0 : ℂ) 1) :
    IsJordanCurve (frontier D) :=
  e.isJordanCurve_frontier_of_closedBall_of_boundaryless 𝓘(ℝ, ℂ) (by simp)

end Homeomorph
