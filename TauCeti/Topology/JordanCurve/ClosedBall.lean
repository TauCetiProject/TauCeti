/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
public import TauCeti.Topology.JordanCurve.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Topology.Homeomorph.SetCongr
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Jordan frontiers of subsets homeomorphic to closed balls

A closed ball has an intrinsic boundary sphere, but identifying this with the ambient
frontier of a homeomorphic subset requires invariance of domain in the same dimension.
In a Hausdorff charted space, the image ball is compact and hence closed, so its ambient
frontier corresponds to the sphere. In dimension two this is a Jordan curve.

The complex closed unit ball is the usual model disk; arbitrary centers, positive radii,
and two-dimensional real normed ball models give the same recognition criterion. These
results identify surface disk boundaries and feed the planar filled-hull recognition in
`TauCeti.Analysis.Complex.PlaneSeparation.Inside`.

## Main results

* `Homeomorph.frontierHomeomorphCircleOfClosedBall`: an explicit frontier-to-circle
  homeomorphism for a complex ball model, with forward and inverse coercion lemmas.
* `Homeomorph.isJordanCurve_frontier_of_closedBall_of_boundaryless`: a closed ball in any
  two-dimensional real normed space gives a Jordan frontier in a boundaryless surface.
* `Homeomorph.isJordanCurve_frontier_of_closedBall`: the planar recognition criterion.

-/

public section

open Set Metric TauCeti
open scoped Manifold

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] {D : Set M}
  {c : ℂ} {r : ℝ}

include I in
/-- The frontier of a subset of a Hausdorff charted space over a two-dimensional real
boundaryless model is homeomorphic to the circle if the subset is homeomorphic to the
closed complex ball of positive radius. -/
noncomputable def frontierHomeomorphCircleOfClosedBall
    (e : D ≃ₜ closedBall c r) (hr : 0 < r) (hdim : Module.finrank ℝ E = 2) :
    frontier D ≃ₜ Circle := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hdim
  have hD : IsClosed D := (isCompact_iff_compactSpace.mpr e.symm.compactSpace).isClosed
  exact (e.frontierOfBoundaryless I 𝓘(ℝ, ℂ) (by simpa using hdim) hD isClosed_closedBall).trans
    ((Homeomorph.setCongr (frontier_closedBall c hr.ne')).trans
      (sphereCircleHomeomorph c hr))

include I in
/-- The frontier-to-circle homeomorphism agrees with the given closed-ball homeomorphism
after normalizing the center and radius. -/
@[simp]
theorem frontierHomeomorphCircleOfClosedBall_apply_coe
    (e : D ≃ₜ closedBall c r) (hr : 0 < r) (hdim : Module.finrank ℝ E = 2) (x : frontier D) :
    (e.frontierHomeomorphCircleOfClosedBall I hr hdim x : ℂ) =
      ((e ⟨x.val, (isCompact_iff_compactSpace.mpr e.symm.compactSpace).isClosed.frontier_subset
        x.property⟩).val - c) / r := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hdim
  simp [frontierHomeomorphCircleOfClosedBall]

include I in
/-- The inverse frontier-to-circle homeomorphism agrees with the inverse closed-ball
homeomorphism after restoring the center and radius. -/
@[simp]
theorem frontierHomeomorphCircleOfClosedBall_symm_apply_coe
    (e : D ≃ₜ closedBall c r) (hr : 0 < r) (hdim : Module.finrank ℝ E = 2) (z : Circle) :
    ((e.frontierHomeomorphCircleOfClosedBall I hr hdim).symm z).val =
      (e.symm ⟨c + r * (z : ℂ), by
        simpa only [coe_sphereCircleHomeomorph_symm_apply] using
          (sphere_subset_closedBall ((sphereCircleHomeomorph c hr).symm z).property)⟩).val := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hdim
  simp [frontierHomeomorphCircleOfClosedBall]

include I in
/-- A subset of a Hausdorff charted space over a two-dimensional real boundaryless model
has a Jordan frontier if it is homeomorphic to a closed ball of positive radius in a
two-dimensional real normed space. -/
theorem isJordanCurve_frontier_of_closedBall_of_boundaryless
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {c : F}
    (e : D ≃ₜ closedBall c r) (hr : 0 < r) (hE : Module.finrank ℝ E = 2)
    (hF : Module.finrank ℝ F = 2) : IsJordanCurve (frontier D) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  obtain ⟨b⟩ := nonempty_homeomorph_closedBall_of_convex (F := ℂ) (convex_closedBall c r)
    (isCompact_closedBall c r)
    ⟨c, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds c hr)⟩ (by simpa using hF)
  exact isJordanCurve_iff.mpr ⟨(e.trans b).frontierHomeomorphCircleOfClosedBall I zero_lt_one hE⟩

/-- The frontier of a planar subset homeomorphic to a closed ball of positive radius in a
two-dimensional real normed space is a Jordan curve. -/
theorem isJordanCurve_frontier_of_closedBall
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {c : F} {D : Set ℂ}
    (e : D ≃ₜ closedBall c r) (hr : 0 < r) (hF : Module.finrank ℝ F = 2) :
    IsJordanCurve (frontier D) :=
  e.isJordanCurve_frontier_of_closedBall_of_boundaryless 𝓘(ℝ, ℂ) hr (by simp) hF

end Homeomorph
