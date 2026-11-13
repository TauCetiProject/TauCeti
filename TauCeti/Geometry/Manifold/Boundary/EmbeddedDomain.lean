/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
/-!
# Ambient interiors and frontiers of embedded domains

The native invariance-of-domain theorem for homeomorphic subsets extends to arbitrary
boundaryless manifold models by their native model transport. Thus a mere homeomorphism
of an embedded surface domain with a closed complex disk identifies its ambient interior
with the open disk and its ambient frontier with the unit circle. No atlas on the subset,
smooth homeomorphism, or single ambient chart is required.
-/

public section
open Set TauCeti
open scoped Manifold
namespace Homeomorph
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] (J : ModelWithCorners ℝ F G) [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {A : Set M} {B : Set N}
include I J in
/-- A homeomorphism of subsets in equal-dimensional boundaryless manifold models preserves
ambient interior membership. -/
theorem coe_apply_mem_interior_iff_of_boundaryless (e : A ≃ₜ B)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (x : A) :
    (e x).val ∈ interior B ↔ x.val ∈ interior A := by
  let a := BoundarylessModel.homeomorph I M
  let b := BoundarylessModel.homeomorph J N
  let e' := (a.image A).symm.trans (e.trans (b.image B))
  have h := e'.coe_apply_mem_interior_iff (E := E) (F := F) hdim (a.image A x)
  simp only [e', Homeomorph.trans_apply, Homeomorph.symm_apply_apply] at h
  change b (e x).val ∈ interior (b '' B) ↔ a x.val ∈ interior (a '' A) at h
  rw [← a.image_interior, ← b.image_interior] at h
  simpa only [Set.mem_image, b.injective.eq_iff, a.injective.eq_iff, exists_eq_right] using h
include I J in
/-- A homeomorphism of subsets in equal-dimensional boundaryless manifold models preserves
ambient frontier membership. -/
theorem coe_apply_mem_frontier_iff_of_boundaryless (e : A ≃ₜ B)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (x : A) :
    (e x).val ∈ frontier B ↔ x.val ∈ frontier A := by
  simp only [frontier, mem_sdiff, subset_closure (e x).property, subset_closure x.property,
    true_and, e.coe_apply_mem_interior_iff_of_boundaryless I J hdim]
include I in
/-- A topological disk identification maps precisely the ambient interior of the embedded
domain to points with norm strictly less than one. -/
theorem norm_apply_lt_one_iff_mem_interior_closed_disk
    (e : A ≃ₜ Metric.closedBall (0 : ℂ) 1) (hdim : Module.finrank ℝ E = 2) (x : A) :
    ‖(e x).val‖ < 1 ↔ x.val ∈ interior A := by
  have h := e.coe_apply_mem_interior_iff_of_boundaryless I 𝓘(ℝ, ℂ) (by simpa using hdim) x
  simpa only [interior_closedBall (0 : ℂ) one_ne_zero, Metric.mem_ball, dist_zero_right] using h
include I in
/-- A topological disk identification maps precisely the ambient frontier of the embedded
domain to the unit circle. -/
theorem norm_apply_eq_one_iff_mem_frontier_closed_disk
    (e : A ≃ₜ Metric.closedBall (0 : ℂ) 1) (hdim : Module.finrank ℝ E = 2) (x : A) :
    ‖(e x).val‖ = 1 ↔ x.val ∈ frontier A := by
  have h := e.coe_apply_mem_frontier_iff_of_boundaryless I 𝓘(ℝ, ℂ) (by simpa using hdim) x
  simpa only [frontier_closedBall (0 : ℂ) one_ne_zero, Metric.mem_sphere, dist_zero_right] using h
end Homeomorph
