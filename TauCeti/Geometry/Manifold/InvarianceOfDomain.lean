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
# Invariance of interior and frontier in boundaryless manifolds

Let `M` and `N` be topological spaces charted on boundaryless models with corners `I` and `J`,
over finite-dimensional real normed spaces of the same dimension. A homeomorphism `e : A ≃ₜ B`
between subsets `A ⊆ M` and `B ⊆ N` maps the points of `A` lying in the ambient interior of `A`
exactly to the points of `B` lying in the ambient interior of `B`, and likewise for frontiers.

This is invariance of domain (`Homeomorph.coe_apply_mem_interior_iff`, stated for spaces charted
on the model vector spaces themselves), transported along the identity homeomorphisms
`BoundarylessModel.homeomorph I M` and `BoundarylessModel.homeomorph J N` to copies of `M` and
`N` charted on `E` and `F`. No smooth structure is involved.

For a subset `A` of a surface without boundary (charted on a boundaryless two-dimensional
model), identified with the closed unit disc of `ℂ` by a mere homeomorphism `e`, the points of
the ambient interior of `A` are those sent into the open unit disc, and the points of the ambient
frontier of `A` those sent to the unit circle.

## Main results

* `Homeomorph.coe_apply_mem_interior_iff_of_boundaryless` and
  `Homeomorph.coe_apply_mem_frontier_iff_of_boundaryless`: invariance of interior and frontier
  points.
* `Homeomorph.dist_apply_lt_iff_mem_interior` and
  `Homeomorph.dist_apply_eq_iff_mem_frontier`: the case of a closed ball of nonzero radius.
* `Homeomorph.norm_apply_lt_one_iff_mem_interior` and
  `Homeomorph.norm_apply_eq_one_iff_mem_frontier`: the case of a topological closed disk in a
  surface without boundary.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2B.3 (invariance of domain).
-/

public section

open Module Set TauCeti
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
/-- **Invariance of interior points in boundaryless manifolds.** Let `A` and `B` be homeomorphic
subsets of spaces charted on boundaryless models over finite-dimensional real normed spaces of
the same dimension. Then a point of `A` lies in the interior of `A` exactly when its image lies
in the interior of `B`. -/
theorem coe_apply_mem_interior_iff_of_boundaryless (e : A ≃ₜ B) (hEF : finrank ℝ E = finrank ℝ F)
    (x : A) : (e x : N) ∈ interior B ↔ (x : M) ∈ interior A := by
  let a := BoundarylessModel.homeomorph I M
  let b := BoundarylessModel.homeomorph J N
  have h := ((a.image A).symm.trans (e.trans (b.image B))).coe_apply_mem_interior_iff
    (E := E) (F := F) hEF (a.image A x)
  simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply,
    Homeomorph.image_apply_coe] at h
  rwa [← a.image_interior, ← b.image_interior, b.injective.mem_set_image,
    a.injective.mem_set_image] at h

include I J in
/-- **Invariance of frontier points in boundaryless manifolds.** Let `A` and `B` be homeomorphic
subsets of spaces charted on boundaryless models over finite-dimensional real normed spaces of
the same dimension. Then a point of `A` lies in the frontier of `A` exactly when its image lies
in the frontier of `B`. -/
theorem coe_apply_mem_frontier_iff_of_boundaryless (e : A ≃ₜ B) (hEF : finrank ℝ E = finrank ℝ F)
    (x : A) : (e x : N) ∈ frontier B ↔ (x : M) ∈ frontier A := by
  simp only [frontier, mem_sdiff, subset_closure (e x).property, subset_closure x.property,
      true_and,
    e.coe_apply_mem_interior_iff_of_boundaryless I J hEF]

include I in
/-- A subset of a manifold charted on a boundaryless model, homeomorphic to a closed ball
of nonzero radius in a finite-dimensional real normed space of the same dimension, has as
ambient interior points exactly the points sent into the open ball. -/
theorem dist_apply_lt_iff_mem_interior {c : F} {r : ℝ} (e : A ≃ₜ Metric.closedBall c r)
    (hr : r ≠ 0) (hEF : finrank ℝ E = finrank ℝ F) (x : A) :
    dist (e x : F) c < r ↔ (x : M) ∈ interior A := by
  have h := e.coe_apply_mem_interior_iff_of_boundaryless I 𝓘(ℝ, F) hEF x
  rwa [interior_closedBall c hr, Metric.mem_ball] at h

include I in
/-- A subset of a manifold charted on a boundaryless model, homeomorphic to a closed ball
of nonzero radius in a finite-dimensional real normed space of the same dimension, has as
ambient frontier points exactly the points sent to the sphere. -/
theorem dist_apply_eq_iff_mem_frontier {c : F} {r : ℝ} (e : A ≃ₜ Metric.closedBall c r)
    (hr : r ≠ 0) (hEF : finrank ℝ E = finrank ℝ F) (x : A) :
    dist (e x : F) c = r ↔ (x : M) ∈ frontier A := by
  have h := e.coe_apply_mem_frontier_iff_of_boundaryless I 𝓘(ℝ, F) hEF x
  rwa [frontier_closedBall c hr, Metric.mem_sphere] at h

omit [FiniteDimensional ℝ E] in
include I in
/-- A subset `A` of a surface without boundary (charted on a boundaryless two-dimensional
model), identified with the closed unit disc of `ℂ` by a homeomorphism `e`, has as ambient
interior points exactly the points sent into the open unit disc. -/
theorem norm_apply_lt_one_iff_mem_interior (e : A ≃ₜ Metric.closedBall (0 : ℂ) 1)
    (hE : finrank ℝ E = 2) (x : A) : ‖(e x : ℂ)‖ < 1 ↔ (x : M) ∈ interior A := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  simpa only [dist_zero_right] using
    e.dist_apply_lt_iff_mem_interior I one_ne_zero (hE.trans Complex.finrank_real_complex.symm) x

omit [FiniteDimensional ℝ E] in
include I in
/-- A subset `A` of a surface without boundary (charted on a boundaryless two-dimensional
model), identified with the closed unit disc of `ℂ` by a homeomorphism `e`, has as ambient
frontier points exactly the points sent to the unit circle. -/
theorem norm_apply_eq_one_iff_mem_frontier (e : A ≃ₜ Metric.closedBall (0 : ℂ) 1)
    (hE : finrank ℝ E = 2) (x : A) : ‖(e x : ℂ)‖ = 1 ↔ (x : M) ∈ frontier A := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  simpa only [dist_zero_right] using
    e.dist_apply_eq_iff_mem_frontier I one_ne_zero (hE.trans Complex.finrank_real_complex.symm) x

end Homeomorph
