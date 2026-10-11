/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Realization
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Ball

/-!
# Interior vertex charts from combinatorial links

A vertex whose link is a combinatorial `n`-sphere has an open star homeomorphic to an
open Euclidean `(n + 1)`-ball. This gives a topological chart containing the vertex,
without assuming a finite triangulation: the spherical link itself has finitely many faces,
which makes the closed star compact.

The sphere identification comes from intrinsic stellar equivalence. The radial star
homeomorphism of `Star.Ball` then extends it across the apex. Piecewise-linear compatibility
of these charts is a separate property.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 2–3 (vertex stars and combinatorial manifolds).
-/

public section

open AbstractSimplicialComplex Metric

namespace PreAbstractSimplicialComplex

/-- A combinatorial sphere link supplies an open ball chart whose radius is one minus the
apex coordinate, so the vertex maps to the origin. The ambient complex and vertex type may
be infinite; the one-dimensional chart has a two-point link. -/
theorem IsCombinatorialSphere.exists_homeomorph_openStar_ball
    {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι} {n : ℕ}
    (h : IsCombinatorialSphere (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ e : openStarRealization K v ≃ₜ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      ∀ x, ‖(e x).1‖ = 1 - x.1.1 v := by
  obtain ⟨e⟩ := h.nonempty_homeomorph_sphere link_le
  let r := Homeomorph.setCongr (Set.ext (mem_geometricLink_iff K v))
  have hc := K.isCompact_closedStarRealization (finite_faces_closedStar_iff.mpr h.finite_faces)
  refine ⟨openStarHomeomorphBall hc (r.trans e), fun x => ?_⟩
  rw [openStarHomeomorphBall_apply, norm_closedStarHomeomorphClosedBall]

end PreAbstractSimplicialComplex
