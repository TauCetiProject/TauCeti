/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Realization
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Ball.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Interior vertex charts from combinatorial links

A vertex whose link is a combinatorial `n`-sphere has an open star homeomorphic to an
open Euclidean `(n + 1)`-ball. This gives a topological chart containing the vertex,
without assuming a finite triangulation: the spherical link itself has finitely many faces,
which makes the closed star compact. Composing with the inclusion of the ball, the same
identification is an open partial homeomorphism from the realization to Euclidean space.

The sphere identification comes from intrinsic stellar equivalence. The radial star
homeomorphism of `Star.Ball.Basic` then extends it across the apex. Piecewise-linear compatibility
of these charts is a separate property.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 2–3 (vertex stars and combinatorial manifolds).
-/

public section

open AbstractSimplicialComplex Metric Set Topology

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
  let r := Homeomorph.setCongr (s := K.geometricLink v)
    (t := {x : Realization K | x.1.support ∈ K.link {v}}) (Set.ext (mem_geometricLink_iff K v))
  have hc := K.isCompact_closedStarRealization (finite_faces_closedStar_iff.mpr h.finite_faces)
  refine ⟨openStarHomeomorphBall hc (r.trans e), fun x => ?_⟩
  rw [openStarHomeomorphBall_apply, norm_closedStarHomeomorphClosedBall]

/-- A combinatorial-sphere link gives a chart on the weak realization, with values in Euclidean
space, whose source is the open vertex star and whose target is the open unit ball. Its radius
records the apex coordinate, so in particular the vertex is sent to the origin. -/
theorem IsCombinatorialSphere.exists_openPartialHomeomorph_openStar_ball
    {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι} {n : ℕ}
    (h : IsCombinatorialSphere (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ c : OpenPartialHomeomorph (Realization K) (EuclideanSpace ℝ (Fin (n + 1))),
      c.source = openStarRealization K v ∧
      c.target = ball 0 1 ∧
      c (vertex K v) = 0 ∧
      ∀ x : openStarRealization K v, ‖c x.1‖ = 1 - x.1.1 v := by
  obtain ⟨e, he⟩ := h.exists_homeomorph_openStar_ball
  let U : Set (EuclideanSpace ℝ (Fin (n + 1))) := ball 0 1
  have hU : IsOpen U := isOpen_ball
  let : Nonempty U := ⟨⟨0, by simp [U]⟩⟩
  let j : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin (n + 1))) :=
    hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  let f := e.toOpenPartialHomeomorph.trans j
  let c := f.lift_openEmbedding (K.isOpen_openStarRealization v).isOpenEmbedding_subtypeVal
  have hradius (x : openStarRealization K v) : ‖c x.1‖ = 1 - x.1.1 v := by
    calc
      ‖c x.1‖ = ‖f x‖ := by
        rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      _ = ‖(e x).1‖ := by
        rw [OpenPartialHomeomorph.trans_apply,
          Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply,
          Homeomorph.toOpenPartialHomeomorph_apply]
      _ = 1 - x.1.1 v := he x
  refine ⟨c, ?_, ?_, ?_, hradius⟩
  · simp only [c, f, j, OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_self,
      Set.image_univ, Subtype.range_coe]
  · ext
    simp [c, f, j, U]
  · apply norm_eq_zero.mp
    simpa using hradius ⟨vertex K v, by simp [mem_openStarRealization]⟩

end PreAbstractSimplicialComplex
