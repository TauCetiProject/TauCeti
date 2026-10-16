/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Realization
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.HalfBall
public import TauCeti.Analysis.InnerProductSpace.Hemisphere
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Boundary vertex charts from combinatorial ball links

A vertex whose link is a combinatorial `n`-ball has an open star homeomorphic to
the open unit ball in the standard Euclidean half-space of dimension `n + 1`.
The vertex maps to zero, and the radius is one minus its barycentric coordinate.
Extending the homeomorphism along the open inclusion of the star gives a chart
on the ambient weak realization, with exactly that star as source.

The link ball is identified with a closed hemisphere using
`TauCeti.hemisphereHomeomorph` and Mathlib's
`OrthonormalBasis.fromOrthogonalSpanSingleton` for the equatorial hyperplane.
The existing `AbstractSimplicialComplex.openStarHomeomorphHalfBall` extends this
identification radially across the vertex. Only the link is required to be finite;
the ambient complex and vertex type may be infinite. These are topological charts;
no piecewise-linear compatibility is asserted.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
  Springer (1972), Chapters 2–3 (conical local models and combinatorial manifolds).
-/

public section

open AbstractSimplicialComplex Metric Set Topology
open scoped RealInnerProductSpace

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι} {n : ℕ}

/-- A combinatorial ball link supplies an open half-ball model at the vertex.
The radius is one minus the apex coordinate, including when the link is a zero-ball
and the model is a half-interval. -/
theorem IsCombinatorialBall.exists_homeomorph_openStar_halfBall
    (h : IsCombinatorialBall (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ e : openStarRealization K v ≃ₜ
        {z : EuclideanHalfSpace (n + 1) | ‖z.1‖ < 1},
      ∀ x, ‖(e x).1.1‖ = 1 - x.1.1 v := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let p : sphere (0 : E) 1 := ⟨EuclideanSpace.single 0 1,
    mem_sphere_zero_iff_norm.mpr (by
      simpa only [E, EuclideanSpace.single, norm_one] using
        (PiLp.norm_single 2 (fun _ : Fin (n + 1) => ℝ) 0 1))⟩
  have hp : (p : E) ≠ 0 := ne_zero_of_mem_unit_sphere p
  let : Fact (Module.finrank ℝ E = n + 1) := ⟨by simp [E]⟩
  let b := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n hp).repr.symm
  let d : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
      closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
    b.toHomeomorph.subtype fun x => by simp
  obtain ⟨a⟩ := h.nonempty_homeomorph_closedBall link_le
  let r := Homeomorph.setCongr (Set.ext (mem_geometricLink_iff K v))
  let l := r.trans (a.trans (d.trans (TauCeti.hemisphereHomeomorph p).symm))
  have hc := K.isCompact_closedStarRealization
    (finite_faces_closedStar_iff.mpr h.finite_faces)
  let f := openStarHomeomorphHalfBall hc l
  have hinner (z : E) : ⟪z, (p : E)⟫ = z 0 := by
    simp [p, E, EuclideanSpace.inner_single_right]
  let q : ↥(ball (0 : E) 1 ∩ {z | 0 ≤ ⟪z, (p : E)⟫}) ≃ₜ
      {z : EuclideanHalfSpace (n + 1) | ‖z.1‖ < 1} := {
    toFun z := ⟨⟨z.1, by
      simpa only [Set.mem_ofPred_eq, hinner] using z.2.2⟩,
      mem_ball_zero_iff.mp z.2.1⟩
    invFun z := ⟨z.1.1, mem_ball_zero_iff.mpr z.2, by
      simpa only [Set.mem_ofPred_eq, hinner] using z.1.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hq (z) : (q z).1.1 = (z : E) := rfl
  refine ⟨f.trans q, fun x => ?_⟩
  rw [Homeomorph.trans_apply, hq, coe_openStarHomeomorphHalfBall_apply,
    norm_closedStarHomeomorphHalfBall]

/-- A combinatorial ball link gives a chart on the weak realization with source
the open vertex star and target the open unit half-ball. Its radius records the
apex coordinate, so in particular the vertex is sent to the boundary origin. -/
theorem IsCombinatorialBall.exists_openPartialHomeomorph_openStar_halfBall
    (h : IsCombinatorialBall (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ c : OpenPartialHomeomorph (Realization K) (EuclideanHalfSpace (n + 1)),
      c.source = openStarRealization K v ∧
      c.target = {z | ‖z.1‖ < 1} ∧
      c (vertex K v) = 0 ∧
      ∀ x : openStarRealization K v, ‖(c x.1).1‖ = 1 - x.1.1 v := by
  obtain ⟨e, he⟩ := h.exists_homeomorph_openStar_halfBall
  let U : Set (EuclideanHalfSpace (n + 1)) := {z | ‖z.1‖ < 1}
  have hU : IsOpen U := isOpen_lt continuous_subtype_val.norm continuous_const
  let : Nonempty U := ⟨⟨⟨0, by simp⟩, by simp [U]⟩⟩
  let j : OpenPartialHomeomorph U (EuclideanHalfSpace (n + 1)) :=
    hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  let f := e.toOpenPartialHomeomorph.trans j
  let c := f.lift_openEmbedding (K.isOpen_openStarRealization v).isOpenEmbedding_subtypeVal
  have hradius (x : openStarRealization K v) : ‖(c x.1).1‖ = 1 - x.1.1 v := by
    calc
      ‖(c x.1).1‖ = ‖(f x).1‖ := by
        rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      _ = ‖(e x).1.1‖ := by
        rw [OpenPartialHomeomorph.trans_apply,
          Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply,
          Homeomorph.toOpenPartialHomeomorph_apply]
      _ = 1 - x.1.1 v := he x
  refine ⟨c, ?_, ?_, ?_, hradius⟩
  · simp only [c, f, j, OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_self,
      Set.image_univ, Subtype.range_coe]
  · simp [c, f, j, U]
  · apply Subtype.ext
    apply norm_eq_zero.mp
    simpa using hradius ⟨vertex K v, by simp [mem_openStarRealization]⟩

end PreAbstractSimplicialComplex
