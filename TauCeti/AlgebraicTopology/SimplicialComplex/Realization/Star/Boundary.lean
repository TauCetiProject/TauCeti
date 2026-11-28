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
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

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

noncomputable section

open AbstractSimplicialComplex Metric Set Topology
open scoped RealInnerProductSpace

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι} {n : ℕ}

private def unitAxisZero (n : ℕ) : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨EuclideanSpace.single 0 1, mem_sphere_zero_iff_norm.mpr (by
    simpa only [EuclideanSpace.single, norm_one] using
      (PiLp.norm_single 2 (fun _ : Fin (n + 1) => ℝ) 0 1))⟩

private def linkBallToOrthogonalBall (n : ℕ) :
    closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
      closedBall (0 : (ℝ ∙ (unitAxisZero n : EuclideanSpace ℝ (Fin (n + 1))))ᗮ) 1 :=
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let : Fact (Module.finrank ℝ E = n + 1) := ⟨by simp [E]⟩
  let hp : (unitAxisZero n : E) ≠ 0 := ne_zero_of_mem_unit_sphere (unitAxisZero n)
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n hp).repr.symm.toHomeomorph.subtype
    fun x => by simp

private def linkToHemisphere
    (a : {x : Realization K | x.val.support ∈ K.link {v}} ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    geometricLink K v ≃ₜ
      {z : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 //
        0 ≤ ⟪(z : EuclideanSpace ℝ (Fin (n + 1))),
          (unitAxisZero n : EuclideanSpace ℝ (Fin (n + 1)))⟫} :=
  let r := Homeomorph.setCongr (s := K.geometricLink v)
    (t := {x : Realization K | x.val.support ∈ K.link {v}}) (Set.ext (mem_geometricLink_iff K v))
  r.trans (a.trans ((linkBallToOrthogonalBall n).trans
    (TauCeti.hemisphereHomeomorph (unitAxisZero n)).symm))

/-- Given a compact closed star at `v` and a homeomorphism `a` from the geometric link to the closed
unit `n`-ball, build a homeomorphism from `openStarRealization K v` to the open unit half-ball
`{z : EuclideanHalfSpace (n + 1) | ‖z.val‖ < 1}`. -/
def openStarHomeomorphHalfBallOfLink
    (hc : IsCompact (closedStarRealization K {v}))
    (a : {x : Realization K | x.val.support ∈ K.link {v}} ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    openStarRealization K v ≃ₜ {z : EuclideanHalfSpace (n + 1) | ‖z.val‖ < 1} :=
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let f := openStarHomeomorphHalfBall hc (linkToHemisphere a)
  have hinner (z : E) : ⟪z, (unitAxisZero n : E)⟫ = z 0 := by
    simp [unitAxisZero, E, EuclideanSpace.inner_single_right]
  let q : ↥(ball (0 : E) 1 ∩ {z | 0 ≤ ⟪z, (unitAxisZero n : E)⟫}) ≃ₜ
      {z : EuclideanHalfSpace (n + 1) | ‖z.val‖ < 1} := {
    toFun z := ⟨⟨z.val, by
      simpa only [Set.mem_ofPred_eq, hinner] using z.property.2⟩,
      mem_ball_zero_iff.mp z.property.1⟩
    invFun z := ⟨z.val.val, mem_ball_zero_iff.mpr z.property, by
      simpa only [Set.mem_ofPred_eq, hinner] using z.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  f.trans q

/-- The Euclidean norm under `openStarHomeomorphHalfBallOfLink` equals one minus the apex
barycentric coordinate. -/
theorem norm_openStarHomeomorphHalfBallOfLink
    (hc : IsCompact (closedStarRealization K {v}))
    (a : {x : Realization K | x.val.support ∈ K.link {v}} ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (x : openStarRealization K v) :
    ‖(openStarHomeomorphHalfBallOfLink hc a x).val.val‖ = 1 - x.val.val v := by
  have hval : (openStarHomeomorphHalfBallOfLink hc a x).val.val =
      (openStarHomeomorphHalfBall hc (linkToHemisphere a) x : EuclideanSpace ℝ (Fin (n + 1))) :=
    rfl
  rw [hval, coe_openStarHomeomorphHalfBall_apply, norm_closedStarHomeomorphHalfBall]

/-- Away from the vertex `v`, the half-space normal coordinate of
`openStarHomeomorphHalfBallOfLink` is `(1 - x v) * √(1 - ‖a (starLinkProjection x)‖²)`. -/
theorem coe_openStarHomeomorphHalfBallOfLink_apply_zero
    (hc : IsCompact (closedStarRealization K {v}))
    (a : {x : Realization K | x.val.support ∈ K.link {v}} ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (x : openStarRealization K v) (hx : x.val.val v < 1) :
    (openStarHomeomorphHalfBallOfLink hc a x).val.val 0 =
      (1 - x.val.val v) *
        √(1 - ‖(a ⟨(starLinkProjection K v ⟨x.val, (mem_puncturedClosedStar K v _).mpr
          ⟨openStarRealization_subset_closedStarRealization K v x.property, hx⟩⟩).val,
          (mem_geometricLink_iff K v _).mp (starLinkProjection K v _).property⟩ :
            EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let p₀ : puncturedClosedStar K v := ⟨x.val, (mem_puncturedClosedStar K v _).mpr
    ⟨openStarRealization_subset_closedStarRealization K v x.property, hx⟩⟩
  let y : geometricLink K v := starLinkProjection K v p₀
  let r := Homeomorph.setCongr (s := K.geometricLink v)
    (t := {x : Realization K | x.val.support ∈ K.link {v}}) (Set.ext (mem_geometricLink_iff K v))
  have hinner (z : E) : z 0 = ⟪z, (unitAxisZero n : E)⟫ := by
    simp [unitAxisZero, E, EuclideanSpace.inner_single_right]
  have hval : (openStarHomeomorphHalfBallOfLink hc a x).val.val =
      (openStarHomeomorphHalfBall hc (linkToHemisphere a) x : E) := rfl
  rw [hval, hinner, coe_openStarHomeomorphHalfBall_apply,
    coe_closedStarHomeomorphHalfBall_of_lt hc (linkToHemisphere a) _ hx, real_inner_smul_left]
  have hl : ((linkToHemisphere a y : sphere (0 : E) 1) : E) =
      ((linkBallToOrthogonalBall n (a (r y)) : (ℝ ∙ (unitAxisZero n : E))ᗮ) : E) +
        √(1 - ‖(linkBallToOrthogonalBall n (a (r y)) : (ℝ ∙ (unitAxisZero n : E))ᗮ)‖ ^ 2) •
          (unitAxisZero n : E) :=
    TauCeti.coe_hemisphereHomeomorph_symm_apply (unitAxisZero n)
      (linkBallToOrthogonalBall n (a (r y)))
  have horth : ⟪((linkBallToOrthogonalBall n (a (r y)) : (ℝ ∙ (unitAxisZero n : E))ᗮ) : E),
      (unitAxisZero n : E)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp
      (linkBallToOrthogonalBall n (a (r y))).val.property
  have hpp : ⟪(unitAxisZero n : E), (unitAxisZero n : E)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere (unitAxisZero n), one_pow]
  have hnorm : ‖(linkBallToOrthogonalBall n (a (r y)) : (ℝ ∙ (unitAxisZero n : E))ᗮ)‖ =
      ‖(a (r y) : EuclideanSpace ℝ (Fin n))‖ := by
    simp [linkBallToOrthogonalBall]
  change (1 - x.val.val v) *
      ⟪((linkToHemisphere a y : sphere (0 : E) 1) : E), (unitAxisZero n : E)⟫ = _
  rw [hl, inner_add_left, real_inner_smul_left, horth, hpp, zero_add, mul_one, hnorm]
  rfl

/-- Away from the vertex `v`, `openStarHomeomorphHalfBallOfLink` hits the boundary hyperplane
`z 0 = 0` iff the link projection maps to the boundary sphere `‖a (starLinkProjection x)‖ = 1`. -/
theorem openStarHomeomorphHalfBallOfLink_apply_zero_eq_zero_iff
    (hc : IsCompact (closedStarRealization K {v}))
    (a : {x : Realization K | x.val.support ∈ K.link {v}} ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (x : openStarRealization K v) (hx : x.val.val v < 1) :
    (openStarHomeomorphHalfBallOfLink hc a x).val.val 0 = 0 ↔
      ‖(a ⟨(starLinkProjection K v ⟨x.val, (mem_puncturedClosedStar K v _).mpr
        ⟨openStarRealization_subset_closedStarRealization K v x.property, hx⟩⟩).val,
        (mem_geometricLink_iff K v _).mp (starLinkProjection K v _).property⟩ :
          EuclideanSpace ℝ (Fin n))‖ = 1 := by
  rw [coe_openStarHomeomorphHalfBallOfLink_apply_zero hc a x hx, mul_eq_zero]
  have hpos : 0 < 1 - x.val.val v := sub_pos.mpr hx
  let u := (a ⟨(starLinkProjection K v ⟨x.val, (mem_puncturedClosedStar K v _).mpr
    ⟨openStarRealization_subset_closedStarRealization K v x.property, hx⟩⟩).val,
    (mem_geometricLink_iff K v _).mp (starLinkProjection K v _).property⟩)
  have hle : ‖(u : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := mem_closedBall_zero_iff.mp u.property
  have hnonneg : 0 ≤ 1 - ‖(u : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
    nlinarith [norm_nonneg (u : EuclideanSpace ℝ (Fin n))]
  change (1 - x.val.val v = 0 ∨ √(1 - ‖(u : EuclideanSpace ℝ (Fin n))‖ ^ 2) = 0) ↔
    ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1
  rw [or_iff_right hpos.ne', Real.sqrt_eq_zero hnonneg, sub_eq_zero, eq_comm,
    pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]

/-- Given a compact closed star at `v` and a link-to-ball homeomorphism `a`, build a half-space
chart on `Realization K` whose source is `openStarRealization K v`, agreeing there with
`openStarHomeomorphHalfBallOfLink`. -/
theorem exists_openPartialHomeomorph_openStar_halfBall_of_link
    (hc : IsCompact (closedStarRealization K {v}))
    (a : {x : Realization K | x.val.support ∈ K.link {v}} ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∃ c : OpenPartialHomeomorph (Realization K) (EuclideanHalfSpace (n + 1)),
      c.source = openStarRealization K v ∧
      c.target = {z | ‖z.val‖ < 1} ∧
      c (vertex K v) = 0 ∧
      (∀ x : openStarRealization K v, ‖(c x.val).val‖ = 1 - x.val.val v) ∧
      (∀ x : openStarRealization K v, c x.val = openStarHomeomorphHalfBallOfLink hc a x) := by
  have hU : IsOpen {z : EuclideanHalfSpace (n + 1) | ‖z.val‖ < 1} :=
    isOpen_lt continuous_subtypeVal.norm continuous_const
  obtain ⟨c, hs, ht, hc_apply⟩ := OpenPartialHomeomorph.exists_source_eq_target_eq_of_homeomorph
    (K.isOpen_openStarRealization v) hU (openStarHomeomorphHalfBallOfLink hc a)
    ⟨vertex K v, by simp [mem_openStarRealization]⟩
  have hradius (x : openStarRealization K v) : ‖(c x.val).val‖ = 1 - x.val.val v := by
    rw [hc_apply x]
    exact norm_openStarHomeomorphHalfBallOfLink hc a x
  refine ⟨c, hs, ht, ?_, hradius, hc_apply⟩
  · apply Subtype.ext
    apply norm_eq_zero.mp
    simpa using hradius ⟨vertex K v, by simp [mem_openStarRealization]⟩

/-- A combinatorial ball link supplies an open half-ball model at the vertex.
The radius is one minus the apex coordinate, including when the link is a zero-ball
and the model is a half-interval. -/
theorem IsCombinatorialBall.exists_homeomorph_openStar_halfBall
    (h : IsCombinatorialBall (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ e : openStarRealization K v ≃ₜ
        {z : EuclideanHalfSpace (n + 1) | ‖z.val‖ < 1},
      ∀ x, ‖(e x).val.val‖ = 1 - x.val.val v := by
  obtain ⟨a⟩ := h.nonempty_homeomorph_closedBall link_le
  have hc := K.isCompact_closedStarRealization
    (finite_faces_closedStar_iff.mpr h.finite_faces)
  exact ⟨openStarHomeomorphHalfBallOfLink hc a, norm_openStarHomeomorphHalfBallOfLink hc a⟩

/-- A combinatorial ball link gives a chart on the weak realization with source
the open vertex star and target the open unit half-ball. Its radius records the
apex coordinate, so in particular the vertex is sent to the boundary origin. -/
theorem IsCombinatorialBall.exists_openPartialHomeomorph_openStar_halfBall
    (h : IsCombinatorialBall (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ c : OpenPartialHomeomorph (Realization K) (EuclideanHalfSpace (n + 1)),
      c.source = openStarRealization K v ∧
      c.target = {z | ‖z.val‖ < 1} ∧
      c (vertex K v) = 0 ∧
      ∀ x : openStarRealization K v, ‖(c x.val).val‖ = 1 - x.val.val v := by
  obtain ⟨a⟩ := h.nonempty_homeomorph_closedBall link_le
  have hc := K.isCompact_closedStarRealization
    (finite_faces_closedStar_iff.mpr h.finite_faces)
  obtain ⟨c, hs, ht, hcv, hrad, -⟩ :=
    exists_openPartialHomeomorph_openStar_halfBall_of_link hc a
  exact ⟨c, hs, ht, hcv, hrad⟩

end PreAbstractSimplicialComplex
