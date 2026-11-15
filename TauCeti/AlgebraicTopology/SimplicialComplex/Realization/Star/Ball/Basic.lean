/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
public import Mathlib.Analysis.Normed.Module.Normalize
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite

/-!
# Ball models for vertex stars with spherical links

A homeomorphism from a vertex link to a unit sphere extends radially across the apex to
identify its closed star with the closed unit ball. The apex coordinate becomes one minus
the norm. Thus the same homeomorphism identifies the open star with the open ball and the
link with the sphere. These are the local topological models at interior vertices of a
triangulated manifold.

Only the closed star needs to be compact, as it is when it has finitely many faces; the
ambient complex and its vertex type may be infinite. No PL regularity of the link
homeomorphism or the radial extension is asserted. The construction also covers an empty
link and a zero-dimensional model space.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapter 2, “Pseudo-Radial Projection”, pp. 20–21.
-/

public section

noncomputable section

open Set Filter Topology NormedSpace Metric TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {v : ι}

private def starBallMap (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1)
    (x : closedStarRealization K {v}) : E :=
  if h : x.1.1 v < 1 then
    (1 - x.1.1 v) • (e (starLinkProjection K v
      ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, h⟩⟩) : E)
  else 0

private theorem norm_starBallMap (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1)
    (x : closedStarRealization K {v}) : ‖starBallMap e x‖ = 1 - x.1.1 v := by
  by_cases hx : x.1.1 v < 1
  · simp only [starBallMap, hx, ↓reduceDIte, norm_smul, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hx)]
    rw [mem_sphere_zero_iff_norm.mp (e _).2, mul_one]
  · have heq : x.1.1 v = 1 := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
    simp [starBallMap, heq]

private theorem starBallMap_ray (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1)
    (y : geometricLink K v) (t : Ico (0 : ℝ) 1) :
    starBallMap e ⟨(starRay K v y t).1,
      ((mem_puncturedClosedStar K v _).mp (starRay K v y t).2).1⟩ =
      (1 - (t : ℝ)) • (e y : E) := by
  have ht : (starRay K v y t).1.1 v < 1 := by simpa using t.2.2
  rw [starBallMap, dite_eq_left ht]
  simp

private def ballStarMap (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1)
    (z : Metric.closedBall (0 : E) 1) : closedStarRealization K {v} := by
  classical
  exact if hz : (z : E) = 0 then starApex K v else
    let y := e.symm ⟨normalize (z : E), mem_sphere_zero_iff_norm.mpr (norm_normalize hz)⟩
    let t : Ico (0 : ℝ) 1 :=
      ⟨1 - ‖(z : E)‖, sub_nonneg.mpr (mem_closedBall_zero_iff.mp z.2),
        by linarith [norm_pos_iff.mpr hz]⟩
    ⟨(starRay K v y t).1, ((mem_puncturedClosedStar K v _).mp (starRay K v y t).2).1⟩

private theorem ballStarMap_starBallMap
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1)
    (x : closedStarRealization K {v}) :
    ballStarMap e ⟨starBallMap e x, mem_closedBall_zero_iff.mpr
      (by rw [norm_starBallMap]; linarith [Realization.nonneg K x.1 v])⟩ = x := by
  by_cases hx : x.1.1 v < 1
  · have hn : starBallMap e x ≠ 0 := by
      intro h
      have := norm_starBallMap e x
      rw [h, norm_zero] at this
      linarith
    have hdir : normalize (starBallMap e x) =
        (e (starLinkProjection K v ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩) : E) := by
      rw [starBallMap, dite_eq_left hx, normalize_smul_of_pos (sub_pos.mpr hx)]
      exact normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp (e _).2)
    have hs : (⟨normalize (starBallMap e x),
        mem_sphere_zero_iff_norm.mpr (norm_normalize hn)⟩ : Metric.sphere (0 : E) 1) =
        e (starLinkProjection K v
          ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩) := Subtype.ext hdir
    have ht : (⟨1 - ‖starBallMap e x‖, by
        rw [norm_starBallMap]
        linarith [Realization.nonneg K x.1 v], by rw [norm_starBallMap]; linarith⟩ :
        Ico (0 : ℝ) 1) = ⟨x.1.1 v, Realization.nonneg K x.1 v, hx⟩ :=
      Subtype.ext (by simp only [norm_starBallMap]; ring)
    simp only [ballStarMap, hn, ↓reduceDIte, hs, e.symm_apply_apply, ht]
    exact Subtype.ext (congrArg (fun z : puncturedClosedStar K v => z.1)
      (starRay_starLinkProjection K v ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩))
  · have heq : x.1.1 v = 1 := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
    have hv : x.1 = vertex K v := (Realization.eq_vertex_iff K x.1 v).mpr heq
    simp only [starBallMap, hx, ↓reduceDIte, ballStarMap, ↓reduceDIte]
    exact Subtype.ext (by simpa using hv.symm)

private theorem starBallMap_ballStarMap
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1)
    (z : Metric.closedBall (0 : E) 1) : starBallMap e (ballStarMap e z) = z := by
  by_cases hz : (z : E) = 0
  · simp [ballStarMap, hz, starBallMap]
  · simp only [ballStarMap, hz, ↓reduceDIte, starBallMap_ray, e.apply_symm_apply,
      sub_sub_cancel, norm_smul_normalize]

private theorem continuous_starBallMap
    (hK : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1) : Continuous (starBallMap e) := by
  have hc : Continuous (fun x : closedStarRealization K {v} => x.1.1 v) :=
    (continuous_apply v).comp ((continuous_realization_coe K).comp continuous_subtype_val)
  have hC := (K.isClosedEmbedding_realization_coe_restrict hK).isEmbedding
  let S : Set (closedStarRealization K {v}) := {x | x.1.1 v < 1}
  have hS : IsOpen S := isOpen_lt hc continuous_const
  have hp : Continuous (fun x : S => starLinkProjection K v
      ⟨x.1.1, (mem_puncturedClosedStar K v _).mpr ⟨x.1.2, x.2⟩⟩) := by
    -- The link embeds into the compact closed star, so test continuity in coordinates.
    have hi : Topology.IsEmbedding (fun y : geometricLink K v =>
        (y.1.1 : ι → ℝ)) := hC.comp (Topology.IsEmbedding.inclusion
      (fun _ hy => ((mem_geometricLink K v _).mp hy).2))
    apply hi.continuous_iff.mpr
    apply continuous_pi
    intro j
    simp only [Function.comp_apply, starLinkProjection_apply]
    by_cases hj : j = v
    · simp only [hj, ↓reduceIte]
      exact continuous_const
    · simp only [hj, ↓reduceIte]
      have hcoord (j : ι) : Continuous (fun x : S => x.1.1.1 j) :=
        (continuous_apply j).comp ((continuous_realization_coe K).comp
          (continuous_subtype_val.comp continuous_subtype_val))
      exact ((continuous_const.sub (hcoord v)).inv₀
        (fun x => (sub_pos.mpr x.2).ne')).mul (hcoord j)
  have haway : ContinuousOn (starBallMap e) S := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h : Continuous (fun x : S => (1 - x.1.1.1 v) •
        (e (starLinkProjection K v
          ⟨x.1.1, (mem_puncturedClosedStar K v _).mpr ⟨x.1.2, x.2⟩⟩) : E)) :=
      ((continuous_const : Continuous (fun _ : S => (1 : ℝ))).sub
      (hc.comp continuous_subtype_val)).smul
      (continuous_subtype_val.comp (e.continuous.comp hp))
    exact h.congr fun x => (dite_eq_left x.2 : starBallMap e x.1 = _).symm
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x.1.1 v < 1
  · exact haway.continuousAt (hS.mem_nhds hx)
  · -- At the apex, the norm is exactly the remaining barycentric mass.
    have heq : x.1.1 v = 1 := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
    have hnorm : Tendsto (fun y : closedStarRealization K {v} => ‖starBallMap e y‖)
        (𝓝 x) (𝓝 0) := by
      have hd : Continuous (fun y : closedStarRealization K {v} => 1 - y.1.1 v) :=
        continuous_const.sub hc
      simpa only [ContinuousAt, norm_starBallMap, heq, sub_self] using hd.continuousAt (x := x)
    simpa only [ContinuousAt, starBallMap, hx, ↓reduceDIte] using
      tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- A spherical link identifies its compact closed vertex star with the closed unit ball.
The apex is sent to zero, and the link is sent to the unit sphere. -/
def closedStarHomeomorphClosedBall
    (hK : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1) :
    closedStarRealization K {v} ≃ₜ Metric.closedBall (0 : E) 1 := by
  let : CompactSpace (closedStarRealization K {v}) :=
    isCompact_iff_compactSpace.mp hK
  let f : closedStarRealization K {v} ≃ Metric.closedBall (0 : E) 1 := {
    toFun x := ⟨starBallMap e x, mem_closedBall_zero_iff.mpr
      (by rw [norm_starBallMap]; linarith [Realization.nonneg K x.1 v])⟩
    invFun := ballStarMap e
    left_inv := ballStarMap_starBallMap e
    right_inv z := Subtype.ext (starBallMap_ballStarMap e z) }
  exact Continuous.homeoOfEquivCompactToT2
    (f := f) ((continuous_starBallMap hK e).subtype_mk _)

variable (hK : IsCompact (closedStarRealization K {v}))
  (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1)

/-- Away from the apex, the ball model scales the spherical link image by the remaining mass. -/
theorem closedStarHomeomorphClosedBall_apply_of_lt (x : closedStarRealization K {v})
    (hx : x.1.1 v < 1) :
    (closedStarHomeomorphClosedBall hK e x : E) = (1 - x.1.1 v) •
      (e (starLinkProjection K v
        ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩) : E) :=
  (dite_eq_left hx : starBallMap e x = _)

/-- The norm in the ball model is one minus the apex coordinate. -/
@[simp]
theorem norm_closedStarHomeomorphClosedBall (x : closedStarRealization K {v}) :
    ‖(closedStarHomeomorphClosedBall hK e x : E)‖ = 1 - x.1.1 v :=
  norm_starBallMap e x

/-- The ball model takes the apex to the origin. -/
@[simp]
theorem closedStarHomeomorphClosedBall_starApex :
    (closedStarHomeomorphClosedBall hK e (starApex K v) : E) = 0 := by
  apply norm_eq_zero.mp
  simp

/-- On a ray, the ball model scales the link image by the mass outside the apex. -/
@[simp]
theorem closedStarHomeomorphClosedBall_starRay (y : geometricLink K v) (t : Ico (0 : ℝ) 1) :
    (closedStarHomeomorphClosedBall hK e
      ⟨(starRay K v y t).1, ((mem_puncturedClosedStar K v _).mp (starRay K v y t).2).1⟩ : E) =
        (1 - (t : ℝ)) • (e y : E) := starBallMap_ray e y t

/-- The inverse sends zero to the apex. -/
@[simp]
theorem closedStarHomeomorphClosedBall_symm_zero :
    (closedStarHomeomorphClosedBall hK e).symm ⟨0, by simp⟩ = starApex K v := by
  apply (closedStarHomeomorphClosedBall hK e).injective
  apply Subtype.ext
  simp

/-- Away from zero, the inverse ball model follows the link direction of the normalized vector
and gives the apex coordinate `1 - ‖z‖`. -/
theorem closedStarHomeomorphClosedBall_symm_apply_of_ne
    (z : Metric.closedBall (0 : E) 1) (hz : (z : E) ≠ 0) :
    (closedStarHomeomorphClosedBall hK e).symm z =
      ⟨(starRay K v
        (e.symm ⟨normalize (z : E), mem_sphere_zero_iff_norm.mpr (norm_normalize hz)⟩)
        ⟨1 - ‖(z : E)‖, sub_nonneg.mpr (mem_closedBall_zero_iff.mp z.2),
          by linarith [norm_pos_iff.mpr hz]⟩).1,
        ((mem_puncturedClosedStar K v _).mp (starRay K v _ _).2).1⟩ := by
  -- This equation records the inverse chosen in the defining equivalence.
  have h : (closedStarHomeomorphClosedBall hK e).symm z = ballStarMap e z := (rfl)
  rw [h, ballStarMap, dite_eq_right hz]

/-- Restrict the spherical-link ball model to an open vertex star, obtaining an open ball.
This supplies the topological local model at the star's apex. -/
def openStarHomeomorphBall
    (hK : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1) :
    openStarRealization K v ≃ₜ Metric.ball (0 : E) 1 := by
  let H := closedStarHomeomorphClosedBall hK e
  let f : openStarRealization K v → Metric.ball (0 : E) 1 := fun x =>
    ⟨(H ⟨x.1, K.openStarRealization_subset_closedStarRealization v x.2⟩ : E),
      by simpa only [H, Metric.mem_ball, dist_zero_right,
        norm_closedStarHomeomorphClosedBall, sub_lt_self_iff, mem_openStarRealization] using x.2⟩
  let g : Metric.ball (0 : E) 1 → openStarRealization K v := fun y =>
    ⟨(H.symm ⟨y.1, mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp y.2).le⟩).1, by
      have hball : (H (H.symm
          ⟨y.1, mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp y.2).le⟩) : E) ∈
          Metric.ball (0 : E) 1 := by simp only [Homeomorph.apply_symm_apply]; exact y.2
      simpa only [H, Metric.mem_ball, dist_zero_right, norm_closedStarHomeomorphClosedBall,
        sub_lt_self_iff, mem_openStarRealization] using hball⟩
  exact {
    toFun := f
    invFun := g
    left_inv x := Subtype.ext (congrArg (fun z : closedStarRealization K {v} => z.1)
      (H.symm_apply_apply ⟨x.1, K.openStarRealization_subset_closedStarRealization v x.2⟩))
    right_inv y := Subtype.ext (congrArg (fun z : Metric.closedBall (0 : E) 1 => z.1)
      (H.apply_symm_apply ⟨y.1, mem_closedBall_zero_iff.mpr
        (mem_ball_zero_iff.mp y.2).le⟩))
    continuous_toFun := (continuous_subtype_val.comp
      (H.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp
      (H.symm.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _ }

/-- The open-star model is the restriction of the closed-star model. -/
@[simp]
theorem openStarHomeomorphBall_apply (x : openStarRealization K v) :
    (openStarHomeomorphBall hK e x : E) =
      (closedStarHomeomorphClosedBall hK e
        ⟨x.1, K.openStarRealization_subset_closedStarRealization v x.2⟩ : E) := (rfl)

/-- The inverse open-star model is the restriction of the inverse closed-star model. -/
@[simp]
theorem openStarHomeomorphBall_symm_apply (y : Metric.ball (0 : E) 1) :
    ((openStarHomeomorphBall hK e).symm y : Realization K) =
      ((closedStarHomeomorphClosedBall hK e).symm
        ⟨y.1, mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp y.2).le⟩).1 := (rfl)

end AbstractSimplicialComplex
