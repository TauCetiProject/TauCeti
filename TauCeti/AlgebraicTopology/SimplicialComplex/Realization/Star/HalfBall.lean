/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Hemispherical vertex links and half-ball charts

A homeomorphism of a vertex link with a closed hemisphere extends radially to a
homeomorphism of its compact closed star with a closed half-ball. The apex goes to zero,
and the norm is the mass outside the apex. Restricting to positive apex coordinate
therefore gives the boundary local model: an open half-ball, including its flat boundary.

These are topological local models. No piecewise-linear regularity is asserted. A ball
link can be identified with a hemisphere using `TauCeti.hemisphereHomeomorph`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2,
  “Pseudo-Radial Projection”, pp. 20–21 (conical extension of link models).
-/

public section

noncomputable section

open Set Metric Filter
open scoped Topology RealInnerProductSpace

namespace AbstractSimplicialComplex

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {v : ι} {p : sphere (0 : E) 1}

private def halfBallMap
    (e : geometricLink K v ≃ₜ {z : sphere (0 : E) 1 // 0 ≤ ⟪(z : E), (p : E)⟫})
    (x : closedStarRealization K {v}) : E :=
  if h : x.1.1 v < 1 then
    (1 - x.1.1 v) • ((e (starLinkProjection K v
      ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, h⟩⟩)).1 : E)
  else 0

private theorem norm_halfBallMap
    (e : geometricLink K v ≃ₜ {z : sphere (0 : E) 1 // 0 ≤ ⟪(z : E), (p : E)⟫})
    (x : closedStarRealization K {v}) : ‖halfBallMap e x‖ = 1 - x.1.1 v := by
  by_cases hx : x.1.1 v < 1
  · simp [halfBallMap, hx, norm_smul, abs_of_nonneg (sub_pos.mpr hx).le,
      norm_eq_of_mem_sphere]
  · have heq := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
    simp [halfBallMap, heq]

private theorem halfBallMap_mem
    (e : geometricLink K v ≃ₜ {z : sphere (0 : E) 1 // 0 ≤ ⟪(z : E), (p : E)⟫})
    (x : closedStarRealization K {v}) :
    halfBallMap e x ∈ closedBall (0 : E) 1 ∩ {z | 0 ≤ ⟪z, (p : E)⟫} := by
  refine ⟨mem_closedBall_zero_iff.mpr ?_, ?_⟩
  · rw [norm_halfBallMap]
    linarith [Realization.nonneg K x.1 v]
  · by_cases hx : x.1.1 v < 1
    · simp only [halfBallMap, hx, ↓reduceDIte, mem_ofPred_eq, real_inner_smul_left]
      exact mul_nonneg (sub_pos.mpr hx).le (e _).2
    · simp [halfBallMap, hx]

private theorem halfBallMap_starRay
    (e : geometricLink K v ≃ₜ {z : sphere (0 : E) 1 // 0 ≤ ⟪(z : E), (p : E)⟫})
    (y : geometricLink K v) (t : Ico (0 : ℝ) 1) :
    halfBallMap e ⟨(starRay K v y t).1, ((mem_puncturedClosedStar K v _).mp
      (starRay K v y t).2).1⟩ =
      (1 - t.1) • ((e y).1 : E) := by
  simp [halfBallMap, t.2.2]

private theorem halfBallMap_bijective
    (e : geometricLink K v ≃ₜ {z : sphere (0 : E) 1 // 0 ≤ ⟪(z : E), (p : E)⟫}) :
    Function.Bijective (fun x : closedStarRealization K {v} =>
      (⟨halfBallMap e x, halfBallMap_mem e x⟩ :
        ↥(closedBall (0 : E) 1 ∩ {z | 0 ≤ ⟪z, (p : E)⟫}))) := by
  constructor
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    have hc : x.1.1 v = y.1.1 v := by
      have hn := congrArg norm h
      rw [norm_halfBallMap, norm_halfBallMap] at hn
      linarith
    by_cases hx : x.1.1 v < 1
    · have hy : y.1.1 v < 1 := hc ▸ hx
      have hlink : starLinkProjection K v ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩ =
          starLinkProjection K v ⟨y.1, (mem_puncturedClosedStar K v _).mpr ⟨y.2, hy⟩⟩ := by
        apply e.injective
        apply Subtype.ext
        apply Subtype.ext
        simp only [halfBallMap, hx, ↓reduceDIte, ← hc] at h
        exact (smul_right_injective E (sub_pos.mpr hx).ne').eq_iff.mp h
      have hr := congrArg Subtype.val (starRay_starLinkProjection K v
        ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩)
      have hs := congrArg Subtype.val (starRay_starLinkProjection K v
        ⟨y.1, (mem_puncturedClosedStar K v _).mpr ⟨y.2, hy⟩⟩)
      apply Subtype.ext
      rw [← hr, ← hs, hlink]
      congr 2
      exact Subtype.ext hc
    · have hx1 : x.1.1 v = 1 := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
      apply Subtype.ext
      exact ((Realization.eq_vertex_iff K x.1 v).mpr hx1).trans
        ((Realization.eq_vertex_iff K y.1 v).mpr (hc ▸ hx1)).symm
  · intro z
    by_cases hz : (z : E) = 0
    · refine ⟨starApex K v, Subtype.ext ?_⟩
      simp [halfBallMap, hz]
    · let u : {z : sphere (0 : E) 1 // 0 ≤ ⟪(z : E), (p : E)⟫} :=
        ⟨⟨‖(z : E)‖⁻¹ • (z : E), mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hz)⟩,
          by simpa only [real_inner_smul_left] using
            mul_nonneg (inv_nonneg.mpr (norm_nonneg (z : E))) z.2.2⟩
      let t : Ico (0 : ℝ) 1 := ⟨1 - ‖(z : E)‖,
        sub_nonneg.mpr (mem_closedBall_zero_iff.mp z.2.1),
        by linarith [norm_pos_iff.mpr hz]⟩
      refine ⟨⟨(starRay K v (e.symm u) t).1, ((mem_puncturedClosedStar K v _).mp
        (starRay K v (e.symm u) t).2).1⟩,
        Subtype.ext ?_⟩
      dsimp only
      rw [halfBallMap_starRay, e.apply_symm_apply]
      simp [t, u, smul_smul, norm_ne_zero_iff.mpr hz]

private theorem continuous_halfBallMap
    (hcompact : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ {z : sphere (0 : E) 1 // 0 ≤ ⟪(z : E), (p : E)⟫}) :
    Continuous (halfBallMap e) := by
  have hc : Continuous (fun x : closedStarRealization K {v} => x.1.1 v) :=
    (continuous_apply v).comp ((continuous_realization_coe K).comp continuous_subtype_val)
  let S : Set (closedStarRealization K {v}) := {x | x.1.1 v < 1}
  have hS : IsOpen S := isOpen_lt hc continuous_const
  have haway : ContinuousOn (halfBallMap e) S := by
    rw [continuousOn_iff_continuous_domRestrict]
    let q : S → puncturedClosedStar K v := fun x =>
      ⟨x.1.1, (mem_puncturedClosedStar K v _).mpr ⟨x.1.2, x.2⟩⟩
    have hq : Continuous q :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have he := continuous_subtype_val.comp (continuous_subtype_val.comp
      (e.continuous.comp ((continuous_starLinkProjection_of_isCompact K v hcompact).comp hq)))
    exact ((((continuous_const (y := (1 : ℝ))).sub hc).comp continuous_subtype_val).smul he).congr
      fun x => by
        have hx : x.1.1.1 v < 1 := x.2
        simp [halfBallMap, hx, q, Set.domRestrict]
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x.1.1 v < 1
  · exact haway.continuousAt (hS.mem_nhds hx)
  · have hx1 := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
    have hnorm : Tendsto (fun y => ‖halfBallMap e y‖) (𝓝 x) (𝓝 0) := by
      simpa only [norm_halfBallMap, ContinuousAt, Pi.sub_def, hx1, sub_self] using
        ((continuous_const (y := (1 : ℝ))).sub hc).continuousAt (x := x)
    simpa only [ContinuousAt, halfBallMap, hx, ↓reduceDIte] using
      (tendsto_zero_iff_norm_tendsto_zero.mpr hnorm)

/-- A hemispherical link identifies its compact closed star with a closed half-ball,
including the apex at the origin. -/
def closedStarHomeomorphHalfBall
    (hcompact : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ {z : sphere (0 : E) 1 // 0 ≤ ⟪(z : E), (p : E)⟫}) :
    closedStarRealization K {v} ≃ₜ
      ↥(closedBall (0 : E) 1 ∩ {z | 0 ≤ ⟪z, (p : E)⟫}) := by
  letI : CompactSpace (closedStarRealization K {v}) := isCompact_iff_compactSpace.mp hcompact
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (halfBallMap_bijective e))
    ((continuous_halfBallMap hcompact e).subtype_mk (halfBallMap_mem e))

/-- The forward closed-star chart is the radial half-ball map. -/
private theorem coe_closedStarHomeomorphHalfBall
    (hcompact : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ {z : sphere (0 : E) 1 // 0 ≤ ⟪(z : E), (p : E)⟫})
    (x : closedStarRealization K {v}) :
    (closedStarHomeomorphHalfBall hcompact e x : E) = halfBallMap e x := by
  -- Both homeoOfEquivCompactToT2 and Equiv.ofBijective preserve the forward function.
  rfl

/-- The radius in the half-ball is exactly the mass away from the apex. -/
@[simp]
theorem norm_closedStarHomeomorphHalfBall
    (hcompact : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ {z : sphere (0 : E) 1 // 0 ≤ ⟪(z : E), (p : E)⟫})
    (x : closedStarRealization K {v}) :
    ‖(closedStarHomeomorphHalfBall hcompact e x : E)‖ = 1 - x.1.1 v := by
  rw [coe_closedStarHomeomorphHalfBall, norm_halfBallMap]

variable (hcompact : IsCompact (closedStarRealization K {v}))
  (e : geometricLink K v ≃ₜ {z : sphere (0 : E) 1 // 0 ≤ ⟪(z : E), (p : E)⟫})

/-- Away from the apex the half-ball chart scales the link identification by the
mass outside the apex. -/
@[simp]
theorem coe_closedStarHomeomorphHalfBall_of_lt
    (x : closedStarRealization K {v}) (hx : x.1.1 v < 1) :
    (closedStarHomeomorphHalfBall hcompact e x : E) =
      (1 - x.1.1 v) • ((e (starLinkProjection K v
        ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩)).1 : E) := by
  rw [coe_closedStarHomeomorphHalfBall, halfBallMap, dite_eq_left hx]

/-- The closed half-ball chart sends its apex to the origin. -/
@[simp]
theorem coe_closedStarHomeomorphHalfBall_starApex :
    (closedStarHomeomorphHalfBall hcompact e (starApex K v) : E) = 0 := by
  apply norm_eq_zero.mp
  simp

/-- A ray in the vertex star becomes the corresponding radial segment in the half-ball. -/
@[simp]
theorem coe_closedStarHomeomorphHalfBall_starRay
    (y : geometricLink K v) (t : Ico (0 : ℝ) 1) :
    (closedStarHomeomorphHalfBall hcompact e
      ⟨(starRay K v y t).1, ((mem_puncturedClosedStar K v _).mp
        (starRay K v y t).2).1⟩ : E) = (1 - t.1) • ((e y).1 : E) := by
  rw [coe_closedStarHomeomorphHalfBall, halfBallMap_starRay]

/-- The inverse chart recovers the barycentric coordinate at the apex from the radius. -/
@[simp]
theorem closedStarHomeomorphHalfBall_symm_apex_coordinate
    (z : ↥(closedBall (0 : E) 1 ∩ {z | 0 ≤ ⟪z, (p : E)⟫})) :
    ((closedStarHomeomorphHalfBall hcompact e).symm z).1.1 v = 1 - ‖(z : E)‖ := by
  have h := norm_closedStarHomeomorphHalfBall hcompact e
    ((closedStarHomeomorphHalfBall hcompact e).symm z)
  rw [Homeomorph.apply_symm_apply] at h
  linarith

/-- The inverse closed half-ball chart sends the origin back to the star apex. -/
@[simp]
theorem closedStarHomeomorphHalfBall_symm_zero :
    (closedStarHomeomorphHalfBall hcompact e).symm ⟨0, by simp⟩ = starApex K v := by
  apply (closedStarHomeomorphHalfBall hcompact e).injective
  apply Subtype.ext
  simp

/-- The open vertex star is homeomorphic to the open unit half-ball. The origin is
included, so this chart contains the boundary vertex itself. -/
def openStarHomeomorphHalfBall :
    openStarRealization K v ≃ₜ ↥(ball (0 : E) 1 ∩ {z | 0 ≤ ⟪z, (p : E)⟫}) where
  toFun x :=
    let y := closedStarHomeomorphHalfBall hcompact e
      ⟨x.1, openStarRealization_subset_closedStarRealization K v x.2⟩
    ⟨y, mem_ball_zero_iff.mpr (by
      rw [norm_closedStarHomeomorphHalfBall]
      linarith [(mem_openStarRealization K).mp x.2]), y.2.2⟩
  invFun z :=
    let y := (closedStarHomeomorphHalfBall hcompact e).symm
      ⟨z.1, ball_subset_closedBall z.2.1, z.2.2⟩
    ⟨y.1, (mem_openStarRealization K).mpr (by
      rw [closedStarHomeomorphHalfBall_symm_apex_coordinate]
      linarith [mem_ball_zero_iff.mp z.2.1])⟩
  left_inv x := by
    dsimp only
    apply Subtype.ext
    exact congrArg (fun y : closedStarRealization K {v} => y.1)
      ((closedStarHomeomorphHalfBall hcompact e).symm_apply_apply
        ⟨x.1, openStarRealization_subset_closedStarRealization K v x.2⟩)
  right_inv z := by
    dsimp only
    apply Subtype.ext
    exact congrArg (fun y : ↥(closedBall (0 : E) 1 ∩ {z | 0 ≤ ⟪z, (p : E)⟫}) => y.1)
      ((closedStarHomeomorphHalfBall hcompact e).apply_symm_apply
        ⟨z.1, ball_subset_closedBall z.2.1, z.2.2⟩)
  continuous_toFun := by
    exact (continuous_subtype_val.comp ((closedStarHomeomorphHalfBall hcompact e).continuous.comp
      (continuous_inclusion (openStarRealization_subset_closedStarRealization K v)))).subtype_mk _
  continuous_invFun := by
    exact (continuous_subtype_val.comp
      ((closedStarHomeomorphHalfBall hcompact e).symm.continuous.comp
        (continuous_inclusion (inter_subset_inter_left _ ball_subset_closedBall)))).subtype_mk _

/-- The open half-ball chart is the restriction of the closed half-ball chart. -/
@[simp]
theorem coe_openStarHomeomorphHalfBall_apply (x : openStarRealization K v) :
    (openStarHomeomorphHalfBall hcompact e x : E) =
      closedStarHomeomorphHalfBall hcompact e
        ⟨x.1, openStarRealization_subset_closedStarRealization K v x.2⟩ := (rfl)

/-- The inverse open chart is the restriction of the inverse closed chart. -/
@[simp]
theorem openStarHomeomorphHalfBall_symm_apply
    (z : ↥(ball (0 : E) 1 ∩ {z | 0 ≤ ⟪z, (p : E)⟫})) :
    ((openStarHomeomorphHalfBall hcompact e).symm z).1 =
      ((closedStarHomeomorphHalfBall hcompact e).symm
        ⟨z.1, ball_subset_closedBall z.2.1, z.2.2⟩).1 := (rfl)

end AbstractSimplicialComplex
