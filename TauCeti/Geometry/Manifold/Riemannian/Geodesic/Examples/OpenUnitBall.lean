/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Geometry.Manifold.Riemannian.Convex

/-!
# The incomplete Riemannian open unit ball

The open unit ball in `ℝ`, equipped with the Euclidean Riemannian metric restricted from `ℝ`,
is a basic incomplete Riemannian manifold. Straight segments stay in the ball and realize the
distance between their endpoints, but the space is neither complete nor proper. In particular,
the closed ball of radius two about zero is the whole open unit ball and is not compact.

This example separates the existence of distance-realizing paths from properness. The missing
boundary point `1` witnesses incompleteness: completeness of the subtype would make the open ball
a closed subset of `ℝ`.

## Main results

* `TauCeti.RealOpenUnitBall.isRiemannianManifold`: the ambient metric is the Riemannian distance
  of the restricted Euclidean metric.
* `TauCeti.RealOpenUnitBall.exists_pathELength_eq_edist`: every point is joined to the centre by
  a `C¹` path whose Riemannian length realizes the distance.
* `TauCeti.RealOpenUnitBall.not_completeSpace`: the open unit ball is not complete.
* `TauCeti.RealOpenUnitBall.closedBall_center_two`: its radius-two closed ball is the whole space.
* `TauCeti.RealOpenUnitBall.not_isCompact_closedBall_center_two` and
  `TauCeti.RealOpenUnitBall.not_properSpace`: that closed ball is not compact, so the space is not
  proper.
-/

public section

open Bundle Manifold Metric Set TopologicalSpace
open scoped ENNReal Manifold TauCeti Topology

noncomputable section

namespace TauCeti

/-- The open unit ball in `ℝ`, bundled as an open submanifold. -/
def realOpenUnitBall : Opens ℝ := ⟨Metric.ball 0 1, isOpen_ball⟩

@[simp]
theorem coe_realOpenUnitBall : (realOpenUnitBall : Set ℝ) = Metric.ball 0 1 := by
  simp [realOpenUnitBall]

local instance : RiemannianBundle
    (fun x : realOpenUnitBall ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
  Manifold.instRiemannianBundleOpen realOpenUnitBall

namespace RealOpenUnitBall

/-- The centre of the real open unit ball. -/
def center : realOpenUnitBall := ⟨0, by simp [realOpenUnitBall]⟩

@[simp]
theorem coe_center : (center : ℝ) = 0 := by simp [center]

/-- Membership in the real open unit ball is the strict inequality `|x| < 1`. -/
@[simp]
theorem mem_iff {x : ℝ} : x ∈ realOpenUnitBall ↔ |x| < 1 := by
  simp [realOpenUnitBall]

/-- The ambient metric on the real open unit ball is the Riemannian distance induced by the
restricted Euclidean metric. -/
theorem isRiemannianManifold : IsRiemannianManifold 𝓘(ℝ, ℝ) realOpenUnitBall :=
  Manifold.isRiemannianManifold_of_convex realOpenUnitBall (convex_ball (0 : ℝ) 1)

/-- Every point of the real open unit ball is joined to its centre by a `C¹` path whose
Riemannian length is exactly the distance between its endpoints. -/
theorem exists_pathELength_eq_edist (q : realOpenUnitBall) :
    ∃ γ : ℝ → realOpenUnitBall, CMDiff[Icc 0 1] 1 γ ∧ γ 0 = center ∧ γ 1 = q ∧
      pathELength 𝓘(ℝ, ℝ) γ 0 1 = edist center q := by
  exact Manifold.exists_pathELength_eq_edist_of_convex realOpenUnitBall
    (convex_ball (0 : ℝ) 1) center q

/-- The real open unit ball is not complete. -/
theorem not_completeSpace : ¬ CompleteSpace realOpenUnitBall := by
  intro hcomplete
  let _ := hcomplete
  have hsetComplete : IsComplete (Metric.ball (0 : ℝ) 1) := by
    have huniv : IsComplete (univ : Set realOpenUnitBall) :=
      completeSpace_iff_isComplete_univ.mp inferInstance
    have himage := Subtype.isComplete_iff.mp huniv
    rw [image_univ, Subtype.range_coe_subtype] at himage
    exact himage
  have hclosed : IsClosed (Metric.ball (0 : ℝ) 1) := hsetComplete.isClosed
  have hclosure : Metric.closedBall (0 : ℝ) 1 = Metric.ball 0 1 := by
    rw [← closure_ball (0 : ℝ) one_ne_zero, hclosed.closure_eq]
  have hone : (1 : ℝ) ∈ Metric.closedBall 0 1 := by simp
  rw [hclosure] at hone
  simp at hone

/-- The closed ball of radius two about the centre is the whole real open unit ball. -/
@[simp]
theorem closedBall_center_two : Metric.closedBall center 2 = univ := by
  apply eq_univ_of_forall
  intro x
  rw [mem_closedBall]
  have hdist : dist x center = |(x : ℝ)| := by
    rw [Subtype.dist_eq, coe_center, Real.dist_eq, sub_zero]
  rw [hdist]
  exact (mem_iff.mp x.property).le.trans (by norm_num)

/-- The radius-two closed ball about the centre of the real open unit ball is not compact. -/
theorem not_isCompact_closedBall_center_two :
    ¬ IsCompact (Metric.closedBall center 2) := by
  rw [closedBall_center_two, isCompact_univ_iff]
  intro hcompact
  let _ := hcompact
  exact not_completeSpace inferInstance

/-- The real open unit ball is not a proper metric space. -/
theorem not_properSpace : ¬ ProperSpace realOpenUnitBall := by
  intro hproper
  let _ := hproper
  exact not_isCompact_closedBall_center_two (isCompact_closedBall center 2)

end RealOpenUnitBall

end TauCeti

end
