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
* `TauCeti.RealOpenUnitBall.radialSegment`: the concrete radial segment from the centre to a point.
* `TauCeti.RealOpenUnitBall.exists_pathELength_eq_edist`: every point is joined to the centre by
  a `C¹` path whose Riemannian length realizes the distance.
* `TauCeti.RealOpenUnitBall.not_completeSpace`: the open unit ball is not complete.
* `TauCeti.RealOpenUnitBall.closedBall_center_eq_univ`: every closed ball of radius at least one
  is the whole space.
* `TauCeti.RealOpenUnitBall.not_isCompact_closedBall_center` and
  `TauCeti.RealOpenUnitBall.not_properSpace`: those closed balls are not compact, so the space is
  not proper.
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

/-- The Riemannian structure on the real open unit ball induced from `ℝ`. -/
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

/-- The radial segment from the centre to `q`, affinely parametrized on `[0, 1]` and clamped
outside that interval. -/
def radialSegment (q : realOpenUnitBall) : ℝ → realOpenUnitBall :=
  TauCeti.TopologicalSpace.Opens.convexSegment realOpenUnitBall
    (convex_ball (0 : ℝ) 1) center q

/-- On `[0, 1]`, the radial segment from the centre to `q` is `t ↦ t * q`. -/
theorem coe_radialSegment (q : realOpenUnitBall) (t : ℝ) (ht : t ∈ Icc 0 1) :
    (radialSegment q t : ℝ) = t * (q : ℝ) := by
  calc
    (radialSegment q t : ℝ) =
        ⇑(ContinuousAffineMap.lineMap (R := ℝ) (center : ℝ) (q : ℝ)) t := by
      simpa only [radialSegment, Function.comp_apply] using
        TauCeti.TopologicalSpace.Opens.convexSegment_val_eqOn realOpenUnitBall
          (convex_ball (0 : ℝ) 1) center q t ht
    _ = t * (q : ℝ) := by
      simp [ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_module]

/-- The radial segment starts at the centre of the open unit ball. -/
@[simp]
theorem radialSegment_zero (q : realOpenUnitBall) : radialSegment q 0 = center :=
  TauCeti.TopologicalSpace.Opens.convexSegment_zero realOpenUnitBall
    (convex_ball (0 : ℝ) 1) center q

/-- The radial segment ends at `q`. -/
@[simp]
theorem radialSegment_one (q : realOpenUnitBall) : radialSegment q 1 = q :=
  TauCeti.TopologicalSpace.Opens.convexSegment_one realOpenUnitBall
    (convex_ball (0 : ℝ) 1) center q

/-- The radial segment is `C¹` on `[0, 1]`. -/
theorem contMDiffOn_radialSegment (q : realOpenUnitBall) :
    CMDiff[Icc 0 1] 1 (radialSegment q) :=
  TauCeti.TopologicalSpace.Opens.contMDiffOn_convexSegment realOpenUnitBall
    (convex_ball (0 : ℝ) 1) center q

/-- The radial segment realizes the distance from the centre to `q`. -/
theorem pathELength_radialSegment (q : realOpenUnitBall) :
    pathELength 𝓘(ℝ, ℝ) (radialSegment q) 0 1 = edist center q :=
  TauCeti.TopologicalSpace.Opens.pathELength_convexSegment_eq_edist realOpenUnitBall
    (convex_ball (0 : ℝ) 1) center q

/-- Every point of the real open unit ball is joined to its centre by its radial `C¹` segment,
whose Riemannian length is exactly the distance between its endpoints. -/
theorem exists_pathELength_eq_edist (q : realOpenUnitBall) :
    ∃ γ : ℝ → realOpenUnitBall, CMDiff[Icc 0 1] 1 γ ∧ γ 0 = center ∧ γ 1 = q ∧
      pathELength 𝓘(ℝ, ℝ) γ 0 1 = edist center q := by
  exact ⟨radialSegment q, contMDiffOn_radialSegment q, radialSegment_zero q,
    radialSegment_one q, pathELength_radialSegment q⟩

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

/-- A closed ball of radius at least one about the centre is the whole real open unit ball. -/
theorem closedBall_center_eq_univ (r : ℝ) (hr : 1 ≤ r) :
    Metric.closedBall center r = univ := by
  apply eq_univ_of_forall
  intro x
  rw [mem_closedBall]
  have hdist : dist x center = |(x : ℝ)| := by
    rw [Subtype.dist_eq, coe_center, Real.dist_eq, sub_zero]
  rw [hdist]
  exact (mem_iff.mp x.property).le.trans hr

/-- A closed ball of radius at least one about the centre of the real open unit ball is not
compact. -/
theorem not_isCompact_closedBall_center (r : ℝ) (hr : 1 ≤ r) :
    ¬ IsCompact (Metric.closedBall center r) := by
  rw [closedBall_center_eq_univ r hr, isCompact_univ_iff]
  intro hcompact
  let _ := hcompact
  exact not_completeSpace inferInstance

/-- The real open unit ball is not a proper metric space. -/
theorem not_properSpace : ¬ ProperSpace realOpenUnitBall := by
  intro hproper
  let _ := hproper
  exact not_isCompact_closedBall_center 2 (by norm_num) (isCompact_closedBall center 2)

end RealOpenUnitBall

end TauCeti

end
