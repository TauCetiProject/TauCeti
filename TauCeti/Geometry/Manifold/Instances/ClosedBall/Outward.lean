/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Inclusion
public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The radial vector is outward for the closed ball

The squared norm has its constrained maximum at the sphere. Its actual derivative, expressed
in a half-space chart, determines the inward normal functional. Invertibility of the inclusion
derivative makes the normal coefficient strictly positive, so the radial vector points outward.
-/

public section

noncomputable section

open Set Metric Filter
open scoped Manifold Topology RealInnerProductSpace

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = n + 1)]

/-- Under the actual inclusion tangent equivalence, the unit radial vector points outward at
 every boundary point of the closed ball. -/
theorem isOutwardPointing_closedBall_radial (x : closedBall (0 : E) 1)
    (hx : x ∈ (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    IsOutwardPointing x ((subtypeValClosedBallTangentEquiv (n := n + 1) x).symm (x : E)) := by
  let I := 𝓡∂ (n + 1)
  let F : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] E :=
    subtypeValClosedBallTangentEquiv (n := n + 1) x
  let y := extChartAt I x x
  let f : EuclideanSpace ℝ (Fin (n + 1)) → E :=
    Subtype.val ∘ (extChartAt I x).symm
  have hxnorm : ‖(x : E)‖ = 1 := by
    simpa only [boundary_closedBall, mem_preimage, mem_sphere, dist_zero_right] using hx
  have hy0 : y 0 = 0 := by
    have h := (ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas
      one_ne_zero (chart_mem_atlas _ x) (mem_chart_source _ x)).mp hx
    simpa only [y, I, extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      modelWithCornersEuclideanHalfSpace_toFun] using h
  have hfy : f y = (x : E) := by
    dsimp only [f, y, Function.comp_apply]
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
  have hdiff := (contMDiff_subtypeVal_closedBall (n := n + 1) (k := 1)).mdifferentiable
    one_ne_zero x
  have hdf : HasFDerivWithinAt f F.toContinuousLinearMap (range I) y := by
    have h := hdiff.hasMFDerivAt.2
    rw [writtenInExtChartAt, extChartAt_model_space_eq_id] at h
    simp only [PartialEquiv.refl_coe, Function.id_comp] at h
    convert! h using 2
    exact subtypeValClosedBallTangentEquiv_toContinuousLinearMap (n := n + 1) x
  let ν : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
    -(2 • (innerSL ℝ (x : E)).comp F.toContinuousLinearMap)
  have hdν : HasFDerivWithinAt (fun z ↦ -‖f z‖ ^ 2) ν (range I) y := by
    have h := hdf.norm_sq.neg
    rw [hfy] at h
    convert! h using 1
  have hmin : IsLocalMinOn (fun z ↦ -‖f z‖ ^ 2) (range I) y := by
    filter_upwards [] with z
    have hz : ‖f z‖ ≤ 1 := by
      exact mem_closedBall_zero_iff.mp ((extChartAt I x).symm z).property
    rw [hfy, hxnorm]
    nlinarith [norm_nonneg (f z)]
  have hnonneg (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : 0 ≤ v 0) : 0 ≤ ν v := by
    apply hmin.hasFDerivWithinAt_nonneg hdν
    apply mem_posTangentConeAt_of_segment_subset
    apply I.convex_range.segment_subset (mem_range_self (chartAt _ x x))
    rw [range_modelWithCornersEuclideanHalfSpace]
    simpa only [mem_ofPred_eq, PiLp.add_apply, hy0, zero_add] using hv
  let a := ν (EuclideanSpace.single 0 1)
  have ha : 0 ≤ a := hnonneg _ (by simp)
  have hfactor := ν.eq_mul_apply_zero_of_nonneg hnonneg (F.symm (x : E))
  have hval : ν (F.symm (x : E)) = -2 := by
    dsimp only [ν]
    rw [neg_apply, smul_apply,
      ContinuousLinearMap.comp_apply]
    -- The linear-map coercion and the tangent equivalence have the same underlying
    -- application, but rw does not unfold that coercion before matching the inverse law.
    change -(2 • ⟪(x : E), F (F.symm (x : E))⟫) = -2
    rw [F.apply_symm_apply, real_inner_self_eq_norm_sq, hxnorm]
    norm_num
  rw [hval] at hfactor
  have hout : (F.symm (x : E) : EuclideanSpace ℝ (Fin (n + 1))) 0 < 0 := by
    dsimp only [a] at hfactor
    by_contra h
    have := mul_nonneg ha (le_of_not_gt h)
    linarith
  rw [isOutwardPointing_iff, and_iff_right hx, mfderiv_extChartAt_self]
  exact hout

end TauCeti
