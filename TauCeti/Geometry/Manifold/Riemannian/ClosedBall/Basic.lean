/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Inclusion
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.Riemannian.Induced

/-!
# The Euclidean metric on the closed unit ball

The closed unit ball of a real inner product space `E` of dimension `n` is an analytic manifold
with boundary modelled on the half-space `𝓡∂ n` (`TauCeti.instChartedSpaceClosedBall`), and the
differential of its inclusion into `E` is invertible at every point, including the points of the
boundary sphere (`TauCeti.subtypeValClosedBallTangentEquiv`). The *Euclidean metric* of the ball
is the Riemannian metric induced by this inclusion: the inner product of two tangent vectors is
the inner product in `E` of their images under the differential of the inclusion. This file
installs it as the `RiemannianBundle` instance on the tangent bundle of the closed ball, together
with its analyticity, so that the closed ball is a Riemannian manifold with boundary.

## Main definitions

* `TauCeti.closedBallEuclideanMetric`: the analytic Euclidean metric on the closed unit ball.
* `TauCeti.instRiemannianBundleClosedBall`, `TauCeti.instIsContMDiffRiemannianBundleClosedBall`
  and `TauCeti.instIsContinuousRiemannianBundleClosedBall`: the corresponding instances, with
  versions for the closed unit ball of `EuclideanSpace ℝ (Fin n)`.
* `TauCeti.closedBallTangentIsometry`: the differential of the inclusion as a linear isometry
  equivalence of each tangent space with `E`.

## Main statements

* `TauCeti.mvfderiv_subtypeVal_closedBall`: the differential of the inclusion, read in `E`, is
  the tangent equivalence `TauCeti.subtypeValClosedBallTangentEquiv`.
* `TauCeti.inner_tangentSpace_closedBall`: the inner product of two tangent vectors is the inner
  product of their images in `E`.
* `TauCeti.norm_tangentSpace_closedBall`: the norm of a tangent vector is the norm of its image in
  `E`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (induced metrics on submanifolds).
-/

public section

open Bundle Metric Module
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n)]

/-- The differential of the inclusion of the closed unit ball into `E`, read in `E`, is the
tangent equivalence `TauCeti.subtypeValClosedBallTangentEquiv`. -/
theorem mvfderiv_subtypeVal_closedBall (x : closedBall (0 : E) 1) :
    mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x =
      (subtypeValClosedBallTangentEquiv (n := n) x).toContinuousLinearMap := by
  rw [mvfderiv, subtypeValClosedBallTangentEquiv_toContinuousLinearMap]

/-- The **Euclidean metric** on the closed unit ball of `E`: the analytic Riemannian metric
induced by the inclusion into `E`. -/
def closedBallEuclideanMetric :
    ContMDiffRiemannianMetric (𝓡∂ n) ω (EuclideanSpace ℝ (Fin n))
      (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ n) x) :=
  inducedRiemannianMetric (n := ω) (Subtype.val : closedBall (0 : E) 1 → E)
    contMDiff_subtypeVal_closedBall fun x _ _ h ↦ injective_mfderiv_subtypeVal_closedBall x
      (by rwa [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply] at h)

/-- The Euclidean metric evaluates the inner product of `E` on the images of tangent vectors
under the differential of the inclusion. -/
@[simp]
theorem closedBallEuclideanMetric_inner (x : closedBall (0 : E) 1)
    (v w : TangentSpace (𝓡∂ n) x) :
    (closedBallEuclideanMetric (E := E)).inner x v w =
      inner ℝ (mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x v)
        (mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x w) :=
  inducedRiemannianMetric_inner _ _ _ x v w

/-- The closed unit ball is a Riemannian manifold with boundary for its Euclidean metric. -/
instance instRiemannianBundleClosedBall :
    RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ n) x) :=
  ⟨(closedBallEuclideanMetric (E := E)).toRiemannianMetric⟩

/-- The Euclidean metric on the closed unit ball is analytic. -/
instance instIsContMDiffRiemannianBundleClosedBall :
    IsContMDiffRiemannianBundle (𝓡∂ n) ω (EuclideanSpace ℝ (Fin n))
      (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ n) x) :=
  Bundle.instIsContMDiffRiemannianBundle (closedBallEuclideanMetric (E := E))

/-- The Euclidean metric on the closed unit ball is continuous. -/
instance instIsContinuousRiemannianBundleClosedBall :
    IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ n) x) :=
  Bundle.instIsContinuousRiemannianBundle
    (closedBallEuclideanMetric (E := E)).toContinuousRiemannianMetric

/-- The inner product of two tangent vectors of the closed unit ball is the inner product in `E`
of their images under the differential of the inclusion. -/
@[simp]
theorem inner_tangentSpace_closedBall (x : closedBall (0 : E) 1) (v w : TangentSpace (𝓡∂ n) x) :
    inner ℝ v w =
      inner ℝ (mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x v)
        (mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x w) :=
  closedBallEuclideanMetric_inner x v w

/-- The norm of a tangent vector of the closed unit ball is the norm in `E` of its image under the
differential of the inclusion. -/
@[simp]
theorem norm_tangentSpace_closedBall (x : closedBall (0 : E) 1) (v : TangentSpace (𝓡∂ n) x) :
    ‖v‖ = ‖mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_tangentSpace_closedBall]

/-- The differential of the inclusion of the closed unit ball, read in `E`, as a linear isometry
equivalence of each tangent space with `E` for the Euclidean metric. -/
def closedBallTangentIsometry (x : closedBall (0 : E) 1) :
    TangentSpace (𝓡∂ n) x ≃ₗᵢ[ℝ] E where
  toLinearEquiv := (subtypeValClosedBallTangentEquiv (n := n) x).toLinearEquiv
  norm_map' v := by
    rw [norm_tangentSpace_closedBall, mvfderiv_subtypeVal_closedBall,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]

/-- The isometry `TauCeti.closedBallTangentIsometry` is the differential of the inclusion. -/
@[simp]
theorem closedBallTangentIsometry_apply (x : closedBall (0 : E) 1) (v : TangentSpace (𝓡∂ n) x) :
    closedBallTangentIsometry x v =
      mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x v := by
  rw [mvfderiv_subtypeVal_closedBall, ContinuousLinearEquiv.coe_coe, closedBallTangentIsometry,
    LinearIsometryEquiv.coe_mk, ContinuousLinearEquiv.coe_toLinearEquiv]

/-! ### The closed unit ball of `EuclideanSpace ℝ (Fin n)` -/

/-- The closed unit ball of `EuclideanSpace ℝ (Fin n)` is a Riemannian manifold with boundary for
its Euclidean metric. -/
instance instRiemannianBundleClosedBallEuclideanSpace :
    RiemannianBundle (fun x : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
      TangentSpace (𝓡∂ n) x) :=
  have := Fact.mk (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
  instRiemannianBundleClosedBall

/-- The Euclidean metric on the closed unit ball of `EuclideanSpace ℝ (Fin n)` is analytic. -/
instance instIsContMDiffRiemannianBundleClosedBallEuclideanSpace :
    IsContMDiffRiemannianBundle (𝓡∂ n) ω (EuclideanSpace ℝ (Fin n))
      (fun x : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ TangentSpace (𝓡∂ n) x) :=
  have := Fact.mk (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
  instIsContMDiffRiemannianBundleClosedBall

/-- The Euclidean metric on the closed unit ball of `EuclideanSpace ℝ (Fin n)` is continuous. -/
instance instIsContinuousRiemannianBundleClosedBallEuclideanSpace :
    IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ TangentSpace (𝓡∂ n) x) :=
  have := Fact.mk (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
  instIsContinuousRiemannianBundleClosedBall

end TauCeti
