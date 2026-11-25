/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Induced
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Basic

/-!
# The Euclidean metric on the closed half-space

The closed half-space `EuclideanHalfSpace n = {x : ℝⁿ | 0 ≤ x 0}` is a manifold with boundary
modelled on itself through `𝓡∂ n`, and the differential of its inclusion into
`EuclideanSpace ℝ (Fin n)` is the identity at every point, including the points of the boundary
hyperplane (`TauCeti.mfderiv_subtypeVal_euclideanHalfSpace`). Its *Euclidean metric*
`TauCeti.euclideanHalfSpaceMetric` is the metric induced by the inclusion, installed as the
`RiemannianBundle` instance on its tangent bundle.

The inclusion is then a local Riemannian isometry into `EuclideanSpace ℝ (Fin n)` with its flat
metric (`TauCeti.isLocalRiemannianIsometry_subtypeVal_euclideanHalfSpace`), so the Hessian of the
restriction of a `C²` function is its second Fréchet derivative at every point, boundary included
(`TauCeti.hessian_comp_subtypeVal_euclideanHalfSpace`). In particular the normal coordinate `x⁰` is
affine with vanishing Hessian, and the second fundamental form of the boundary hyperplane is zero
(`TauCeti.boundarySecondFundamentalForm_euclideanHalfSpace`).

## Main declarations

* `TauCeti.euclideanHalfSpaceMetric`: the analytic Euclidean metric on the closed half-space, with
  the instances `TauCeti.instRiemannianBundleEuclideanHalfSpace` and
  `TauCeti.instIsContMDiffRiemannianBundleEuclideanHalfSpace`.
* `TauCeti.inner_tangentSpace_euclideanHalfSpace`: the inner product of two tangent vectors is
  their inner product in `EuclideanSpace ℝ (Fin n)`.
* `TauCeti.hessian_comp_subtypeVal_euclideanHalfSpace`: the Hessian of the restriction of a
  function is its second Fréchet derivative.
* `TauCeti.outwardUnitNormal_euclideanHalfSpace`: the outward unit normal is `-e₀`.
* `TauCeti.boundarySecondFundamentalForm_euclideanHalfSpace`: the boundary hyperplane of the
  Euclidean half-space has `II = 0`.
-/

public section

open Bundle Function Set TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace Gradient

noncomputable section

namespace TauCeti

variable {n : ℕ} [NeZero n]

/-- The differential of the inclusion of the closed half-space into `EuclideanSpace ℝ (Fin n)` is
the identity at every point, including the points of the boundary hyperplane. -/
theorem mfderiv_subtypeVal_euclideanHalfSpace (x : EuclideanHalfSpace n) :
    mfderiv (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (𝓡∂ n) x =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  have hdiff : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (𝓡∂ n) x :=
    ((𝓡∂ n).contMDiff (n := 1)).mdifferentiableAt one_ne_zero
  have heq : EqOn (writtenInExtChartAt (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x
      (𝓡∂ n)) id (range (𝓡∂ n)) :=
    fun y hy ↦ (𝓡∂ n).right_inv hy
  have hx : extChartAt (𝓡∂ n) x x ∈ range (𝓡∂ n) := mem_range_self _
  rw [hdiff.mfderiv, ((hasFDerivWithinAt_id _ _).congr heq (heq hx)).fderivWithin
    ((𝓡∂ n).uniqueDiffOn _ hx)]
  rfl

/-- The differential of the inclusion of the closed half-space, read in
`EuclideanSpace ℝ (Fin n)`, is the identity. -/
theorem mvfderiv_subtypeVal_euclideanHalfSpace (x : EuclideanHalfSpace n)
    (v : TangentSpace (𝓡∂ n) x) :
    mvfderiv (𝓡∂ n) (𝓡∂ n) x v = v := by
  change NormedSpace.fromTangentSpace _
    (mfderiv (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ n) x v) = v
  rw [mfderiv_subtypeVal_euclideanHalfSpace]
  rfl

/-- The **Euclidean metric** on the closed half-space: the analytic Riemannian metric induced by
the inclusion into `EuclideanSpace ℝ (Fin n)`. -/
def euclideanHalfSpaceMetric :
    ContMDiffRiemannianMetric (𝓡∂ n) ω (EuclideanSpace ℝ (Fin n))
      (fun x : EuclideanHalfSpace n ↦ TangentSpace (𝓡∂ n) x) :=
  inducedRiemannianMetric (n := ω)
    (𝓡∂ n) (𝓡∂ n).contMDiff
    fun x v w h ↦ by
      rwa [mvfderiv_subtypeVal_euclideanHalfSpace, mvfderiv_subtypeVal_euclideanHalfSpace] at h

/-- The closed half-space is a Riemannian manifold with boundary for its Euclidean metric. -/
instance instRiemannianBundleEuclideanHalfSpace :
    RiemannianBundle (fun x : EuclideanHalfSpace n ↦ TangentSpace (𝓡∂ n) x) :=
  ⟨(euclideanHalfSpaceMetric (n := n)).toRiemannianMetric⟩

/-- The Euclidean metric on the closed half-space is analytic. -/
instance instIsContMDiffRiemannianBundleEuclideanHalfSpace :
    IsContMDiffRiemannianBundle (𝓡∂ n) ω (EuclideanSpace ℝ (Fin n))
      (fun x : EuclideanHalfSpace n ↦ TangentSpace (𝓡∂ n) x) :=
  Bundle.instIsContMDiffRiemannianBundle (euclideanHalfSpaceMetric (n := n))

/-- The Euclidean metric on the closed half-space evaluates the inner product of
`EuclideanSpace ℝ (Fin n)` on the images of tangent vectors under the differential of the
inclusion. -/
theorem euclideanHalfSpaceMetric_inner (x : EuclideanHalfSpace n) (v w : TangentSpace (𝓡∂ n) x) :
    (euclideanHalfSpaceMetric (n := n)).inner x v w =
      ⟪mvfderiv (𝓡∂ n) (𝓡∂ n) x v, mvfderiv (𝓡∂ n) (𝓡∂ n) x w⟫ :=
  inducedRiemannianMetric_inner _ _ _ x v w

/-- The inner product of two tangent vectors of the closed half-space is their inner product in
`EuclideanSpace ℝ (Fin n)`. -/
theorem inner_tangentSpace_euclideanHalfSpace (x : EuclideanHalfSpace n)
    (v w : TangentSpace (𝓡∂ n) x) :
    ⟪v, w⟫ = @inner ℝ (EuclideanSpace ℝ (Fin n)) _ v w := by
  rw [show ⟪v, w⟫ = (euclideanHalfSpaceMetric (n := n)).inner x v w from rfl,
    euclideanHalfSpaceMetric_inner, mvfderiv_subtypeVal_euclideanHalfSpace,
    mvfderiv_subtypeVal_euclideanHalfSpace]

/-- The norm of a tangent vector of the closed half-space is its norm in
`EuclideanSpace ℝ (Fin n)`. -/
theorem norm_tangentSpace_euclideanHalfSpace (x : EuclideanHalfSpace n)
    (v : TangentSpace (𝓡∂ n) x) :
    ‖v‖ = @norm (EuclideanSpace ℝ (Fin n)) _ v := by
  rw [norm_eq_sqrt_real_inner v, inner_tangentSpace_euclideanHalfSpace]
  exact (@norm_eq_sqrt_real_inner (EuclideanSpace ℝ (Fin n)) _ _ v).symm

/-- The inclusion of the closed half-space, with its Euclidean metric, into
`EuclideanSpace ℝ (Fin n)`, with its flat metric, is a local Riemannian isometry. -/
theorem isLocalRiemannianIsometry_subtypeVal_euclideanHalfSpace :
    IsLocalRiemannianIsometry (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (𝓡∂ n) where
  contMDiff := (𝓡∂ n).contMDiff
  isInvertible_mfderiv x := by
    rw [mfderiv_subtypeVal_euclideanHalfSpace]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  inner_mfderiv x v w := by
    rw [inner_tangentSpace_vectorSpace, mfderiv_subtypeVal_euclideanHalfSpace]
    exact (inner_tangentSpace_euclideanHalfSpace x v w).symm

/-- **The Hessian on the closed half-space.** For a function `f`, `C²` at a point `x` of the closed
half-space, the Hessian of its restriction for the Euclidean metric is the second Fréchet
derivative of `f` at `x`. This holds at the points of the boundary hyperplane as well. -/
theorem hessian_comp_subtypeVal_euclideanHalfSpace {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanHalfSpace n} (hf : ContDiffAt ℝ 2 f ((𝓡∂ n) x)) (u w : TangentSpace (𝓡∂ n) x) :
    hessian (𝓡∂ n) (f ∘ (𝓡∂ n)) x u w = fderiv ℝ (fderiv ℝ f) ((𝓡∂ n) x) u w := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) ((𝓡∂ n) x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hgrad : DifferentiableAt ℝ (∇ f) ((𝓡∂ n) x) :=
    (InnerProductSpace.toDual ℝ _).symm.differentiableAt.comp _ hD
  rw [isLocalRiemannianIsometry_subtypeVal_euclideanHalfSpace.hessian_comp
    (contMDiffAt_iff_contDiffAt.2 hf), hessian_eq_iteratedFDeriv_model_space hgrad,
    iteratedFDeriv_two_apply, mfderiv_subtypeVal_euclideanHalfSpace]
  rfl

/-- The outward unit normal of the Euclidean half-space `{x⁰ ≥ 0}` at every point of its boundary
hyperplane is `-e₀`. -/
theorem outwardUnitNormal_euclideanHalfSpace {n : ℕ}
    (q : (𝓡∂ (n + 1)).boundary (EuclideanHalfSpace (n + 1))) :
    outwardUnitNormal q = -EuclideanSpace.single 0 1 := by
  refine (eq_outwardUnitNormal_iff.2
    ⟨?_, isOutwardPointing_iff.2 ⟨q.property, ?_⟩, fun w ↦ ?_⟩).symm
  · exact (norm_tangentSpace_euclideanHalfSpace _ _).trans (by simp)
  · rw [show ⇑(extChartAt (𝓡∂ (n + 1)) (q : EuclideanHalfSpace (n + 1))) = 𝓡∂ (n + 1) from rfl,
      mfderiv_subtypeVal_euclideanHalfSpace]
    change (-EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) 0 < 0
    simp
  · refine (inner_tangentSpace_euclideanHalfSpace _ _ _).trans ?_
    have h := DFunLike.congr_fun (mfderiv_subtypeVal_boundary q) w
    have h0 (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v = euclideanHalfSpaceBoundaryParam n w) :
        @inner ℝ (EuclideanSpace ℝ (Fin (n + 1))) _ (-EuclideanSpace.single 0 1) v = 0 := by
      simp only [hv, inner_neg_left, EuclideanSpace.inner_single_left, map_one, one_mul,
        neg_eq_zero]
      exact euclideanHalfSpaceBoundaryParam_apply_zero (n := n) w
    exact h0 _ h

/-- **The boundary hyperplane of the Euclidean half-space is totally geodesic.** For the Euclidean
metric on the closed half-space, the normal coordinate `x⁰` is affine, so its Hessian vanishes and
the second fundamental form of the boundary is zero. -/
theorem boundarySecondFundamentalForm_euclideanHalfSpace {n : ℕ}
    (q : (𝓡∂ (n + 1)).boundary (EuclideanHalfSpace (n + 1)))
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    boundarySecondFundamentalForm q u w = 0 := by
  -- The preferred chart of the model space is the identity, so `-x⁰` is a linear function.
  let ℓ : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ := -EuclideanSpace.proj 0
  have hφ : (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1))
      (q : EuclideanHalfSpace (n + 1)) y).val 0) = ℓ ∘ (𝓡∂ (n + 1)) := rfl
  have h2 : fderiv ℝ (fderiv ℝ ℓ) = 0 := by
    rw [show fderiv ℝ ℓ = fun _ ↦ ℓ from funext fun _ ↦ ℓ.fderiv]
    exact funext fun _ ↦ fderiv_const_apply ℓ
  rw [boundarySecondFundamentalForm_apply, hφ, hessian_comp_subtypeVal_euclideanHalfSpace
    ℓ.contDiff.contDiffAt, h2]
  exact mul_eq_zero_of_right _ rfl

end TauCeti
