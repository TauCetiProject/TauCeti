/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Restriction.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Hessian.OneDimensional
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Radial calculus on open subsets of the real line

For the restriction of the standard Euclidean metric to any open subset of `ℝ`,
the scalar Hessian multiplies coordinates by the second derivative, the
Laplace–Beltrami operator is the second derivative, and the squared gradient
norm is the square of the first derivative. Only pointwise regularity is needed.
These identities supply the radial terms in warped-product curvature formulas.

## Main results

* `TauCeti.Manifold.laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv`: the
  Laplace–Beltrami operator on an open subset of `ℝ` is `deriv (deriv f)`.
* `TauCeti.Manifold.inner_restrictOpenTangentSpace_real`: the restricted Euclidean inner product on
  an open subset of `ℝ` multiplies model-space tangent coordinates.
* `TauCeti.Manifold.hessian_restrictOpenTangentSpace_real_eq_mul_deriv_deriv`: the scalar Hessian
  multiplies model-space tangent coordinates by `deriv (deriv f)`.
* `TauCeti.Manifold.sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv`: the squared
  Riemannian gradient norm is `deriv f ^ 2`.
-/

public noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.Manifold

/-- The Laplace–Beltrami operator of the restricted Euclidean metric on an open
subset of `ℝ` is the ordinary second derivative. -/
theorem laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv
    (U : Opens ℝ) {f : ℝ → ℝ} {x : U} (hf : ContDiffAt ℝ 2 f (x : ℝ)) :
    let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
    let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
      ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
    laplaceBeltrami 𝓘(ℝ) (fun r : U ↦ f r) x = deriv (deriv f) x := by
  dsimp only
  rw [laplaceBeltrami_restrictOpenTangentSpace_eq_laplacian U hf,
    InnerProductSpace.laplacian_eq_iteratedDeriv_real]
  simp [iteratedDeriv_succ]

/-- The restricted Euclidean inner product on an open subset of `ℝ` is the product
of the model-space tangent coordinates. -/
theorem inner_restrictOpenTangentSpace_real
    (U : Opens ℝ) (x : U) (v w : TangentSpace 𝓘(ℝ) x) :
    (((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U).inner
        x v w =
      tangentSpaceCastModel 𝓘(ℝ) x v * tangentSpaceCastModel 𝓘(ℝ) x w := by
  have hcast (u : TangentSpace 𝓘(ℝ) x) :
      NormedSpace.fromTangentSpace (x : ℝ) (tangentSpaceOpenEquiv x u) =
        tangentSpaceCastModel 𝓘(ℝ) x u := by
    rw [tangentSpaceOpenEquiv_apply]
    -- `NormedSpace.fromTangentSpace` on `ℝ` and `tangentSpaceCastModel 𝓘(ℝ)` are both the identity
    -- equivalence on `ℝ`.
    rfl
  rw [ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner,
    ContMDiffRiemannianMetric.ofLE_inner,
    ← ContMDiffRiemannianMetric.inner_riemannianBundle (riemannianMetricVectorSpace ℝ),
    inner_tangentSpace_vectorSpace, hcast, hcast]
  simp [mul_comm]

/-- The scalar Hessian for the restricted Euclidean metric on an open subset of
`ℝ` is the product of the tangent coordinates times the ordinary second derivative. -/
theorem hessian_restrictOpenTangentSpace_real_eq_mul_deriv_deriv
    (U : Opens ℝ) {f : ℝ → ℝ} {x : U} (hf : ContDiffAt ℝ 2 f (x : ℝ))
    (v w : TangentSpace 𝓘(ℝ) x) :
    let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
    let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
      ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
    hessian 𝓘(ℝ) (fun r : U ↦ f r) x v w =
      tangentSpaceCastModel 𝓘(ℝ) x v * tangentSpaceCastModel 𝓘(ℝ) x w * deriv (deriv f) x := by
  dsimp only
  let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
  let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
    ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
  let _ := Bundle.instIsContMDiffRiemannianBundle (g.restrictOpenTangentSpace U)
  have hin : inner ℝ v w = tangentSpaceCastModel 𝓘(ℝ) x v * tangentSpaceCastModel 𝓘(ℝ) x w :=
    inner_restrictOpenTangentSpace_real U x v w
  rw [hessian_eq_laplaceBeltrami_mul_inner_of_finrank_le_one (by simp),
    laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv U hf, hin]
  ring

/-- The squared gradient norm for the restricted Euclidean metric on an open
subset of `ℝ` is the square of the ordinary derivative. -/
theorem sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv
    (U : Opens ℝ) {f : ℝ → ℝ} {x : U} (hf : DifferentiableAt ℝ f (x : ℝ)) :
    let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
    let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
      ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
    ‖mgradient 𝓘(ℝ) (fun r : U ↦ f r) x‖ ^ 2 = deriv f x ^ 2 := by
  dsimp only
  rw [norm_mgradient_restrictOpenTangentSpace_eq_norm_gradient U hf,
    gradient_eq_deriv', Real.norm_eq_abs, sq_abs]

end TauCeti.Manifold
