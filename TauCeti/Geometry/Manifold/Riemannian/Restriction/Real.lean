/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Restriction.NormedSpace
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
  have h := ((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace_inner
    U x v w
  rw [ContMDiffRiemannianMetric.ofLE_inner, tangentSpaceOpenEquiv_apply,
    tangentSpaceOpenEquiv_apply] at h
  exact h.trans <| by
    change inner ℝ (tangentSpaceCastModel 𝓘(ℝ) x v) (tangentSpaceCastModel 𝓘(ℝ) x w) = _
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
  let e₁ : TangentSpace 𝓘(ℝ) x := (tangentSpaceCastModel 𝓘(ℝ) x).symm 1
  have hu (u : TangentSpace 𝓘(ℝ) x) : u = tangentSpaceCastModel 𝓘(ℝ) x u • e₁ :=
    (tangentSpaceCastModel 𝓘(ℝ) x).injective (by simp [e₁])
  have he₁ : inner ℝ e₁ e₁ = (1 : ℝ) := by
    change (g.restrictOpenTangentSpace U).inner x e₁ e₁ = 1
    rw [inner_restrictOpenTangentSpace_real]
    simp [e₁]
  let b := stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ) x)
  have h1 : hessian 𝓘(ℝ) (fun r : U ↦ f r) x e₁ e₁ = deriv (deriv f) x := by
    have hlap := laplaceBeltrami_eq_sum_hessian 𝓘(ℝ) (fun r : U ↦ f r) x b
    have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ) x))) = 1 := by
      rw [Fintype.card_fin, (tangentSpaceCastModel 𝓘(ℝ) x).toLinearEquiv.finrank_eq,
        Module.finrank_self]
    have hsum : (∑ i, hessian 𝓘(ℝ) (fun r : U ↦ f r) x (b i) (b i)) =
        ∑ _i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ) x)),
          hessian 𝓘(ℝ) (fun r : U ↦ f r) x e₁ e₁ :=
      Finset.sum_congr rfl fun i _ ↦ by
        have hi := b.inner_eq_one i
        rw [hu (b i), real_inner_smul_left, real_inner_smul_right, he₁, mul_one] at hi
        rw [hu (b i), hessian_smul_left, hessian_smul_right, ← mul_assoc, hi, one_mul]
    rw [hsum, Finset.sum_const, Finset.card_univ, hcard, one_smul,
      laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv U hf] at hlap
    exact hlap.symm
  conv_lhs => rw [hu v, hu w]
  rw [hessian_smul_left, hessian_smul_right, h1]
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
