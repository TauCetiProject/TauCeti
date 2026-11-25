/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.WithMetric
public import TauCeti.Geometry.Manifold.Riemannian.WarpedProd
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.LocallySymmetric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Homogeneous
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Euclidean
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Prod.Basic
import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Isometry
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Scalar

/-!
# Geometry of warped planes `(ℝ × ℝ, dx² + f(x)² dy²)`

For a smooth nowhere-vanishing warping function `f : ℝ → ℝ`, `TauCeti.warpedPlaneMetric f hf hf₀`
is the warped-product metric `dx² + f(x)² dy²` on `ℝ × ℝ`. Its scalar curvature is
`-2 f''(x) / f(x)`. On `WithMetric (warpedPlaneMetric f hf hf₀)`:

* the underlying space is contractible (hence simply connected);
* whenever `|f|` is bounded away from zero (`0 < c` and `c ≤ |f x|` for all `x`), the metric
  uniformly dominates a positive multiple of the standard complete product metric on `ℝ × ℝ`, and
  is therefore metrically and geodesically complete;
* whenever `f'' / f` is nonconstant, the scalar curvature is nonconstant, so the Levi-Civita
  connection fails to have parallel curvature (`¬ HasParallelCurvature`).

## Main definitions

* `TauCeti.warpedPlaneMetric`: the warped metric `dx² + f(x)² dy²` on `ℝ × ℝ`.

## Main results

* `TauCeti.warpedPlaneMetric_inner` and `TauCeti.warpedPlaneMetric_inner_eq_mul`: formulas for the
  inner product of `warpedPlaneMetric`.
* `TauCeti.scalarCurvature_warpedPlaneMetric`: `Scal = -2 f''(x) / f(x)`.
* `TauCeti.instContractibleSpaceWithMetricWarpedPlane`: `WithMetric (warpedPlaneMetric f hf hf₀)`
  is contractible.
* `TauCeti.isGeodesicallyCompleteAt_withMetric_warpedPlaneMetric`: geodesic completeness when `|f|`
  is bounded away from zero.
* `TauCeti.not_hasParallelCurvature_withMetric_warpedPlaneMetric`: nonconstant `f'' / f` precludes
  parallel curvature.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 3, 6, 7.
* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7, Corollary 43.
-/

public section

open Bundle CovariantDerivative Manifold
open TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold NNReal

noncomputable section

namespace TauCeti

/-- The warped product metric `dx² + f(x)² dy²` on `ℝ × ℝ`, for a smooth nowhere-vanishing
warping function `f : ℝ → ℝ`. -/
def warpedPlaneMetric (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hf₀ : ∀ x, f x ≠ 0) :
    ContMDiffRiemannianMetric (𝓘(ℝ).prod 𝓘(ℝ)) ∞ (ℝ × ℝ)
      (fun p : ℝ × ℝ ↦ TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) p) :=
  ((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).warpedProdTangentSpace
    f hf.contMDiff hf₀ ((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top)

/-- The inner product of `warpedPlaneMetric f hf hf₀` at `p : ℝ × ℝ` pairs horizontal components by
the standard inner product and vertical components by `f(p.1)²` times the standard inner product. -/
@[simp]
theorem warpedPlaneMetric_inner (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hf₀ : ∀ x, f x ≠ 0)
    (p : ℝ × ℝ) (v w : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) p) :
    (warpedPlaneMetric f hf hf₀).inner p v w =
      inner ℝ (tangentSpaceProdEquiv p v).1 (tangentSpaceProdEquiv p w).1 +
        f p.1 ^ 2 * inner ℝ (tangentSpaceProdEquiv p v).2 (tangentSpaceProdEquiv p w).2 := by
  rw [warpedPlaneMetric, ContMDiffRiemannianMetric.warpedProdTangentSpace_inner,
    ContMDiffRiemannianMetric.ofLE_inner, riemannianMetricVectorSpace_inner,
    riemannianMetricVectorSpace_inner, ← inner_tangentSpace_vectorSpace,
    ← inner_tangentSpace_vectorSpace]

/-- Explicit coordinate formula `u₁ w₁ + f(x)² u₂ w₂` for `warpedPlaneMetric`. -/
theorem warpedPlaneMetric_inner_eq_mul (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hf₀ : ∀ x, f x ≠ 0)
    (p : ℝ × ℝ) (v w : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) p) :
    (warpedPlaneMetric f hf hf₀).inner p v w =
      NormedSpace.fromTangentSpace p.1 (tangentSpaceProdEquiv p v).1 *
          NormedSpace.fromTangentSpace p.1 (tangentSpaceProdEquiv p w).1 +
        f p.1 ^ 2 *
          (NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p v).2 *
            NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p w).2) := by
  rw [warpedPlaneMetric_inner, inner_tangentSpace_vectorSpace, inner_tangentSpace_vectorSpace,
    real_inner_eq_re_inner, real_inner_eq_re_inner, RCLike.inner_apply, RCLike.inner_apply]
  simp [mul_comm]

/-- The scalar curvature of `dx² + f(x)² dy²` on `ℝ × ℝ` is `-2 f''(x) / f(x)`. -/
theorem scalarCurvature_warpedPlaneMetric (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hf₀ : ∀ x, f x ≠ 0) (p : ℝ × ℝ) :
    (warpedPlaneMetric f hf hf₀).scalarCurvature p = -2 * deriv (deriv f) p.1 / f p.1 := by
  let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
  have hg : ∀ x : ℝ, g.scalarCurvature x = 0 := fun x ↦ by
    rw [ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvature_leviCivitaConnection g
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _).symm,
      scalarCurvature_leviCivitaConnection_model_space]
  have hgrad : DifferentiableAt ℝ (gradient f) p.1 :=
    (hf.gradient_right (m := 1) (by simp)).differentiable (by simp) p.1
  have hlap :
      (letI : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ) x) :=
        ⟨g.toRiemannianMetric⟩
      laplaceBeltrami 𝓘(ℝ) f p.1) = deriv (deriv f) p.1 := by
    let : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ) x) := ⟨g.toRiemannianMetric⟩
    rw [laplaceBeltrami_eq_laplacian_of_eq
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _) hgrad,
      InnerProductSpace.laplacian_eq_iteratedDeriv_real]
    simp [iteratedDeriv_succ]
  rw [warpedPlaneMetric, ContMDiffRiemannianMetric.scalarCurvature_warpedProdTangentSpace,
    hg p.1, hg p.2, hlap]
  simp only [Module.finrank_self, Nat.cast_one, sub_self, zero_div, add_zero, mul_one]
  ring

/-- `WithMetric (warpedPlaneMetric f hf hf₀)` is contractible (hence simply connected). -/
instance instContractibleSpaceWithMetricWarpedPlane (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hf₀ : ∀ x, f x ≠ 0) :
    ContractibleSpace (WithMetric (warpedPlaneMetric f hf hf₀)) :=
  (WithMetric.homeomorph (warpedPlaneMetric f hf hf₀)).contractibleSpace

/-- If `f : ℝ → ℝ` is bounded away from zero (`0 < c` and `c ≤ |f x|` for all `x`), then
`(ℝ × ℝ, dx² + f(x)² dy²)` is geodesically complete at every point. -/
theorem isGeodesicallyCompleteAt_withMetric_warpedPlaneMetric (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hf₀ : ∀ x, f x ≠ 0) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x, c ≤ |f x|)
    (p : WithMetric (warpedPlaneMetric f hf hf₀)) :
    IsGeodesicallyCompleteAt (𝓘(ℝ).prod 𝓘(ℝ))
      (WithMetric (warpedPlaneMetric f hf hf₀)) p := by
  have : IsContinuousRiemannianBundle (ℝ × ℝ)
      (fun x : ℝ × ℝ ↦ TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := 𝓘(ℝ).prod 𝓘(ℝ)) (n := ∞) (F := ℝ × ℝ)
      (V := fun x : ℝ × ℝ ↦ TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x)
  let g := warpedPlaneMetric f hf hf₀
  let m : EMetricSpace (ℝ × ℝ) := EMetricSpace.ofRiemannianMetric (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × ℝ)
  have : @CompleteSpace (ℝ × ℝ) m.toUniformSpace :=
    completeSpace_ofRiemannianMetric_of_isPretransitive_isom (I := 𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × ℝ)
  let C : ℝ≥0 := max 1 ⟨c⁻¹, inv_nonneg.2 hc.le⟩
  have hC1 : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast le_max_left (1 : ℝ≥0) ⟨c⁻¹, inv_nonneg.2 hc.le⟩
  have hCinv : c⁻¹ ≤ (C : ℝ) := by
    exact_mod_cast le_max_right (1 : ℝ≥0) ⟨c⁻¹, inv_nonneg.2 hc.le⟩
  have hC0 : C ≠ 0 := by
    intro h0
    rw [h0] at hC1
    norm_num at hC1
  have hdom : ∀ x (v : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x),
      ‖v‖ ^ 2 ≤ (C : ℝ) ^ 2 * g.inner x v v := fun x v ↦ by
    rw [← real_inner_self_eq_norm_sq, Manifold.inner_tangentSpace_prod, warpedPlaneMetric_inner]
    set u := tangentSpaceProdEquiv x v
    have h1 : (1 : ℝ) ≤ (C : ℝ) ^ 2 := by nlinarith
    have h2 : (1 : ℝ) ≤ (C : ℝ) ^ 2 * f x.1 ^ 2 := by
      have hcf : 1 ≤ (C : ℝ) * |f x.1| := calc
        (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
        _ ≤ (C : ℝ) * |f x.1| := mul_le_mul hCinv (hbound x.1) hc.le (by positivity)
      have hsq : (1 : ℝ) ^ 2 ≤ ((C : ℝ) * |f x.1|) ^ 2 :=
        pow_le_pow_left₀ zero_le_one hcf 2
      simpa [mul_pow, sq_abs] using hsq
    nlinarith [real_inner_self_nonneg (x := u.1), real_inner_self_nonneg (x := u.2)]
  exact WithMetric.isGeodesicallyCompleteAt_of_sq_norm_le_mul hC0 hdom p

/-- If `f'' / f` is nonconstant, then `(ℝ × ℝ, dx² + f(x)² dy²)` does not have parallel
curvature. -/
theorem not_hasParallelCurvature_withMetric_warpedPlaneMetric (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hf₀ : ∀ x, f x ≠ 0) {x₁ x₂ : ℝ}
    (hne : deriv (deriv f) x₁ / f x₁ ≠ deriv (deriv f) x₂ / f x₂) :
    ¬ (leviCivitaConnection (𝓘(ℝ).prod 𝓘(ℝ))
        (WithMetric (warpedPlaneMetric f hf hf₀))).HasParallelCurvature := by
  intro hpar
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hloc :=
    (hasParallelCurvature_iff_isLocallyConstant_scalarCurvature_of_finrank_eq_two
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod 𝓘(ℝ))) hdim).1 hpar
  let g := warpedPlaneMetric f hf hf₀
  have hscal : ∀ q : WithMetric g,
      (leviCivitaConnection (𝓘(ℝ).prod 𝓘(ℝ)) (WithMetric g)).scalarCurvature q =
        g.scalarCurvature q.ofWithMetric := fun q ↦ by
    let : RiemannianBundle (fun x : ℝ × ℝ ↦ TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x) :=
      ⟨g.toRiemannianMetric⟩
    rw [ContMDiffRiemannianMetric.scalarCurvature_def g q.ofWithMetric,
      ← WithMetric.coe_riemannianIsometry g]
    exact ((WithMetric.riemannianIsometry g).isLocalRiemannianIsometry.scalarCurvature_map q).symm
  have heq := hloc.apply_eq_of_preconnectedSpace
    (WithMetric.toWithMetric g (x₁, 0)) (WithMetric.toWithMetric g (x₂, 0))
  rw [hscal, hscal, WithMetric.ofWithMetric_toWithMetric, WithMetric.ofWithMetric_toWithMetric,
    scalarCurvature_warpedPlaneMetric, scalarCurvature_warpedPlaneMetric] at heq
  apply hne
  rw [mul_div_assoc, mul_div_assoc] at heq
  exact mul_left_cancel₀ (by norm_num) heq

end TauCeti

end
