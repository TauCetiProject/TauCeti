/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Coordinates
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic

/-!
# Coordinate pullback metric coefficients on metric-indexed copies

For a Riemannian metric `g` on a manifold `M` modelled on `EuclideanSpace ℝ (Fin n)`, the
coordinate pullback coefficients (`TauCeti.pullbackMetricCoeff`) of the copy `TauCeti.WithMetric g`
along `WithMetric.toWithMetric g ∘ φ` evaluate `g.inner` on the differentials of `φ` along the
standard coordinate basis vectors. Consequently, conformal rescaling `g ↦ f • g` multiplies the
coordinate coefficients by `f (φ x)`, and on Euclidean space `ℝⁿ` the conformally flat metric
`f • g_eucl` has coordinate coefficients `f x * δ_ij`.

## Main results

* `TauCeti.pullbackMetricCoeff_toWithMetric_comp`: coordinate pullback coefficients of
  `WithMetric g` along `WithMetric.toWithMetric g ∘ φ`.
* `TauCeti.pullbackMetricCoeff_toWithMetric_rescale_comp`: coordinate pullback coefficients scale
  by `f (φ x)` under conformal rescaling `g.rescale f hf hf_pos`.
* `TauCeti.pullbackMetricCoeff_toWithMetric_rescale`: pulling back `f • g_eucl` along
  `WithMetric.toWithMetric` yields `f x * δ_ij`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (pullback metrics and conformal changes of metric).
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

/-- Pulling back `WithMetric g` along `WithMetric.toWithMetric g ∘ φ` evaluates `g.inner` on the
differentials of `φ` along the Euclidean coordinate basis vectors. -/
theorem pullbackMetricCoeff_toWithMetric_comp {n : ℕ} {k : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) 1 M]
    (g : ContMDiffRiemannianMetric (𝓡 n) k (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x))
    (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff (WithMetric.toWithMetric g ∘ φ) x i j =
      g.inner (φ x) (mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ i))
        (mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace (𝓡 n) y) := ⟨g.toRiemannianMetric⟩
  rw [pullbackMetricCoeff_def, WithMetric.inner_def,
    ← ContMDiffRiemannianMetric.inner_riemannianBundle,
    ← ContMDiffRiemannianMetric.inner_riemannianBundle]
  exact inner_tangentSpace_congr (I := 𝓡 n) (WithMetric.ofWithMetric_toWithMetric g (φ x))
    (WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric_comp φ x _)
    (WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric_comp φ x _)

/-- Conformal rescaling of pulled-back metric coefficients: pulling back `g.rescale f hf hf_pos`
along `WithMetric.toWithMetric _ ∘ φ` multiplies the pulled-back metric coefficients of `g` by
`f (φ x)`. -/
theorem pullbackMetricCoeff_toWithMetric_rescale_comp {n : ℕ} {k : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) 1 M]
    (g : ContMDiffRiemannianMetric (𝓡 n) k (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)
    (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff (WithMetric.toWithMetric (g.rescale f hf hf_pos) ∘ φ) x i j =
      f (φ x) * pullbackMetricCoeff (WithMetric.toWithMetric g ∘ φ) x i j := by
  rw [pullbackMetricCoeff_toWithMetric_comp, pullbackMetricCoeff_toWithMetric_comp,
    ContMDiffRiemannianMetric.rescale_inner]

/-- Pulling back the conformally rescaled Euclidean metric `f • g_eucl` along
`WithMetric.toWithMetric` yields the conformally flat coefficients `f x * δ_ij`. -/
@[simp]
theorem pullbackMetricCoeff_toWithMetric_rescale {n : ℕ} {k : ℕ∞ω}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff
      (WithMetric.toWithMetric
        (((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE le_top).rescale
          f hf hf_pos))
      x i j = f x * if i = j then 1 else 0 := by
  rw [← Function.comp_id (WithMetric.toWithMetric _),
    pullbackMetricCoeff_toWithMetric_rescale_comp, pullbackMetricCoeff_toWithMetric_comp, id_eq,
    ContMDiffRiemannianMetric.ofLE_inner, ← ContMDiffRiemannianMetric.inner_riemannianBundle,
    ← pullbackMetricCoeff_def, pullbackMetricCoeff_id]

end TauCeti
