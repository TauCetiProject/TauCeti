/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic

/-!
# Pulled-back metric coefficients on metric-indexed manifolds

For a `C^k` Riemannian metric `g` on a manifold `M`, the pulled-back metric coefficients
(`TauCeti.pullbackMetricCoeff`) of the metric-indexed copy `TauCeti.WithMetric g` along
`WithMetric.toWithMetric g ∘ φ` evaluate `g.inner` on the differentials of `φ` along the standard
Euclidean basis vectors. Consequently, conformal rescaling `g ↦ f • g` scales the pulled-back
coefficient matrix by `f (φ x)`, and on Euclidean space `ℝⁿ` the conformally flat metric
`f • g_eucl` has pulled-back coefficient matrix `f x • 1`.

## Main results

* `TauCeti.pullbackMetricCoeff_toWithMetric_comp`: coordinate pullback coefficients of
  `WithMetric g` along `WithMetric.toWithMetric g ∘ φ`.
* `TauCeti.pullbackMetricCoeff_toWithMetric_rescale_comp`: coordinate pullback coefficients scale
  by `f (φ x)` under conformal rescaling `g.rescale f hf hf_pos`.
* `TauCeti.pullbackMetricCoeff_toWithMetric_rescale`: pulling back `f • g_eucl` along
  `WithMetric.toWithMetric` yields `f x • 1`.

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
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : ContMDiffRiemannianMetric I k E (fun x : M ↦ TangentSpace I x))
    (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff I (WithMetric.toWithMetric g ∘ φ) x =
      Matrix.of fun i j ↦
        g.inner (φ x)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x (EuclideanSpace.basisFun (Fin n) ℝ i))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  ext i j
  rw [pullbackMetricCoeff_apply, Matrix.of_apply, WithMetric.inner_def,
    ← ContMDiffRiemannianMetric.inner_riemannianBundle,
    ← ContMDiffRiemannianMetric.inner_riemannianBundle]
  exact inner_tangentSpace_congr (I := I) (WithMetric.ofWithMetric_toWithMetric g (φ x))
    (WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric_comp φ x _)
    (WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric_comp φ x _)

/-- Conformal rescaling of pulled-back metric coefficients: pulling back `g.rescale f hf hf_pos`
along `WithMetric.toWithMetric _ ∘ φ` scales the pulled-back metric coefficient matrix of `g` by
`f (φ x)`. -/
theorem pullbackMetricCoeff_toWithMetric_rescale_comp {n : ℕ} {k : ℕ∞ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : ContMDiffRiemannianMetric I k E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)
    (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff I (WithMetric.toWithMetric (g.rescale f hf hf_pos) ∘ φ) x =
      f (φ x) • pullbackMetricCoeff I (WithMetric.toWithMetric g ∘ φ) x := by
  ext i j
  rw [pullbackMetricCoeff_toWithMetric_comp, Matrix.smul_apply,
    pullbackMetricCoeff_toWithMetric_comp, Matrix.of_apply, Matrix.of_apply,
    ContMDiffRiemannianMetric.rescale_inner, smul_eq_mul]

/-- Pulling back the conformally rescaled Euclidean metric `f • g_eucl` along
`WithMetric.toWithMetric` yields the scalar multiple `f x • 1` of the identity matrix. -/
@[simp]
theorem pullbackMetricCoeff_toWithMetric_rescale {n : ℕ} {k : ℕ∞ω}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)
    (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (WithMetric.toWithMetric
        (((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE le_top).rescale
          f hf hf_pos))
      x = f x • 1 := by
  rw [← Function.comp_id (WithMetric.toWithMetric _),
    pullbackMetricCoeff_toWithMetric_rescale_comp, id_eq]
  congr 1
  ext i j
  rw [pullbackMetricCoeff_toWithMetric_comp, Matrix.of_apply, id_eq,
    ContMDiffRiemannianMetric.ofLE_inner, ← ContMDiffRiemannianMetric.inner_riemannianBundle,
    ← pullbackMetricCoeff_apply, pullbackMetricCoeff_id]

end TauCeti
