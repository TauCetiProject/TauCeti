/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Horizontal
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Vertical
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Scalar curvature of warped products

For the metric `g_M + f² g_N`, with `n = dim N`, scalar curvature is

`Scal_M + Scal_N / f² - 2n Δf / f - n(n-1)|grad f|² / f²`.

Here `Δ` is the native Laplace–Beltrami operator `div grad`, and the fibre scalar
curvature and gradient use the original factor metrics. The formula follows by
contracting the horizontal, mixed and vertical curvature identities in a warped
orthonormal basis. It includes zero-dimensional factors and requires only that
`f` be nonzero at the point evaluated, rather than positive everywhere.

## Main results

* `TauCeti.Manifold.IsWarpedProduct.scalarCurvature`: the formula for an installed warped metric.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_warpedProdTangentSpace`: the formula for the
  warped-product construction on smooth metrics.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7,
  Proposition 42 and Corollary 43 (warped-product curvature and its contractions).
-/

public section

noncomputable section

open Bundle CovariantDerivative Manifold
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p)]
  [IsContMDiffRiemannianBundle (I.prod J) ∞ (E × F)
    (fun p : M × N ↦ TangentSpace (I.prod J) p)]
  {f : M → ℝ} (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
  (p : M × N) (hf₀ : f p.1 ≠ 0)
  {ι κ : Type*} [Fintype ι] [Fintype κ]
  (b : OrthonormalBasis ι ℝ (TangentSpace I p.1))
  (c : OrthonormalBasis κ ℝ (TangentSpace J p.2))

include h hf

/-- The horizontal block of the scalar contraction is the base scalar curvature. -/
private theorem IsWarpedProduct.sum_horizontal_curvature :
    (∑ j, ∑ k, ⟪(leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
      ((tangentSpaceProdEquiv p).symm (b k, 0))
      ((tangentSpaceProdEquiv p).symm (b j, 0))
      ((tangentSpaceProdEquiv p).symm (b j, 0)),
      (tangentSpaceProdEquiv p).symm (b k, 0)⟫_ℝ) =
      (leviCivitaConnection I M).scalarCurvature p.1 := by
  rw [scalarCurvature_eq_sum_inner_curvatureTensor _ _ b]
  simp only [real_inner_comm, h.inner_eq,
    h.tangentSpaceProdEquiv_curvatureTensor_horizontal (hf.mdifferentiable (by simp)),
    ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, mul_zero, add_zero]

include hf₀

/-- One mixed block contributes minus `dim N` times the normalized base Hessian trace. -/
private theorem IsWarpedProduct.sum_mixed_curvature :
    (∑ j, ∑ k, ⟪(leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
      ((tangentSpaceProdEquiv p).symm (b k, 0))
      ((tangentSpaceProdEquiv p).symm (0, (f p.1)⁻¹ • c j))
      ((tangentSpaceProdEquiv p).symm (0, (f p.1)⁻¹ • c j)),
      (tangentSpaceProdEquiv p).symm (b k, 0)⟫_ℝ) =
      -(Fintype.card κ : ℝ) * laplaceBeltrami I f p.1 / f p.1 := by
  simp only [h.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hf p,
    real_inner_smul_left, real_inner_smul_right, c.inner_eq_one, mul_one]
  have hterm (k : ι) :
      -f p.1 * hessian I f p.1 (b k) (b k) * ((f p.1)⁻¹ * (f p.1)⁻¹) =
        -hessian I f p.1 (b k) (b k) / f p.1 := by field_simp
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_neg_distrib, ← laplaceBeltrami_eq_sum_hessian I f p.1 b]
  simp [div_eq_mul_inv, mul_assoc]

/-- The vertical block contracts fibre curvature and its gradient correction. -/
private theorem IsWarpedProduct.sum_vertical_curvature :
    (∑ j, ∑ k, ⟪(leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
      ((tangentSpaceProdEquiv p).symm (0, (f p.1)⁻¹ • c k))
      ((tangentSpaceProdEquiv p).symm (0, (f p.1)⁻¹ • c j))
      ((tangentSpaceProdEquiv p).symm (0, (f p.1)⁻¹ • c j)),
      (tangentSpaceProdEquiv p).symm (0, (f p.1)⁻¹ • c k)⟫_ℝ) =
      (leviCivitaConnection J N).scalarCurvature p.2 / f p.1 ^ 2 -
        (Fintype.card κ : ℝ) * (Fintype.card κ - 1) * ‖mgradient I f p.1‖ ^ 2 /
          f p.1 ^ 2 := by
  classical
  have hterm (j k : κ) :
      ⟪(leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
        ((tangentSpaceProdEquiv p).symm (0, (f p.1)⁻¹ • c k))
        ((tangentSpaceProdEquiv p).symm (0, (f p.1)⁻¹ • c j))
        ((tangentSpaceProdEquiv p).symm (0, (f p.1)⁻¹ • c j)),
        (tangentSpaceProdEquiv p).symm (0, (f p.1)⁻¹ • c k)⟫_ℝ =
      (⟪(leviCivitaConnection J N).curvatureTensor p.2 (c k) (c j) (c j), c k⟫_ℝ -
        ‖mgradient I f p.1‖ ^ 2 * (1 - if k = j then 1 else 0)) / f p.1 ^ 2 := by
    rw [h.inner_eq, h.tangentSpaceProdEquiv_curvatureTensor_vertical hf p]
    simp only [ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, zero_add,
      inner_sub_left, map_smul, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
      c.inner_eq_one]
    rw [c.inner_eq_ite k j, c.inner_eq_ite j k]
    split_ifs with hkj <;> simp_all; field_simp
  have hscal : (∑ j, ∑ k,
      ⟪(leviCivitaConnection J N).curvatureTensor p.2 (c k) (c j) (c j), c k⟫_ℝ) =
        (leviCivitaConnection J N).scalarCurvature p.2 := by
    simpa only [real_inner_comm] using
      (scalarCurvature_eq_sum_inner_curvatureTensor (leviCivitaConnection J N) p.2 c).symm
  simp_rw [hterm, sub_div, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [hscal]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp
  ring

/-- Scalar curvature of `g_M + f² g_N`, with `Δ = div grad` on the base and the
original fibre scalar curvature. The dimension coefficients are real, so the formula
also includes zero-dimensional fibres. -/
theorem IsWarpedProduct.scalarCurvature :
    (leviCivitaConnection (I.prod J) (M × N)).scalarCurvature p =
      (leviCivitaConnection I M).scalarCurvature p.1 +
        (leviCivitaConnection J N).scalarCurvature p.2 / f p.1 ^ 2 -
        2 * (Module.finrank ℝ F : ℝ) * laplaceBeltrami I f p.1 / f p.1 -
        (Module.finrank ℝ F : ℝ) * (Module.finrank ℝ F - 1) *
          ‖mgradient I f p.1‖ ^ 2 / f p.1 ^ 2 := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I p.1)
  let c := stdOrthonormalBasis ℝ (TangentSpace J p.2)
  let e := h.tangentSpaceProdLinearIsometryEquiv p hf₀
  let B := (b.prod c).map e.symm
  have hB₁ (i) : B (Sum.inl i) = (tangentSpaceProdEquiv p).symm (b i, 0) := by
    simp only [B, e, OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply,
      Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply,
      IsWarpedProduct.tangentSpaceProdLinearIsometryEquiv_symm_apply, smul_zero]
  have hB₂ (j) : B (Sum.inr j) =
      (tangentSpaceProdEquiv p).symm (0, (f p.1)⁻¹ • c j) := by
    simp only [B, e, OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply,
      Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply,
      IsWarpedProduct.tangentSpaceProdLinearIsometryEquiv_symm_apply]
  rw [scalarCurvature_eq_sum_inner_curvatureTensor _ p B]
  conv_lhs =>
    arg 2
    ext j
    arg 2
    ext k
    rw [real_inner_comm]
  simp only [Fintype.sum_sum_type, hB₁, hB₂, Finset.sum_add_distrib]
  rw [h.sum_horizontal_curvature hf p b, h.sum_mixed_curvature hf p hf₀ b c,
    h.sum_vertical_curvature hf p hf₀ c]
  have hswap := IsMetricCompatible.inner_curvatureTensor_swap_pairs
    (isMetricCompatible_leviCivitaConnection (I.prod J) (M := M × N))
    (torsion_leviCivitaConnection_eq_zero (I.prod J)) p
  rw [Finset.sum_comm]
  conv_lhs =>
    pattern (∑ _, ∑ _, _)
    arg 2
    ext j
    arg 2
    ext k
    rw [hswap]
  rw [h.sum_mixed_curvature hf p hf₀ b c]
  simp only [Fintype.card_fin, TauCeti.finrank_tangentSpace]
  ring

end TauCeti.Manifold

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

/-- Scalar curvature of the warped product constructed from two smooth metrics.
The Laplacian and gradient are taken with respect to the base metric `g₁`, with
`Δ = div grad`. No positivity assumption on the nowhere-zero warping function is needed. -/
theorem scalarCurvature_warpedProdTangentSpace
    (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, f x ≠ 0)
    (g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) (p : M × N) :
    let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
    (g₁.warpedProdTangentSpace f hf hf₀ g₂).scalarCurvature p =
      g₁.scalarCurvature p.1 + g₂.scalarCurvature p.2 / f p.1 ^ 2 -
        2 * (Module.finrank ℝ F : ℝ) * laplaceBeltrami I f p.1 / f p.1 -
        (Module.finrank ℝ F : ℝ) * (Module.finrank ℝ F - 1) *
          ‖mgradient I f p.1‖ ^ 2 / f p.1 ^ 2 := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  let : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g₂.toRiemannianMetric⟩
  let : RiemannianBundle (fun q : M × N ↦ TangentSpace (I.prod J) q) :=
    ⟨(g₁.warpedProdTangentSpace f hf hf₀ g₂).toRiemannianMetric⟩
  have h : TauCeti.Manifold.IsWarpedProduct I J N f :=
    TauCeti.Manifold.isWarpedProduct_of_eq hf₀ (warpedProdTangentSpace_toRiemannianMetric ..)
  rw [scalarCurvature_def, scalarCurvature_def, scalarCurvature_def]
  exact h.scalarCurvature hf p (hf₀ p.1)

end Bundle.ContMDiffRiemannianMetric
