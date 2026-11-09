/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Horizontal
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Vertical
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Ricci curvature of warped products

For the metric `g_M + f² g_N`, the Ricci tensor has horizontal block
`Ric_M - (dim N / f) Hess f`, zero mixed block, and vertical block
`Ric_N - (f Δf + (dim N - 1) |grad f|²) g_N`.
Here `Δ = div grad`, and all quantities on the right use the original factor metrics.
These contractions turn the horizontal, mixed and vertical curvature formulas into
criteria for Ricci curvature of warped metrics. The formulas allow zero-dimensional
factors and require only that the warping function be nonzero at the point evaluated.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7, Corollary 43.
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
  {f : M → ℝ}

/-- The horizontal Ricci tensor of `g_M + f² g_N` is
`Ric_M - (dim N / f) Hess f`, evaluated on unscaled base vectors. -/
theorem IsWarpedProduct.ricciTensor_horizontal
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (p : M × N) (hp : f p.1 ≠ 0) (u v : TangentSpace I p.1) :
    (leviCivitaConnection (I.prod J) (M × N)).ricciTensor p
        ((tangentSpaceProdEquiv p).symm (u, 0))
        ((tangentSpaceProdEquiv p).symm (v, 0)) =
      (leviCivitaConnection I M).ricciTensor p.1 u v -
        (Module.finrank ℝ F : ℝ) / f p.1 * hessian I f p.1 u v := by
  rw [ricciTensor_eq_sum_factor_basis, ricciTensor_eq_sum_inner _ p.1
    (stdOrthonormalBasis ℝ (TangentSpace I p.1))]
  simp only [h.tangentSpaceProdEquiv_curvatureTensor_horizontal (hf.mdifferentiable (by simp))]
  have hv (w : TangentSpace J p.2) :
      tangentSpaceProdEquiv p ((leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
        ((tangentSpaceProdEquiv p).symm (0, w))
        ((tangentSpaceProdEquiv p).symm (u, 0))
        ((tangentSpaceProdEquiv p).symm (v, 0))) =
        (0, -(hessian I f p.1 u v / f p.1) • w) := by
    rw [curvatureTensor_antisymm, LinearMap.neg_apply, map_neg,
      h.tangentSpaceProdEquiv_curvatureTensor_horizontal_vertical_horizontal hf p hp]
    simp
  simp only [hv, inner_smul_right, (stdOrthonormalBasis ℝ (TangentSpace J p.2)).inner_eq_one,
    mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    TauCeti.finrank_tangentSpace, nsmul_eq_mul]
  ring

/-- The Ricci tensor of a warped product has zero horizontal-vertical block. -/
-- Use this as a rewrite lemma in named tangent-product coordinates; `simp` expands the equivalence.
theorem IsWarpedProduct.ricciTensor_horizontal_vertical
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (p : M × N) (hp : f p.1 ≠ 0) (u : TangentSpace I p.1) (v : TangentSpace J p.2) :
    (leviCivitaConnection (I.prod J) (M × N)).ricciTensor p
        ((tangentSpaceProdEquiv p).symm (u, 0))
        ((tangentSpaceProdEquiv p).symm (0, v)) = 0 := by
  set e := tangentSpaceProdEquiv (I := I) (J := J) p with he
  set cov := leviCivitaConnection (I.prod J) (M × N) with hcov
  have hh (w : TangentSpace I p.1) :
      inner ℝ w (e (cov.curvatureTensor p (e.symm (w, 0))
        (e.symm (u, 0)) (e.symm (0, v)))).1 = 0 := by
    have hc := (isMetricCompatible_leviCivitaConnection (I.prod J)).inner_curvatureTensor_eq_neg
      p (e.symm (w, 0)) (e.symm (u, 0)) (e.symm (0, v)) (e.symm (w, 0))
    rw [h.inner_eq, h.inner_eq] at hc
    simp only [e, ContinuousLinearEquiv.apply_symm_apply,
      h.tangentSpaceProdEquiv_curvatureTensor_horizontal (hf.mdifferentiable (by simp)),
      inner_zero_left, inner_zero_right, mul_zero, add_zero, neg_zero] at hc
    simpa only [e, cov, real_inner_comm] using hc
  have hv (w : TangentSpace J p.2) :
      inner ℝ w (e (cov.curvatureTensor p (e.symm (0, w))
        (e.symm (u, 0)) (e.symm (0, v)))).2 = 0 := by
    have hc := (isMetricCompatible_leviCivitaConnection (I.prod J)).inner_curvatureTensor_swap_pairs
      (torsion_leviCivitaConnection_eq_zero (I.prod J)) p
      (e.symm (0, w)) (e.symm (u, 0)) (e.symm (0, v)) (e.symm (0, w))
    rw [h.inner_eq, h.inner_eq] at hc
    simp only [e, ContinuousLinearEquiv.apply_symm_apply,
      h.tangentSpaceProdEquiv_curvatureTensor_vertical hf p,
      inner_zero_right, inner_zero_left, zero_add, mul_zero, add_zero] at hc
    rw [real_inner_comm] at hc
    simpa only [e, cov] using (mul_eq_zero.mp hc).resolve_left (pow_ne_zero 2 hp)
  rw [ricciTensor_eq_sum_factor_basis]
  simp only [← he, ← hcov, hh, hv, Finset.sum_const_zero, add_zero]

/-- The vertical Ricci tensor of `g_M + f² g_N`, expressed in the original fibre metric.
The Laplace–Beltrami operator on the right has sign `Δ = div grad`. -/
theorem IsWarpedProduct.ricciTensor_vertical
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (p : M × N) (hp : f p.1 ≠ 0) (u v : TangentSpace J p.2) :
    (leviCivitaConnection (I.prod J) (M × N)).ricciTensor p
        ((tangentSpaceProdEquiv p).symm (0, u))
        ((tangentSpaceProdEquiv p).symm (0, v)) =
      (leviCivitaConnection J N).ricciTensor p.2 u v -
        (f p.1 * laplaceBeltrami I f p.1 +
          ((Module.finrank ℝ F : ℝ) - 1) * ‖mgradient I f p.1‖ ^ 2) * inner ℝ u v := by
  set e := tangentSpaceProdEquiv (I := I) (J := J) p with he
  set b := stdOrthonormalBasis ℝ (TangentSpace I p.1) with hb
  set c := stdOrthonormalBasis ℝ (TangentSpace J p.2) with hc
  have hh (w : TangentSpace I p.1) :
      inner ℝ w (e ((leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
        (e.symm (w, 0)) (e.symm (0, u)) (e.symm (0, v)))).1 =
        -f p.1 * hessian I f p.1 w w * inner ℝ u v := by
    have hc := h.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hf p hp w w u v
    rw [h.inner_eq] at hc
    simp only [ContinuousLinearEquiv.apply_symm_apply,
      inner_zero_right, mul_zero, add_zero] at hc
    rw [real_inner_comm] at hc
    exact hc
  rw [ricciTensor_eq_sum_factor_basis, ricciTensor_eq_sum_inner _ p.2 c,
    laplaceBeltrami_eq_sum_hessian I f p.1 b]
  simp only [← he, hh]
  simp only [he, h.tangentSpaceProdEquiv_curvatureTensor_vertical hf p,
    inner_sub_right, inner_smul_right]
  simp only [← hb, ← hc, c.inner_eq_one, mul_one]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, TauCeti.finrank_tangentSpace,
    nsmul_eq_mul]
  have hs : ∑ i, inner ℝ (c i) v * inner ℝ (c i) u = inner ℝ u v := by
    simpa only [real_inner_comm v] using c.sum_inner_mul_inner v u
  rw [hs]
  ring

/-- The vertical-horizontal Ricci block vanishes as well. -/
theorem IsWarpedProduct.ricciTensor_vertical_horizontal
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (p : M × N) (hp : f p.1 ≠ 0) (u : TangentSpace J p.2) (v : TangentSpace I p.1) :
    (leviCivitaConnection (I.prod J) (M × N)).ricciTensor p
        ((tangentSpaceProdEquiv p).symm (0, u))
        ((tangentSpaceProdEquiv p).symm (v, 0)) = 0 := by
  rw [CovariantDerivative.IsMetricCompatible.ricciTensor_comm
    (leviCivitaConnection (I.prod J) (M × N))
    (isMetricCompatible_leviCivitaConnection (I.prod J))
    (torsion_leviCivitaConnection_eq_zero (I.prod J))]
  exact h.ricciTensor_horizontal_vertical hf p hp v u

/-- The full Ricci transformation law for a warped metric, on arbitrary tangent vectors.
The horizontal and vertical entries are read using the canonical tangent-product equivalence. -/
theorem IsWarpedProduct.ricciTensor_eq
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (p : M × N) (hp : f p.1 ≠ 0) (u v : TangentSpace (I.prod J) p) :
    (leviCivitaConnection (I.prod J) (M × N)).ricciTensor p u v =
      (leviCivitaConnection I M).ricciTensor p.1
          (tangentSpaceProdEquiv p u).1 (tangentSpaceProdEquiv p v).1 -
        (Module.finrank ℝ F : ℝ) / f p.1 *
          hessian I f p.1 (tangentSpaceProdEquiv p u).1 (tangentSpaceProdEquiv p v).1 +
      (leviCivitaConnection J N).ricciTensor p.2
          (tangentSpaceProdEquiv p u).2 (tangentSpaceProdEquiv p v).2 -
        (f p.1 * laplaceBeltrami I f p.1 +
          ((Module.finrank ℝ F : ℝ) - 1) * ‖mgradient I f p.1‖ ^ 2) *
          inner ℝ (tangentSpaceProdEquiv p u).2 (tangentSpaceProdEquiv p v).2 := by
  let e := tangentSpaceProdEquiv (I := I) (J := J) p
  have hsplit (w : TangentSpace (I.prod J) p) :
      w = e.symm ((e w).1, 0) + e.symm (0, (e w).2) := by
    rw [← map_add]
    simp
  conv_lhs => rw [hsplit u, hsplit v]
  simp only [map_add, LinearMap.add_apply, e,
    h.ricciTensor_horizontal hf p hp, h.ricciTensor_vertical hf p hp,
    h.ricciTensor_horizontal_vertical hf p hp, h.ricciTensor_vertical_horizontal hf p hp,
    add_zero, zero_add]
  ring

end TauCeti.Manifold
