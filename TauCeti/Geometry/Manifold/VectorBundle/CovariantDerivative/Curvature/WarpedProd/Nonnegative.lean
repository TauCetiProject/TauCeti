/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hessian.OneDimensional
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Vertical
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi

/-!
# Nonnegative sectional curvature of warped products over a curve

For a positive warping function over a one-dimensional base, concavity and a lower
bound on the fibre curvature give nonnegative sectional curvature of the warped metric.
The criterion controls every tangent plane, including planes neither vertical nor mixed.
It uses the native Levi-Civita connection and includes dependent pairs, whose totalized
sectional curvature is zero.

The curvature formulas follow B. O'Neill, *Semi-Riemannian Geometry* (1983),
Chapter 7, Proposition 42. They apply in particular to rotationally symmetric caps.
-/

public noncomputable section

open Bundle CovariantDerivative
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

/-- The curvature numerator for one arbitrary vector and one vertical vector. The
horizontal and vertical contributions have no cross term. Fibre inner products and
curvature on the right are computed in the unscaled fibre metric. -/
theorem IsWarpedProduct.inner_curvatureTensor_vertical_right
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (p : M × N) (u : TangentSpace I p.1)
    (v w : TangentSpace J p.2) :
    inner ℝ ((leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
      ((tangentSpaceProdEquiv p).symm (u, v))
      ((tangentSpaceProdEquiv p).symm (0, w))
      ((tangentSpaceProdEquiv p).symm (0, w)))
      ((tangentSpaceProdEquiv p).symm (u, v)) =
    -f p.1 * hessian I f p.1 u u * ‖w‖ ^ 2 + f p.1 ^ 2 *
      (inner ℝ ((leviCivitaConnection J N).curvatureTensor p.2 v w w) v -
        ‖mgradient I f p.1‖ ^ 2 * (Matrix.gram ℝ ![v, w]).det) := by
  let e := tangentSpaceProdEquiv (I := I) (J := J) p
  let R := (leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
  have hsplit : e.symm (u, v) = e.symm (u, 0) + e.symm (0, v) := by
    rw [← map_add]
    simp
  have hcross : inner ℝ (R (e.symm (u, 0)) (e.symm (0, w)) (e.symm (0, w)))
      (e.symm (0, v)) = 0 := by
    rw [IsMetricCompatible.inner_curvatureTensor_swap_pairs
      (isMetricCompatible_leviCivitaConnection (I.prod J))
      (torsion_leviCivitaConnection_eq_zero (I.prod J))]
    rw [(isMetricCompatible_leviCivitaConnection (I.prod J)).inner_curvatureTensor_eq_neg,
      real_inner_comm, h.inner_eq, h.tangentSpaceProdEquiv_curvatureTensor_vertical hf p]
    simp only [e, ContinuousLinearEquiv.apply_symm_apply, inner_zero_left,
      inner_zero_right, mul_zero, add_zero, neg_zero]
  have hcross' : inner ℝ (R (e.symm (0, v)) (e.symm (0, w)) (e.symm (0, w)))
      (e.symm (u, 0)) = 0 := by
    rw [h.inner_eq, h.tangentSpaceProdEquiv_curvatureTensor_vertical hf p]
    simp only [e, ContinuousLinearEquiv.apply_symm_apply, inner_zero_right, mul_zero,
      add_zero, inner_zero_left]
  dsimp only [R] at hcross hcross'
  dsimp only [e] at hsplit hcross hcross'
  rw [hsplit]
  simp only [map_add, LinearMap.add_apply, inner_add_left, inner_add_right, hcross, hcross',
    add_zero, zero_add]
  rw [h.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hf p,
    h.inner_eq, h.tangentSpaceProdEquiv_curvatureTensor_vertical hf p]
  simp only [ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, zero_add,
    inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    Matrix.real_det_gram_fin_two, real_inner_comm w v]
  ring

/-- Over a one-dimensional base, a positive warping function with nonpositive
Laplacian and fibre curvature numerator at least `|grad f|² det Gram` gives
nonnegative sectional curvature on every plane of the warped product. The bound
on the fibre includes dependent pairs and requires no choice of orthonormal basis. -/
theorem IsWarpedProduct.sectionalCurvature_nonneg_of_finrank_eq_one
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hn : Module.finrank ℝ E = 1) (p : M × N) (hpos : 0 < f p.1)
    (hlap : laplaceBeltrami I f p.1 ≤ 0)
    (hfibre : ∀ v w : TangentSpace J p.2,
      ‖mgradient I f p.1‖ ^ 2 * (Matrix.gram ℝ ![v, w]).det ≤
        inner ℝ ((leviCivitaConnection J N).curvatureTensor p.2 v w w) v)
    (u v : TangentSpace (I.prod J) p) :
    0 ≤ (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (I.prod J)) p u v := by
  let e := tangentSpaceProdEquiv (I := I) (J := J) p
  let K := (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
    (isMetricCompatible_leviCivitaConnection (I.prod J)) p
  have hver (a : TangentSpace (I.prod J) p) (w : TangentSpace J p.2) :
      0 ≤ K a (e.symm (0, w)) := by
    dsimp only [K]
    have hnum := h.inner_curvatureTensor_vertical_right hf p (e a).1 (e a).2 w
    rw [ContinuousLinearEquiv.symm_apply_apply] at hnum
    rw [sectionalCurvature_apply, hnum]
    apply div_nonneg _ (Matrix.posSemidef_gram ℝ _).det_nonneg
    apply add_nonneg _ (mul_nonneg (sq_nonneg _) (sub_nonneg.2 (hfibre _ _)))
    rw [hessian_eq_laplaceBeltrami_mul_inner_of_finrank_eq_one hn]
    exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 hpos.le)
      (mul_nonpos_of_nonpos_of_nonneg hlap (real_inner_self_nonneg (x := (e a).1)))) (sq_nonneg _)
  by_cases hu : (e u).1 = 0
  · have heq : u = e.symm (0, (e u).2) := by rw [← hu]; exact (e.symm_apply_apply u).symm
    rw [heq, IsMetricCompatible.sectionalCurvature_comm]
    exact hver _ _
  · obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_ne_zero' (e u).1 hu).1
      ((finrank_tangentSpace p.1).trans hn) (e v).1
    have heq : v + (-a) • u = e.symm (0, (e v).2 - a • (e u).2) := by
      apply e.injective
      simp [Prod.ext_iff, ha, sub_eq_add_neg]
    rw [← sectionalCurvature_add_smul_right _ _ p u v (-a), heq]
    exact hver _ _

end TauCeti.Manifold
