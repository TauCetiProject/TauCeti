/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Scalar
import TauCeti.Geometry.Manifold.Riemannian.Restriction.Real
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace

/-!
# Curvature of warped round spheres over the real line

On any open subset of `ℝ`, the warped product metric `dr² + f(r)² g_(Sⁿ)` decomposes every tangent
two-plane `X = (a₁, v₁)`, `Y = (a₂, v₂)` at `(r, u)` into mixed and vertical parts:
* `det(Gram(X, Y)) = f(r)² ‖a₁ • v₂ - a₂ • v₁‖² + f(r)⁴ det(Gram(v₁, v₂))`,
* `⟪R(X, Y) Y, X⟫ = -f(r) f''(r) ‖a₁ • v₂ - a₂ • v₁‖² + f(r)² (1 - f'(r)²) det(Gram(v₁, v₂))`.

Hence mixed planes have sectional curvature `-f''/f`, vertical planes have `(1 - f'²)/f²`, any
common bound or value transfers to every tangent two-plane, and the scalar curvature is
`n(n-1)(1-f'²)/f² - 2n f''/f`. Smoothness and nonvanishing of `f` are needed only on the open set.

## Main results

* `TauCeti.det_gram_warpedProdTangentSpace_real_sphere`,
  `TauCeti.inner_curvatureTensor_warpedProdTangentSpace_real_sphere`: mixed/vertical decomposition
  of the Gram determinant and Riemann curvature numerator.
* `TauCeti.sectionalCurvature_warpedProdTangentSpace_real_sphere_mixed`,
  `TauCeti.sectionalCurvature_warpedProdTangentSpace_real_sphere_vertical`,
  `TauCeti.le_sectionalCurvature_warpedProdTangentSpace_real_sphere`,
  `TauCeti.sectionalCurvature_warpedProdTangentSpace_real_sphere_le`,
  `TauCeti.hasSectionalCurvatureAt_warpedProdTangentSpace_real_sphere`: sectional curvature of
  mixed, vertical, and general two-planes.
* `TauCeti.scalarCurvature_warpedProdTangentSpace_real_sphere`: scalar curvature formula.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7,
  Proposition 42 and Corollary 43.
-/

public noncomputable section

open Bundle CovariantDerivative TopologicalSpace
open TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti

private theorem contDiffAt_two_of_contMDiff {U : Opens ℝ} {f : ℝ → ℝ}
    (hf : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : U ↦ f r)) (r : U) : ContDiffAt ℝ 2 f (r : ℝ) :=
  (contMDiffAt_iff_contDiffAt.1 (contMDiffAt_subtype_iff.1 hf.contMDiffAt)).of_le (by simp)

private theorem mul_sq_eq_neg_mul_deriv_deriv {f : ℝ → ℝ} {x : ℝ} (hx : f x ≠ 0) :
    -deriv (deriv f) x / f x * f x ^ 2 = -f x * deriv (deriv f) x := by field_simp

private theorem mul_pow_four_eq_sq_mul_one_sub {f : ℝ → ℝ} {x : ℝ} (hx : f x ≠ 0) :
    (1 - deriv f x ^ 2) / f x ^ 2 * f x ^ 4 = f x ^ 2 * (1 - deriv f x ^ 2) := by field_simp

section Sectional

variable (U : Opens ℝ) {f : ℝ → ℝ} (hf : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : U ↦ f r))
  (hf₀ : ∀ r : U, f r ≠ 0) {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (Module.finrank ℝ V = n + 1)]

private abbrev realOpenMetric (U : Opens ℝ) :
    ContMDiffRiemannianMetric 𝓘(ℝ) ∞ ℝ (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
  ((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U

private abbrev realSphereWarpedMetric :
    ContMDiffRiemannianMetric (𝓘(ℝ).prod (𝓡 n)) ∞ (ℝ × EuclideanSpace ℝ (Fin n))
      (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
  (realOpenMetric U).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
    ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)

private abbrev realOpenBundle (U : Opens ℝ) : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
  ⟨(realOpenMetric U).toRiemannianMetric⟩

private abbrev realSphereWarpedBundle :
    RiemannianBundle (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
  ⟨(realSphereWarpedMetric U hf hf₀ (V := V) (n := n)).toRiemannianMetric⟩

private theorem isWarpedProduct_real_sphere :
    letI := realOpenBundle U; letI := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
    IsWarpedProduct 𝓘(ℝ) (𝓡 n) (Metric.sphere (0 : V) 1) (fun r : U ↦ f r) := by
  let _ := realOpenBundle U; let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  refine ⟨fun p v w ↦ ?_⟩
  change (realSphereWarpedMetric U hf hf₀ (V := V)).inner p v w =
    (realOpenMetric U).inner p.1 (tangentSpaceProdEquiv p v).1 (tangentSpaceProdEquiv p w).1 +
      f p.1 ^ 2 * (sphereRoundMetric (E := V) (n := n)).inner p.2
        (tangentSpaceProdEquiv p v).2 (tangentSpaceProdEquiv p w).2
  rw [realSphereWarpedMetric, ContMDiffRiemannianMetric.warpedProdTangentSpace_inner,
    ContMDiffRiemannianMetric.ofLE_inner]

private theorem eq_symm_fst_add_symm_snd (p : U × Metric.sphere (0 : V) 1)
    (Z : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    Z = (tangentSpaceProdEquiv p).symm ((tangentSpaceProdEquiv p Z).1, 0) +
      (tangentSpaceProdEquiv p).symm (0, (tangentSpaceProdEquiv p Z).2) :=
  (tangentSpaceProdEquiv p).injective (by
    simp only [map_add, ContinuousLinearEquiv.apply_symm_apply, Prod.mk_add_mk, add_zero, zero_add,
      Prod.mk.eta])

private theorem inner_linearMap_split [RiemannianBundle
    (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q)]
    (p : U × Metric.sphere (0 : V) 1)
    (L : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p →ₗ[ℝ] TangentSpace (𝓘(ℝ).prod (𝓡 n)) p)
    (X Y : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    let e := tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓡 n) p
    ⟪L Y, X⟫_ℝ =
      (⟪L (e.symm ((e Y).1, 0)), e.symm ((e X).1, 0)⟫_ℝ +
        ⟪L (e.symm (0, (e Y).2)), e.symm ((e X).1, 0)⟫_ℝ) +
      (⟪L (e.symm ((e Y).1, 0)), e.symm (0, (e X).2)⟫_ℝ +
        ⟪L (e.symm (0, (e Y).2)), e.symm (0, (e X).2)⟫_ℝ) := by
  dsimp only; conv_lhs => rw [eq_symm_fst_add_symm_snd U p Y, eq_symm_fst_add_symm_snd U p X]
  simp only [map_add, inner_add_right, inner_add_left]

/-- The Gram determinant of two tangent vectors in `dr² + f(r)² g_(Sⁿ)` splits into
`f(r)² ‖a₁ • v₂ - a₂ • v₁‖²` and `f(r)⁴ det(Gram(v₁, v₂))`, measured in the unscaled
round metric of `Sⁿ`. -/
theorem det_gram_warpedProdTangentSpace_real_sphere
    (p : U × Metric.sphere (0 : V) 1)
    (X Y : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    letI : RiemannianBundle
      (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U
        ).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    (Matrix.gram ℝ ![X, Y]).det =
      f p.1 ^ 2 *
        ‖tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p X).1 •
            (tangentSpaceProdEquiv p Y).2 -
          tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p Y).1 •
            (tangentSpaceProdEquiv p X).2‖ ^ 2 +
      f p.1 ^ 4 *
        (Matrix.gram ℝ ![(tangentSpaceProdEquiv p X).2, (tangentSpaceProdEquiv p Y).2]).det := by
  let _ := realOpenBundle U
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  have hw := isWarpedProduct_real_sphere U hf hf₀ (V := V) (n := n)
  have hbase (u w : TangentSpace 𝓘(ℝ) p.1) :
      inner ℝ u w = tangentSpaceCastModel 𝓘(ℝ) p.1 u * tangentSpaceCastModel 𝓘(ℝ) p.1 w :=
    inner_restrictOpenTangentSpace_real U p.1 u w
  rw [Matrix.real_det_gram_fin_two, Matrix.real_det_gram_fin_two, norm_sub_sq_real,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right, hw.inner_eq, hw.inner_eq, hw.inner_eq,
    hbase, hbase, hbase,
    real_inner_comm (tangentSpaceProdEquiv p X).2 (tangentSpaceProdEquiv p Y).2,
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  ring

private theorem curvatureTensor_horizontal_horizontal_real_sphere
    (p : U × Metric.sphere (0 : V) 1)
    (u₁ u₂ : TangentSpace 𝓘(ℝ) p.1) (Z : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    letI := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).curvatureTensor
        p ((tangentSpaceProdEquiv p).symm (u₁, 0))
        ((tangentSpaceProdEquiv p).symm (u₂, 0)) Z = 0 := by
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  let e := tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓡 n) p
  let e₁ : TangentSpace 𝓘(ℝ) p.1 := (tangentSpaceCastModel 𝓘(ℝ) p.1).symm 1
  have hu (u : TangentSpace 𝓘(ℝ) p.1) :
      e.symm (u, 0) = tangentSpaceCastModel 𝓘(ℝ) p.1 u • e.symm (e₁, 0) := by
    apply e.injective
    simp only [map_smul, ContinuousLinearEquiv.apply_symm_apply, Prod.smul_mk, smul_zero]
    exact Prod.ext ((tangentSpaceCastModel 𝓘(ℝ) p.1).injective (by simp [e₁])) rfl
  change (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) _).curvatureTensor
    p (e.symm (u₁, 0)) (e.symm (u₂, 0)) Z = 0
  rw [hu u₁, hu u₂]
  simp [(leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) _).curvatureTensor_self]

private theorem inner_mixed_term_real_sphere
    (p : U × Metric.sphere (0 : V) 1)
    (u : TangentSpace 𝓘(ℝ) p.1) (v : TangentSpace (𝓡 n) p.2)
    (X Y : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    letI := realOpenBundle U
    letI := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
    ⟪(leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).curvatureTensor
        p ((tangentSpaceProdEquiv p).symm (u, 0))
        ((tangentSpaceProdEquiv p).symm (0, v)) Y, X⟫_ℝ =
      f p.1 * hessian 𝓘(ℝ) (fun r : U ↦ f r) p.1 u (tangentSpaceProdEquiv p Y).1 *
          ⟪v, (tangentSpaceProdEquiv p X).2⟫_ℝ -
        f p.1 * hessian 𝓘(ℝ) (fun r : U ↦ f r) p.1 u (tangentSpaceProdEquiv p X).1 *
          ⟪v, (tangentSpaceProdEquiv p Y).2⟫_ℝ := by
  let _ := realOpenBundle U
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  let _ := Bundle.instIsContMDiffRiemannianBundle (realOpenMetric U)
  let _ :=
    Bundle.instIsContMDiffRiemannianBundle (realSphereWarpedMetric U hf hf₀ (V := V) (n := n))
  let e := tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓡 n) p
  have hw := isWarpedProduct_real_sphere U hf hf₀ (V := V) (n := n)
  have hmc := isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
    (M := U × Metric.sphere (0 : V) 1)
  have ht := torsion_leviCivitaConnection_eq_zero (𝓘(ℝ).prod (𝓡 n))
    (M := U × Metric.sphere (0 : V) 1)
  let R0 := (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) _).curvatureTensor
    p (e.symm (u, 0)) (e.symm (0, v))
  have t1 : ⟪R0 (e.symm ((e Y).1, 0)), e.symm ((e X).1, 0)⟫_ℝ = 0 :=
    (hmc.inner_curvatureTensor_swap_pairs ht p _ _ _ _).trans <| by
      rw [curvatureTensor_horizontal_horizontal_real_sphere U hf hf₀ p (e Y).1 (e X).1,
        inner_zero_left]
  have t2 : ⟪R0 (e.symm ((e Y).1, 0)), e.symm (0, (e X).2)⟫_ℝ =
      f p.1 * hessian 𝓘(ℝ) (fun r : U ↦ f r) p.1 u (e Y).1 * ⟪v, (e X).2⟫_ℝ :=
    (hmc.inner_curvatureTensor_eq_neg p _ _ _ _).trans <|
      (congrArg Neg.neg ((real_inner_comm _ _).trans
        (hw.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hf p u (e Y).1 v
          (e X).2))).trans (by ring)
  have t3 := hw.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hf p u (e X).1 v
    (e Y).2
  have t4 : ⟪R0 (e.symm (0, (e Y).2)), e.symm (0, (e X).2)⟫_ℝ = 0 :=
    (hmc.inner_curvatureTensor_swap_pairs ht p _ _ _ _).trans <|
      (hmc.inner_curvatureTensor_eq_neg p _ _ _ _).trans <| by
        rw [hw.inner_eq, hw.tangentSpaceProdEquiv_curvatureTensor_vertical hf p (e Y).2 (e X).2 v]
        simp only [e, ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, inner_zero_right,
          mul_zero, add_zero, neg_zero]
  exact (inner_linearMap_split U p R0 X Y).trans ((congrArg₂ (· + ·) (congrArg₂ (· + ·) t1 t3)
    (congrArg₂ (· + ·) t2 t4)).trans (by ring))

private theorem inner_mixed_real_sphere
    (p : U × Metric.sphere (0 : V) 1)
    (X Y : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    letI := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
    ⟪(leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).curvatureTensor
          p ((tangentSpaceProdEquiv p).symm ((tangentSpaceProdEquiv p X).1, 0))
          ((tangentSpaceProdEquiv p).symm (0, (tangentSpaceProdEquiv p Y).2)) Y -
        (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).curvatureTensor
          p ((tangentSpaceProdEquiv p).symm ((tangentSpaceProdEquiv p Y).1, 0))
          ((tangentSpaceProdEquiv p).symm (0, (tangentSpaceProdEquiv p X).2)) Y, X⟫_ℝ =
      -f p.1 * deriv (deriv f) p.1 *
        ‖tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p X).1 •
            (tangentSpaceProdEquiv p Y).2 -
          tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p Y).1 •
            (tangentSpaceProdEquiv p X).2‖ ^ 2 := by
  let _ := realOpenBundle U
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  have hf₂ := contDiffAt_two_of_contMDiff hf p.1
  have h1 := inner_mixed_term_real_sphere U hf hf₀ p
    (tangentSpaceProdEquiv p X).1 (tangentSpaceProdEquiv p Y).2 X Y
  have h2 := inner_mixed_term_real_sphere U hf hf₀ p
    (tangentSpaceProdEquiv p Y).1 (tangentSpaceProdEquiv p X).2 X Y
  rw [inner_sub_left, h1, h2, norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left,
    real_inner_smul_right,
    real_inner_comm (tangentSpaceProdEquiv p Y).2 (tangentSpaceProdEquiv p X).2,
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  repeat rw [hessian_restrictOpenTangentSpace_real_eq_mul_deriv_deriv U hf₂]
  ring

private theorem inner_vertical_horizontal_real_sphere
    (p : U × Metric.sphere (0 : V) 1)
    (v w z : TangentSpace (𝓡 n) p.2) (u : TangentSpace 𝓘(ℝ) p.1) :
    letI := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
    ⟪(leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).curvatureTensor
        p ((tangentSpaceProdEquiv p).symm (0, v)) ((tangentSpaceProdEquiv p).symm (0, w))
        ((tangentSpaceProdEquiv p).symm (0, z)),
      (tangentSpaceProdEquiv p).symm (u, 0)⟫_ℝ = 0 := by
  let _ := realOpenBundle U
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  let _ := Bundle.instIsContMDiffRiemannianBundle (realOpenMetric U)
  let _ :=
    Bundle.instIsContMDiffRiemannianBundle (realSphereWarpedMetric U hf hf₀ (V := V) (n := n))
  have hw := isWarpedProduct_real_sphere U hf hf₀ (V := V) (n := n)
  rw [hw.inner_eq, hw.tangentSpaceProdEquiv_curvatureTensor_vertical hf p v w z]
  simp only [ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, inner_zero_right, mul_zero,
    add_zero]

private theorem inner_vertical_vertical_real_sphere
    (p : U × Metric.sphere (0 : V) 1)
    (v₁ v₂ : TangentSpace (𝓡 n) p.2) :
    letI := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
    ⟪(leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).curvatureTensor
        p ((tangentSpaceProdEquiv p).symm (0, v₁))
        ((tangentSpaceProdEquiv p).symm (0, v₂))
        ((tangentSpaceProdEquiv p).symm (0, v₂)),
      (tangentSpaceProdEquiv p).symm (0, v₁)⟫_ℝ =
      f p.1 ^ 2 * (1 - deriv f p.1 ^ 2) * (Matrix.gram ℝ ![v₁, v₂]).det := by
  let _ := realOpenBundle U
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  let _ := Bundle.instIsContMDiffRiemannianBundle (realOpenMetric U)
  let _ :=
    Bundle.instIsContMDiffRiemannianBundle (realSphereWarpedMetric U hf hf₀ (V := V) (n := n))
  have hw := isWarpedProduct_real_sphere U hf hf₀ (V := V) (n := n)
  have hf₁ := (contDiffAt_two_of_contMDiff hf p.1).differentiableAt (by norm_num)
  rw [hw.inner_eq, hw.tangentSpaceProdEquiv_curvatureTensor_vertical hf p v₁ v₂ v₂,
    curvatureTensor_sphere, sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv U hf₁,
    Matrix.real_det_gram_fin_two]
  simp only [ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, zero_add, inner_sub_left,
    real_inner_smul_left]
  rw [real_inner_comm v₂ v₁]
  ring

private theorem inner_vertical_real_sphere
    (p : U × Metric.sphere (0 : V) 1)
    (X Y : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    letI := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
    ⟪(leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).curvatureTensor
        p ((tangentSpaceProdEquiv p).symm (0, (tangentSpaceProdEquiv p X).2))
        ((tangentSpaceProdEquiv p).symm (0, (tangentSpaceProdEquiv p Y).2)) Y, X⟫_ℝ =
      f p.1 ^ 2 * (1 - deriv f p.1 ^ 2) *
        (Matrix.gram ℝ ![(tangentSpaceProdEquiv p X).2, (tangentSpaceProdEquiv p Y).2]).det := by
  let _ := realOpenBundle U
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  let _ := Bundle.instIsContMDiffRiemannianBundle (realOpenMetric U)
  let _ :=
    Bundle.instIsContMDiffRiemannianBundle (realSphereWarpedMetric U hf hf₀ (V := V) (n := n))
  let e := tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓡 n) p
  have hmc := isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
    (M := U × Metric.sphere (0 : V) 1)
  have ht := torsion_leviCivitaConnection_eq_zero (𝓘(ℝ).prod (𝓡 n))
    (M := U × Metric.sphere (0 : V) 1)
  have hvvh := inner_vertical_horizontal_real_sphere U hf hf₀ (n := n) p
  let Rv := (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) _).curvatureTensor
    p (e.symm (0, (e X).2)) (e.symm (0, (e Y).2))
  have s1 : ⟪Rv (e.symm ((e Y).1, 0)), e.symm ((e X).1, 0)⟫_ℝ = 0 :=
    (hmc.inner_curvatureTensor_swap_pairs ht p _ _ _ _).trans <| by
      rw [curvatureTensor_horizontal_horizontal_real_sphere U hf hf₀ p (e Y).1 (e X).1,
        inner_zero_left]
  have s2 : ⟪Rv (e.symm ((e Y).1, 0)), e.symm (0, (e X).2)⟫_ℝ = 0 :=
    (hmc.inner_curvatureTensor_eq_neg p _ _ _ _).trans <|
      (congrArg Neg.neg ((real_inner_comm _ _).trans
        (hvvh (e X).2 (e Y).2 (e X).2 (e Y).1))).trans neg_zero
  have s3 := hvvh (e X).2 (e Y).2 (e Y).2 (e X).1
  have s4 := inner_vertical_vertical_real_sphere U hf hf₀ (n := n) p (e X).2 (e Y).2
  exact (inner_linearMap_split U p Rv X Y).trans ((congrArg₂ (· + ·) (congrArg₂ (· + ·) s1 s3)
    (congrArg₂ (· + ·) s2 s4)).trans (by ring))

/-- Full Riemann curvature numerator `⟪R(X, Y) Y, X⟫` of `dr² + f(r)² g_(Sⁿ)` on an open subset
of `ℝ` times the unit sphere, valid for arbitrary tangent vectors `X` and `Y` (including tilted
planes, dependent pairs, and low sphere dimensions). -/
theorem inner_curvatureTensor_warpedProdTangentSpace_real_sphere
    (p : U × Metric.sphere (0 : V) 1)
    (X Y : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    letI : RiemannianBundle
      (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U
        ).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    ⟪(leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).curvatureTensor
        p X Y Y, X⟫_ℝ =
      -f p.1 * deriv (deriv f) p.1 *
          ‖tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p X).1 •
              (tangentSpaceProdEquiv p Y).2 -
            tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p Y).1 •
              (tangentSpaceProdEquiv p X).2‖ ^ 2 +
        f p.1 ^ 2 * (1 - deriv f p.1 ^ 2) *
          (Matrix.gram ℝ ![(tangentSpaceProdEquiv p X).2, (tangentSpaceProdEquiv p Y).2]).det := by
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  let e := tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓡 n) p
  let C := (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).curvatureTensor p
  have hXY : C X Y Y =
      (C (e.symm ((e X).1, 0)) (e.symm ((e Y).1, 0)) Y +
        C (e.symm (0, (e X).2)) (e.symm ((e Y).1, 0)) Y) +
      (C (e.symm ((e X).1, 0)) (e.symm (0, (e Y).2)) Y +
        C (e.symm (0, (e X).2)) (e.symm (0, (e Y).2)) Y) := by
    have := congrArg₂ (fun a b ↦ C a b) (eq_symm_fst_add_symm_snd U p X)
      (eq_symm_fst_add_symm_snd U p Y)
    simpa only [map_add, LinearMap.add_apply] using congrArg (fun L ↦ L Y) this
  have hhh := curvatureTensor_horizontal_horizontal_real_sphere U hf hf₀ p (e X).1 (e Y).1 Y
  have hanti : C (e.symm (0, (e X).2)) (e.symm ((e Y).1, 0)) Y =
      -C (e.symm ((e Y).1, 0)) (e.symm (0, (e X).2)) Y := by
    rw [(leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) _).curvatureTensor_antisymm, LinearMap.neg_apply]
  have hdecomp : C X Y Y =
      (C (e.symm ((e X).1, 0)) (e.symm (0, (e Y).2)) Y -
        C (e.symm ((e Y).1, 0)) (e.symm (0, (e X).2)) Y) +
      C (e.symm (0, (e X).2)) (e.symm (0, (e Y).2)) Y := by
    rw [hXY, hhh, hanti, zero_add, ← add_assoc, add_comm (-_), ← sub_eq_add_neg]
  exact (congrArg (⟪·, X⟫_ℝ) hdecomp).trans ((inner_add_left _ _ _).trans
    (congrArg₂ (· + ·) (inner_mixed_real_sphere U hf hf₀ p X Y)
      (inner_vertical_real_sphere U hf hf₀ p X Y)))

/-- A mixed radial-spherical tangent plane in `dr² + f(r)² g_(Sⁿ)` has sectional curvature
`-f''(r) / f(r)`. Both spanning vectors must be nonzero: the totalized sectional curvature
vanishes when either input is zero, whereas `-f''(r) / f(r)` need not vanish. -/
theorem sectionalCurvature_warpedProdTangentSpace_real_sphere_mixed
    (p : U × Metric.sphere (0 : V) 1)
    (u : TangentSpace 𝓘(ℝ) p.1) (v : TangentSpace (𝓡 n) p.2) (hu : u ≠ 0) (hv : v ≠ 0) :
    letI : RiemannianBundle
      (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U
        ).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p
        ((tangentSpaceProdEquiv p).symm (u, 0))
        ((tangentSpaceProdEquiv p).symm (0, v)) =
      -deriv (deriv f) p.1 / f p.1 := by
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  have hau : tangentSpaceCastModel 𝓘(ℝ) p.1 u ≠ 0 :=
    (tangentSpaceCastModel 𝓘(ℝ) p.1).toLinearEquiv.map_ne_zero_iff.2 hu
  rw [sectionalCurvature_apply,
    inner_curvatureTensor_warpedProdTangentSpace_real_sphere U hf hf₀ p,
    det_gram_warpedProdTangentSpace_real_sphere U hf hf₀ p]
  simp only [ContinuousLinearEquiv.apply_symm_apply, map_zero, zero_smul, sub_zero, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, Matrix.real_det_gram_fin_two, inner_zero_left, zero_mul,
    zero_pow two_ne_zero, sub_self, mul_zero, add_zero]
  field_simp [hf₀ p.1, hau, norm_ne_zero_iff.2 hv]

/-- A vertical spherical tangent plane in `dr² + f(r)² g_(Sⁿ)` has sectional curvature
`(1 - f'(r)²) / f(r)²`. Linear independence is required because the totalized sectional quotient
vanishes on dependent pairs. -/
theorem sectionalCurvature_warpedProdTangentSpace_real_sphere_vertical
    (p : U × Metric.sphere (0 : V) 1)
    (v w : TangentSpace (𝓡 n) p.2) (hvw : LinearIndependent ℝ ![v, w]) :
    letI : RiemannianBundle
      (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U
        ).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p
        ((tangentSpaceProdEquiv p).symm (0, v))
        ((tangentSpaceProdEquiv p).symm (0, w)) =
      (1 - deriv f p.1 ^ 2) / f p.1 ^ 2 := by
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  have hdet := Matrix.det_gram_ne_zero_iff_linearIndependent.2 hvw
  rw [sectionalCurvature_apply,
    inner_curvatureTensor_warpedProdTangentSpace_real_sphere U hf hf₀ p,
    det_gram_warpedProdTangentSpace_real_sphere U hf hf₀ p]
  simp only [ContinuousLinearEquiv.apply_symm_apply, map_zero, zero_smul, sub_self, norm_zero,
    zero_pow two_ne_zero, mul_zero, zero_add]
  field_simp [hf₀ p.1, hdet]

private theorem det_gram_fin_two_nonneg {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v w : E) : 0 ≤ (Matrix.gram ℝ ![v, w]).det := by
  rw [Matrix.real_det_gram_fin_two]
  nlinarith [real_inner_mul_inner_self_le v w]

/-- A common lower bound `κ` on the mixed and vertical sectional curvatures `-f''/f` and
`(1 - f'²)/f²` bounds the curvature numerator from below for all tangent pairs, hence bounds the
sectional curvature of every tangent two-plane at `p`. -/
theorem le_sectionalCurvature_warpedProdTangentSpace_real_sphere
    (p : U × Metric.sphere (0 : V) 1) {κ : ℝ}
    (hmix : κ ≤ -deriv (deriv f) p.1 / f p.1)
    (hvert : κ ≤ (1 - deriv f p.1 ^ 2) / f p.1 ^ 2)
    (X Y : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) (hXY : LinearIndependent ℝ ![X, Y]) :
    letI : RiemannianBundle
      (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U
        ).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    κ ≤ (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p X Y := by
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  let _ :=
    Bundle.instIsContMDiffRiemannianBundle (realSphereWarpedMetric U hf hf₀ (V := V) (n := n))
  rw [sectionalCurvature_apply, le_div_iff₀ (Matrix.posDef_gram_of_linearIndependent hXY).det_pos,
    inner_curvatureTensor_warpedProdTangentSpace_real_sphere U hf hf₀ p,
    det_gram_warpedProdTangentSpace_real_sphere U hf hf₀ p]
  have h1 := (mul_le_mul_of_nonneg_right hmix (sq_nonneg (f p.1))).trans_eq
    (mul_sq_eq_neg_mul_deriv_deriv (hf₀ p.1))
  have h2 := (mul_le_mul_of_nonneg_right hvert (by positivity)).trans_eq
    (mul_pow_four_eq_sq_mul_one_sub (hf₀ p.1))
  nlinarith [det_gram_fin_two_nonneg (tangentSpaceProdEquiv p X).2 (tangentSpaceProdEquiv p Y).2,
    sq_nonneg ‖tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p X).1 •
        (tangentSpaceProdEquiv p Y).2 -
      tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p Y).1 •
        (tangentSpaceProdEquiv p X).2‖]

/-- If `-f''/f` and `(1 - f'²)/f²` are nonnegative at `p`, the sectional curvature of
`dr² + f(r)² g_(Sⁿ)` is nonnegative on *every* pair of tangent vectors at `p` (dependent pairs
give zero). -/
theorem sectionalCurvature_warpedProdTangentSpace_real_sphere_nonneg
    (p : U × Metric.sphere (0 : V) 1)
    (hmix : 0 ≤ -deriv (deriv f) p.1 / f p.1)
    (hvert : 0 ≤ (1 - deriv f p.1 ^ 2) / f p.1 ^ 2)
    (X Y : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    letI : RiemannianBundle
      (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U
        ).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    0 ≤ (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p X Y := by
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  by_cases hXY : LinearIndependent ℝ ![X, Y]
  · exact le_sectionalCurvature_warpedProdTangentSpace_real_sphere U hf hf₀ p hmix hvert X Y hXY
  · rw [sectionalCurvature_apply,
      not_not.mp (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr hXY), div_zero]

/-- A common upper bound `κ` on `-f''/f` and `(1 - f'²)/f²` bounds the sectional curvature of
every tangent two-plane at `p` from above. -/
theorem sectionalCurvature_warpedProdTangentSpace_real_sphere_le
    (p : U × Metric.sphere (0 : V) 1) {κ : ℝ}
    (hmix : -deriv (deriv f) p.1 / f p.1 ≤ κ)
    (hvert : (1 - deriv f p.1 ^ 2) / f p.1 ^ 2 ≤ κ)
    (X Y : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) (hXY : LinearIndependent ℝ ![X, Y]) :
    letI : RiemannianBundle
      (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U
        ).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p X Y ≤ κ := by
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  let _ :=
    Bundle.instIsContMDiffRiemannianBundle (realSphereWarpedMetric U hf hf₀ (V := V) (n := n))
  rw [sectionalCurvature_apply, div_le_iff₀ (Matrix.posDef_gram_of_linearIndependent hXY).det_pos,
    inner_curvatureTensor_warpedProdTangentSpace_real_sphere U hf hf₀ p,
    det_gram_warpedProdTangentSpace_real_sphere U hf hf₀ p]
  have h1 := (mul_sq_eq_neg_mul_deriv_deriv (hf₀ p.1)).symm.trans_le
    (mul_le_mul_of_nonneg_right hmix (sq_nonneg (f p.1)))
  have h2 := (mul_pow_four_eq_sq_mul_one_sub (hf₀ p.1)).symm.trans_le
    (mul_le_mul_of_nonneg_right hvert (by positivity))
  nlinarith [det_gram_fin_two_nonneg (tangentSpaceProdEquiv p X).2 (tangentSpaceProdEquiv p Y).2,
    sq_nonneg ‖tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p X).1 •
        (tangentSpaceProdEquiv p Y).2 -
      tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p Y).1 •
        (tangentSpaceProdEquiv p X).2‖]

/-- When `-f''/f = κ` and `(1 - f'²)/f² = κ` at `p`, every tangent two-plane of
`dr² + f(r)² g_(Sⁿ)` at `p` has sectional curvature `κ`. -/
theorem hasSectionalCurvatureAt_warpedProdTangentSpace_real_sphere
    (p : U × Metric.sphere (0 : V) 1) {κ : ℝ}
    (hmix : -deriv (deriv f) p.1 / f p.1 = κ)
    (hvert : (1 - deriv f p.1 ^ 2) / f p.1 ^ 2 = κ) :
    letI : RiemannianBundle
      (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U
        ).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p κ := by
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  exact ((leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)
    ).hasSectionalCurvatureAt_iff _ p κ).2 fun X Y hXY ↦ le_antisymm
    (sectionalCurvature_warpedProdTangentSpace_real_sphere_le U hf hf₀ p hmix.le hvert.le X Y hXY)
    (le_sectionalCurvature_warpedProdTangentSpace_real_sphere U hf hf₀ p hmix.ge hvert.ge X Y hXY)

end Sectional

/-- Scalar curvature of `dr² + f(r)² g_(Sⁿ)` on an arbitrary open subset of
`ℝ` times the unit sphere. Smoothness and nonvanishing are required only on the
open set; the sign of `f` is irrelevant. -/
theorem scalarCurvature_warpedProdTangentSpace_real_sphere
    (U : Opens ℝ) {f : ℝ → ℝ}
    (hf : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : U ↦ f r))
    (hf₀ : ∀ r : U, f r ≠ 0)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (p : U × Metric.sphere (0 : V) 1) :
    let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
    ((g.restrictOpenTangentSpace U).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
      ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).scalarCurvature p =
      (n : ℝ) * (n - 1) * (1 - deriv f p.1 ^ 2) / f p.1 ^ 2 -
        2 * n * deriv (deriv f) p.1 / f p.1 := by
  dsimp only
  let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
  have hg : g.scalarCurvature (p.1 : ℝ) = 0 := by
    rw [ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvature_leviCivitaConnection g
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _).symm,
      scalarCurvature_leviCivitaConnection_model_space]
  have hf₂ := contDiffAt_two_of_contMDiff hf p.1
  rw [ContMDiffRiemannianMetric.scalarCurvature_warpedProdTangentSpace,
    ContMDiffRiemannianMetric.scalarCurvature_restrictOpenTangentSpace,
    scalarCurvature_sphereRoundMetric_ofLE, hg,
    laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv U hf₂,
    sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv U
      (hf₂.differentiableAt (by norm_num))]
  simp only [finrank_euclideanSpace_fin]
  ring

end TauCeti
