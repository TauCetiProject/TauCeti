/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Sectional
import TauCeti.Analysis.InnerProductSpace.Gram.Basic
import TauCeti.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Restriction.Real
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace

/-!
# Curvature of warped round spheres over the real line

On any open subset of `ℝ`, specializing the warped-product curvature formulas over a curve to the
round sphere `Sⁿ` gives the curvature of `dr² + f(r)² g_(Sⁿ)`: mixed radial-spherical planes have
sectional curvature `-f''/f`, vertical spherical planes have `(1 - f'²)/f²`, any common lower or
upper bound on `-f''/f` and (for `2 ≤ n`) `(1 - f'²)/f²` transfers to every tangent two-plane, the
sectional curvature is nonnegative when `f f'' ≤ 0` and `f'² ≤ 1` at the point and equals `k` when
`f'' = -k f` and `f'² + k f² = 1` there, and the scalar curvature is
`n(n-1)(1-f'²)/f² - 2n f''/f`. Smoothness and nonvanishing of `f` are needed only on the open set;
no standard-cap assumptions enter these computations.

## Main results

* `TauCeti.sectionalCurvature_warpedProdTangentSpace_real_sphere_horizontal_vertical`,
  `TauCeti.sectionalCurvature_warpedProdTangentSpace_real_sphere_vertical`,
  `TauCeti.le_sectionalCurvature_warpedProdTangentSpace_real_sphere`,
  `TauCeti.sectionalCurvature_warpedProdTangentSpace_real_sphere_le`,
  `TauCeti.hasSectionalCurvatureAt_warpedProdTangentSpace_real_sphere`,
  `TauCeti.sectionalCurvature_warpedProdTangentSpace_real_sphere_nonneg`: sectional curvature of
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

private theorem mul_sq_eq_neg_mul_deriv_deriv {f : ℝ → ℝ} {x : ℝ} (hx : f x ≠ 0) :
    -deriv (deriv f) x / f x * f x ^ 2 = -f x * deriv (deriv f) x := by field_simp

private abbrev realOpenMetric (U : Opens ℝ) :
    ContMDiffRiemannianMetric 𝓘(ℝ) ∞ ℝ (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
  ((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U

private abbrev realOpenBundle (U : Opens ℝ) : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
  ⟨(realOpenMetric U).toRiemannianMetric⟩

section Sectional

variable (U : Opens ℝ) {f : ℝ → ℝ} (hf : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : U ↦ f r))
  (hf₀ : ∀ r : U, f r ≠ 0) {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (Module.finrank ℝ V = n + 1)]

private abbrev realSphereWarpedMetric :
    ContMDiffRiemannianMetric (𝓘(ℝ).prod (𝓡 n)) ∞ (ℝ × EuclideanSpace ℝ (Fin n))
      (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
  (realOpenMetric U).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
    ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)

private abbrev realSphereWarpedBundle :
    RiemannianBundle (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
  ⟨(realSphereWarpedMetric U hf hf₀ (V := V) (n := n)).toRiemannianMetric⟩

private theorem isWarpedProduct_real_sphere :
    letI := realOpenBundle U; letI := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
    IsWarpedProduct 𝓘(ℝ) (𝓡 n) (Metric.sphere (0 : V) 1) (fun r : U ↦ f r) := by
  let _ := realOpenBundle U; let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  refine ⟨fun p v w ↦ ?_⟩
  rw [ContMDiffRiemannianMetric.inner_riemannianBundle (realSphereWarpedMetric U hf hf₀ (V := V)),
    ContMDiffRiemannianMetric.inner_riemannianBundle (realOpenMetric U),
    ContMDiffRiemannianMetric.inner_riemannianBundle (sphereRoundMetric (E := V)),
    realSphereWarpedMetric, ContMDiffRiemannianMetric.warpedProdTangentSpace_inner,
    ContMDiffRiemannianMetric.ofLE_inner]

/-- A mixed radial-spherical tangent plane in `dr² + f(r)² g_(Sⁿ)` has sectional curvature
`-f''(r) / f(r)`. Both spanning vectors must be nonzero: the totalized sectional curvature
vanishes when either input is zero, whereas `-f''(r) / f(r)` need not vanish. -/
theorem sectionalCurvature_warpedProdTangentSpace_real_sphere_horizontal_vertical
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
  let _ := realOpenBundle U
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  let _ := Bundle.instIsContMDiffRiemannianBundle (realOpenMetric U)
  let _ :=
    Bundle.instIsContMDiffRiemannianBundle (realSphereWarpedMetric U hf hf₀ (V := V) (n := n))
  have hw := isWarpedProduct_real_sphere U hf hf₀ (V := V) (n := n)
  have hf₂ : ContDiffAt ℝ 2 f p.1 :=
    (contMDiffAt_subtype_iff_contDiffAt.1 hf.contMDiffAt).of_le (by simp)
  have hnorm : ‖u‖ ^ 2 = tangentSpaceCastModel 𝓘(ℝ) p.1 u ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      ContMDiffRiemannianMetric.inner_riemannianBundle (realOpenMetric U),
      inner_restrictOpenTangentSpace_real U p.1 u u, sq]
  have hau : tangentSpaceCastModel 𝓘(ℝ) p.1 u ≠ 0 :=
    (tangentSpaceCastModel 𝓘(ℝ) p.1).toLinearEquiv.map_ne_zero_iff.2 hu
  rw [hw.sectionalCurvature_horizontal_vertical hf p u v hv,
    hessian_restrictOpenTangentSpace_real_eq_mul_deriv_deriv U hf₂, hnorm]
  field_simp [hf₀ p.1, hau]

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
  let _ := realOpenBundle U
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  let _ := Bundle.instIsContMDiffRiemannianBundle (realOpenMetric U)
  let _ :=
    Bundle.instIsContMDiffRiemannianBundle (realSphereWarpedMetric U hf hf₀ (V := V) (n := n))
  have hw := isWarpedProduct_real_sphere U hf hf₀ (V := V) (n := n)
  have hf₁ : DifferentiableAt ℝ f p.1 :=
    (contMDiffAt_subtype_iff_contDiffAt.1 hf.contMDiffAt).differentiableAt (by simp)
  rw [hw.sectionalCurvature_vertical hf p v w hvw,
    ((hasConstantSectionalCurvature_sphere (E := V) (n := n)).hasSectionalCurvatureAt
      p.2).sectionalCurvature_eq v w hvw,
    sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv U hf₁]

/-- A common lower bound `κ` on `-f''/f` and (for `2 ≤ n`) `(1 - f'²)/f²` bounds the sectional
curvature of every tangent two-plane at `p` from below. -/
theorem le_sectionalCurvature_warpedProdTangentSpace_real_sphere
    (p : U × Metric.sphere (0 : V) 1) {κ : ℝ}
    (hmix : κ ≤ -deriv (deriv f) p.1 / f p.1)
    (hvert : 2 ≤ n → κ ≤ (1 - deriv f p.1 ^ 2) / f p.1 ^ 2)
    (X Y : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) (hXY : LinearIndependent ℝ ![X, Y]) :
    letI : RiemannianBundle
      (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U
        ).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    κ ≤ (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p X Y := by
  let _ := realOpenBundle U
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  let _ := Bundle.instIsContMDiffRiemannianBundle (realOpenMetric U)
  let _ :=
    Bundle.instIsContMDiffRiemannianBundle (realSphereWarpedMetric U hf hf₀ (V := V) (n := n))
  have hw := isWarpedProduct_real_sphere U hf hf₀ (V := V) (n := n)
  have hf₂ : ContDiffAt ℝ 2 f p.1 :=
    (contMDiffAt_subtype_iff_contDiffAt.1 hf.contMDiffAt).of_le (by simp)
  refine hw.le_sectionalCurvature_of_finrank_le_one hf (by simp) p ?_ (fun v w ↦ ?_) hXY
  · rw [laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv U hf₂]
    have := (mul_le_mul_of_nonneg_right hmix (sq_nonneg (f p.1))).trans_eq
      (mul_sq_eq_neg_mul_deriv_deriv (hf₀ p.1))
    linarith
  · rw [inner_curvatureTensor_sphere_eq_det_gram,
      sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv U
        (hf₂.differentiableAt (by norm_num))]
    by_cases hn : 2 ≤ n
    · have hcoef : κ * f p.1 ^ 2 + deriv f p.1 ^ 2 ≤ 1 := by
        have := (mul_le_mul_of_nonneg_right (hvert hn) (sq_nonneg (f p.1))).trans_eq
          (div_mul_cancel₀ _ (pow_ne_zero 2 (hf₀ p.1)))
        linarith
      nlinarith [(Matrix.posSemidef_gram ℝ ![v, w]).det_nonneg]
    · have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p.2) < Fintype.card (Fin 2) := by
        rw [TauCeti.finrank_tangentSpace, finrank_euclideanSpace_fin, Fintype.card_fin]
        omega
      simp [Matrix.det_gram_eq_zero_of_finrank_lt hdim ![v, w]]

/-- A common upper bound `κ` on `-f''/f` and (for `2 ≤ n`) `(1 - f'²)/f²` bounds the sectional
curvature of every tangent two-plane at `p` from above. -/
theorem sectionalCurvature_warpedProdTangentSpace_real_sphere_le
    (p : U × Metric.sphere (0 : V) 1) {κ : ℝ}
    (hmix : -deriv (deriv f) p.1 / f p.1 ≤ κ)
    (hvert : 2 ≤ n → (1 - deriv f p.1 ^ 2) / f p.1 ^ 2 ≤ κ)
    (X Y : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) (hXY : LinearIndependent ℝ ![X, Y]) :
    letI : RiemannianBundle
      (fun q : U × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace U
        ).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n)) (U × Metric.sphere (0 : V) 1)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p X Y ≤ κ := by
  let _ := realOpenBundle U
  let _ := realSphereWarpedBundle U hf hf₀ (V := V) (n := n)
  let _ := Bundle.instIsContMDiffRiemannianBundle (realOpenMetric U)
  let _ :=
    Bundle.instIsContMDiffRiemannianBundle (realSphereWarpedMetric U hf hf₀ (V := V) (n := n))
  have hw := isWarpedProduct_real_sphere U hf hf₀ (V := V) (n := n)
  have hf₂ : ContDiffAt ℝ 2 f p.1 :=
    (contMDiffAt_subtype_iff_contDiffAt.1 hf.contMDiffAt).of_le (by simp)
  refine hw.sectionalCurvature_le_of_finrank_le_one hf (by simp) p ?_ (fun v w ↦ ?_) hXY
  · rw [laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv U hf₂]
    have := (mul_sq_eq_neg_mul_deriv_deriv (hf₀ p.1)).symm.trans_le
      (mul_le_mul_of_nonneg_right hmix (sq_nonneg (f p.1)))
    linarith
  · rw [inner_curvatureTensor_sphere_eq_det_gram,
      sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv U
        (hf₂.differentiableAt (by norm_num))]
    by_cases hn : 2 ≤ n
    · have hcoef : 1 ≤ κ * f p.1 ^ 2 + deriv f p.1 ^ 2 := by
        have := (div_mul_cancel₀ (1 - deriv f p.1 ^ 2) (pow_ne_zero 2 (hf₀ p.1))).symm.trans_le
          (mul_le_mul_of_nonneg_right (hvert hn) (sq_nonneg (f p.1)))
        linarith
      nlinarith [(Matrix.posSemidef_gram ℝ ![v, w]).det_nonneg]
    · have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p.2) < Fintype.card (Fin 2) := by
        rw [TauCeti.finrank_tangentSpace, finrank_euclideanSpace_fin, Fintype.card_fin]
        omega
      simp [Matrix.det_gram_eq_zero_of_finrank_lt hdim ![v, w]]

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
  have hf₂ : ContDiffAt ℝ 2 f (p.1 : ℝ) :=
    (contMDiffAt_subtype_iff_contDiffAt.1 hf.contMDiffAt).of_le (by simp)
  rw [ContMDiffRiemannianMetric.scalarCurvature_warpedProdTangentSpace,
    ContMDiffRiemannianMetric.scalarCurvature_restrictOpenTangentSpace,
    scalarCurvature_sphereRoundMetric_ofLE, hg,
    laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv U hf₂,
    sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv U
      (hf₂.differentiableAt (by norm_num))]
  simp only [finrank_euclideanSpace_fin]
  ring

/-- The metric `dr² + f(r)² g_(Sⁿ)` has nonnegative sectional curvature when
`f f'' ≤ 0` and `f'² ≤ 1` at the radial coordinate. The warping function need
only be smooth and nonzero on the open set; its sign is irrelevant. -/
theorem sectionalCurvature_warpedProdTangentSpace_real_sphere_nonneg
    (U : Opens ℝ) {f : ℝ → ℝ}
    (hf : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : U ↦ f r))
    (hf₀ : ∀ r : U, f r ≠ 0)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (p : U × Metric.sphere (0 : V) 1)
    (hdd : f p.1 * deriv (deriv f) p.1 ≤ 0) (hd : deriv f p.1 ^ 2 ≤ 1)
    (u v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
    letI : RiemannianBundle (fun q : U × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((g.restrictOpenTangentSpace U).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    0 ≤ (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
      (U × Metric.sphere (0 : V) 1)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p u v := by
  let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
  let g₁ := g.restrictOpenTangentSpace U
  let g₂ := (sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top
  let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) := ⟨g₁.toRiemannianMetric⟩
  let : RiemannianBundle (fun s : Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓡 n) s) :=
    ⟨g₂.toRiemannianMetric⟩
  let : RiemannianBundle (fun q : U × Metric.sphere (0 : V) 1 ↦
    TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
    ⟨(g₁.warpedProdTangentSpace (fun r ↦ f r) hf hf₀ g₂).toRiemannianMetric⟩
  have h : IsWarpedProduct 𝓘(ℝ) (𝓡 n) (Metric.sphere (0 : V) 1) (fun r : U ↦ f r) :=
    ⟨fun q a b ↦ ContMDiffRiemannianMetric.warpedProdTangentSpace_inner _ _ _ _ _ q a b⟩
  have hf₂ : ContDiffAt ℝ 2 f (p.1 : ℝ) :=
    (contMDiffAt_iff_contDiffAt.1 (contMDiffAt_subtype_iff.1
      hf.contMDiffAt)).of_le (by simp)
  apply h.sectionalCurvature_nonneg_of_finrank_le_one hf (by simp) p
  · rwa [laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv U hf₂]
  · intro a b
    have hR := g₂.isConstantCurvatureTensor_iff 1 |>.mp
      isConstantCurvatureTensor_sphereRoundMetric_ofLE p.2 a b b
    rw [hR, one_smul]
    simp only [inner_sub_left, real_inner_smul_left]
    rw [sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv U
      (hf₂.differentiableAt (by norm_num)), Matrix.real_det_gram_fin_two]
    have hgram := (Matrix.posSemidef_gram ℝ ![a, b]).det_nonneg
    rw [Matrix.real_det_gram_fin_two] at hgram
    have hbound := mul_le_mul_of_nonneg_right hd hgram
    simp only [real_inner_comm b a] at *
    nlinarith

/-- The metric `dr² + f(r)² g_(Sⁿ)` has sectional curvature `k` at a point where
`f'' = -k f` and `f'² + k f² = 1`. These are the equations satisfied by the profiles
`sin (√k r) / √k` of round spheres when `k > 0`. The warping function need only be smooth and
nonzero on the open set; its sign is irrelevant. -/
theorem hasSectionalCurvatureAt_warpedProdTangentSpace_real_sphere
    (U : Opens ℝ) {f : ℝ → ℝ}
    (hf : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : U ↦ f r))
    (hf₀ : ∀ r : U, f r ≠ 0)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (p : U × Metric.sphere (0 : V) 1) {k : ℝ}
    (hdd : deriv (deriv f) p.1 = -(k * f p.1)) (hd : deriv f p.1 ^ 2 + k * f p.1 ^ 2 = 1) :
    let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
    letI : RiemannianBundle (fun q : U × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((g.restrictOpenTangentSpace U).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
      (U × Metric.sphere (0 : V) 1)).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p k := by
  let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
  let g₁ := g.restrictOpenTangentSpace U
  let g₂ := (sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top
  let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) := ⟨g₁.toRiemannianMetric⟩
  let : RiemannianBundle (fun s : Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓡 n) s) :=
    ⟨g₂.toRiemannianMetric⟩
  let : RiemannianBundle (fun q : U × Metric.sphere (0 : V) 1 ↦
    TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
    ⟨(g₁.warpedProdTangentSpace (fun r ↦ f r) hf hf₀ g₂).toRiemannianMetric⟩
  have h : IsWarpedProduct 𝓘(ℝ) (𝓡 n) (Metric.sphere (0 : V) 1) (fun r : U ↦ f r) :=
    ⟨fun q a b ↦ ContMDiffRiemannianMetric.warpedProdTangentSpace_inner _ _ _ _ _ q a b⟩
  have hf₂ : ContDiffAt ℝ 2 f (p.1 : ℝ) :=
    (contMDiffAt_iff_contDiffAt.1 (contMDiffAt_subtype_iff.1
      hf.contMDiffAt)).of_le (by simp)
  apply h.hasSectionalCurvatureAt_of_finrank_le_one hf (by simp) p
  · rw [laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv U hf₂, hdd]
    ring
  · intro a b
    have hR := g₂.isConstantCurvatureTensor_iff 1 |>.mp
      isConstantCurvatureTensor_sphereRoundMetric_ofLE p.2 a b b
    rw [hR, one_smul, sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv U
      (hf₂.differentiableAt (by norm_num)), hd, one_mul, Matrix.real_det_gram_fin_two]
    simp only [inner_sub_left, real_inner_smul_left, real_inner_comm b a]
    ring

end TauCeti
