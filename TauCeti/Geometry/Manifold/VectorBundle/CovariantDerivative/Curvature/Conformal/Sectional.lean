/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Conformal.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Sectional curvature under conformal change

For `ĝ = e^(2φ) g`, the sectional curvature on a `g`-orthonormal pair `u, v` is

`K_ĝ(u,v) = e^(-2φ) (K_g(u,v) - Hess φ(u,u) - Hess φ(v,v)
  + dφ(u)² + dφ(v)² - |grad φ|²)`.

This file also gives the formula for an arbitrary independent spanning pair, with its Gram
determinant, and the surface formula `K_ĝ = e^(-2φ) (K_g - Δφ)`, where `Δ = div grad`.
All differentials, Hessians and norms on the right are for `g`. The orthonormal pair is for
`g`, rather than the rescaled metric; sectional curvature is independent of its normalization.
The independent-pair hypotheses exclude the totalized quotient on degenerate pairs.

These are contractions of the conformal curvature tensor, with convention
`R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y]Z`, so the round sphere has curvature `+1`.
No completeness, compactness, connectedness or dimension restriction is used in the general
formula. The surface formula explicitly requires dimension two.

## Main results

* `Bundle.ContMDiffRiemannianMetric.sectionalCurvature_leviCivitaConnection_rescale`:
  transformation on arbitrary independent spanning vectors.
* `Bundle.ContMDiffRiemannianMetric.sectionalCurvature_leviCivitaConnection_rescale_of_orthonormal`:
  transformation on a pair orthonormal for the original metric.
* The surface specialization
  `sectionalCurvature_leviCivitaConnection_rescale_of_finrank_eq_two`
  in `Bundle.ContMDiffRiemannianMetric`:
  Gaussian curvature transformation on a surface.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.J.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer (2018), Chapter 7.
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace Matrix

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- Under `ĝ = f g = e^(2φ) g`, the sectional curvature of an independent pair is obtained by
contracting the Hessian and differential of `φ` against that pair and dividing by its original
Gram determinant. All quantities on the right are computed for `g`. -/
theorem sectionalCurvature_leviCivitaConnection_rescale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ}
    (hfφ : ∀ x, f x = Real.exp (2 * φ x)) (x : M) (u v : TangentSpace I x)
    (huv : LinearIndependent ℝ ![u, v]) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v) =
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    (f x)⁻¹ * ((CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v +
      (2 * ⟪u, v⟫ * hessian I φ x u v - ⟪u, u⟫ * hessian I φ x v v -
        ⟪v, v⟫ * hessian I φ x u u +
        ⟪u, u⟫ * mvfderiv I φ x v ^ 2 + ⟪v, v⟫ * mvfderiv I φ x u ^ 2 -
        2 * ⟪u, v⟫ * mvfderiv I φ x u * mvfderiv I φ x v) /
          (Matrix.gram ℝ ![u, v]).det - ‖mgradient I φ x‖ ^ 2) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hφ : ContMDiff I 𝓘(ℝ) ∞ φ := by
    simpa only [hfφ, Real.log_exp, mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] using
      (hf.log fun y ↦ (hf_pos y).ne').div_const 2
  have hH (a b : TangentSpace I x) : g.inner x
      (CovariantDerivative.leviCivitaConnection I M (mgradient I φ) x a) b =
        hessian I φ x a b := (hessian_def I φ x a b).symm
  have hd (a : TangentSpace I x) : g.inner x (mgradient I φ x) a = mvfderiv I φ x a :=
    inner_mgradient a
  have hdet : ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2 ≠ 0 := by
    rw [← Matrix.real_det_gram_fin_two]
    exact (Matrix.posDef_gram_of_linearIndependent huv).det_pos.ne'
  have hs : g.inner x v u = g.inner x u v := real_inner_comm u v
  have hgram :
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (Matrix.gram ℝ ![u, v]).det) =
        f x ^ 2 * (g.inner x u u * g.inner x v v - g.inner x u v ^ 2) := by
    simp [Matrix.det_fin_two, Matrix.gram_apply, inner_riemannianBundle, rescale_inner, hs]
    ring
  -- The numerator scales by `f`; its Gram denominator scales by `f²`.
  simp only [CovariantDerivative.sectionalCurvature_apply]
  rw [hgram]
  simp only [Matrix.real_det_gram_fin_two, inner_riemannianBundle, rescale_inner,
    curvatureTensor_leviCivitaConnection_rescale g hf hf_pos hfφ]
  simp only [map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply,
    smul_eq_mul, hH, hd]
  rw [hs, hessian_symm x (hφ.of_le (by simp)).contMDiffAt v u]
  -- Express the nonzero denominator and all metric coefficients in the same metric API.
  simp only [inner_riemannianBundle] at hdet
  field_simp [hdet, (hf_pos x).ne']
  ring

/-- For a pair orthonormal in `g`, conformal change subtracts the two directional Hessians and
adds the squared differential in the plane minus the full squared gradient norm. -/
theorem sectionalCurvature_leviCivitaConnection_rescale_of_orthonormal
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ}
    (hfφ : ∀ x, f x = Real.exp (2 * φ x)) (x : M) (u v : TangentSpace I x)
    (huv : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      Orthonormal ℝ ![u, v]) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v) =
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    (f x)⁻¹ * ((CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v -
      hessian I φ x u u - hessian I φ x v v +
      mvfderiv I φ x u ^ 2 + mvfderiv I φ x v ^ 2 - ‖mgradient I φ x‖ ^ 2) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [sectionalCurvature_leviCivitaConnection_rescale g hf hf_pos hfφ x u v
    huv.linearIndependent, Matrix.gram_eq_one_iff_orthonormal.mpr huv, Matrix.det_one]
  have hu : ⟪u, u⟫ = 1 := inner_self_eq_one_of_norm_eq_one (huv.1 0)
  have hv : ⟪v, v⟫ = 1 := inner_self_eq_one_of_norm_eq_one (huv.1 1)
  have hzero : ⟪u, v⟫ = 0 := huv.2 (by decide : (0 : Fin 2) ≠ 1)
  simp only [hu, hv, hzero]
  ring

/-- **Gaussian curvature under conformal change.** On a surface, for any independent pair,
`K_(e^(2φ)g) = e^(-2φ) (K_g - Δφ)`, where `Δ = div grad` for `g`. -/
theorem sectionalCurvature_leviCivitaConnection_rescale_of_finrank_eq_two
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hE : Module.finrank ℝ E = 2) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ} (hfφ : ∀ x, f x = Real.exp (2 * φ x))
    (x : M) (u v : TangentSpace I x) (huv : LinearIndependent ℝ ![u, v]) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v) =
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    (f x)⁻¹ * ((CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v -
      laplaceBeltrami I φ x) := by
  have hdim : Module.finrank ℝ (TangentSpace I x) = 2 := by
    rw [TauCeti.finrank_tangentSpace, hE]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hK (g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v) =
        g'.scalarCurvature x / 2 := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
    rw [scalarCurvature_def]
    let cov := CovariantDerivative.leviCivitaConnection I M
    have h := cov.hasSectionalCurvatureAt_scalarCurvature_div_two
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) hdim
    exact h.sectionalCurvature_eq u v huv
  rw [hK (g.rescale f hf hf_pos), hK g,
    scalarCurvature_rescale_of_finrank_eq_two g hE hf hf_pos hfφ x]
  ring

end Bundle.ContMDiffRiemannianMetric
