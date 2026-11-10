/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Geometry.Manifold.Riemannian.Hessian.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace

/-!
# Radial calculus on open subsets of the real line

For the restriction of the standard Euclidean metric to any open subset of `ℝ`,
the Laplace–Beltrami operator is the second derivative and the squared gradient
norm is the square of the first derivative. Only pointwise regularity is needed.
These identities supply the radial terms in warped-product curvature formulas.
-/

public noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.Manifold

/-- The Laplace–Beltrami operator of the restricted Euclidean metric on an open
subset of `ℝ` is the ordinary second derivative. -/
theorem laplaceBeltrami_restrictOpen_real_eq_deriv_deriv
    (U : Opens ℝ) {f : ℝ → ℝ} {x : U} (hf : ContDiffAt ℝ 2 f (x : ℝ)) :
    let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
    let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
      ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
    laplaceBeltrami 𝓘(ℝ) (fun r : U ↦ f r) x = deriv (deriv f) x := by
  dsimp only
  let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
  let gU := g.restrictOpenTangentSpace U
  let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) := ⟨gU.toRiemannianMetric⟩
  let : RiemannianBundle (fun r : ℝ ↦ TangentSpace 𝓘(ℝ) r) := ⟨g.toRiemannianMetric⟩
  let := Bundle.instIsContMDiffRiemannianBundle gU
  let := Bundle.instIsContMDiffRiemannianBundle g
  have h := (g.isLocalRiemannianIsometry_restrictOpenTangentSpace U).laplaceBeltrami_comp
    (u := f) (x := x) hf.contMDiffAt
  simp only [Function.comp_def] at h
  rw [h, laplaceBeltrami_eq_laplacian_of_eq
    (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _)
    ((hf.gradient_right (m := 1) (by norm_num)).differentiableAt (by norm_num)),
    InnerProductSpace.laplacian_eq_iteratedDeriv_real]
  simp [iteratedDeriv_succ]

/-- The squared gradient norm for the restricted Euclidean metric on an open
subset of `ℝ` is the square of the ordinary derivative. -/
theorem norm_mgradient_restrictOpen_real_sq
    (U : Opens ℝ) {f : ℝ → ℝ} {x : U} (hf : DifferentiableAt ℝ f (x : ℝ)) :
    let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
    let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
      ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
    ‖mgradient 𝓘(ℝ) (fun r : U ↦ f r) x‖ ^ 2 = deriv f x ^ 2 := by
  dsimp only
  let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
  let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
    ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
  let : RiemannianBundle (fun r : ℝ ↦ TangentSpace 𝓘(ℝ) r) := ⟨g.toRiemannianMetric⟩
  have h := (g.isLocalRiemannianIsometry_restrictOpenTangentSpace U).norm_mgradient_comp
    (φ := f) (x := x) hf.mdifferentiableAt
  simp only [Function.comp_def] at h
  rw [h, norm_mgradient_eq_norm_gradient_of_eq
    (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _),
    gradient_eq_deriv', Real.norm_eq_abs, sq_abs]

end TauCeti.Manifold
