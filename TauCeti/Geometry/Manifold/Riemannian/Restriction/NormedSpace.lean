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
# Euclidean calculus on open subsets of inner product spaces

For the restriction of the standard Euclidean metric to an open subset of a
finite-dimensional real inner product space, the Laplace–Beltrami operator is
the flat Laplacian and the manifold gradient has the norm of the flat gradient.
Only pointwise regularity is needed. The real-line specializations supply the
radial terms in warped-product curvature formulas.
-/

public noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff Manifold Gradient Laplacian

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The Laplace–Beltrami operator of the restricted Euclidean metric on an open
subset of a finite-dimensional real inner product space is the flat Laplacian. -/
theorem laplaceBeltrami_restrictOpenTangentSpace_eq_laplacian
    (U : Opens F) {f : F → ℝ} {x : U} (hf : ContDiffAt ℝ 2 f (x : F)) :
    let g := (riemannianMetricVectorSpace F).ofLE (m := ∞) le_top
    let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ, F) r) :=
      ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
    laplaceBeltrami 𝓘(ℝ, F) (fun r : U ↦ f r) x = Δ f x := by
  dsimp only
  let g := (riemannianMetricVectorSpace F).ofLE (m := ∞) le_top
  let gU := g.restrictOpenTangentSpace U
  let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ, F) r) := ⟨gU.toRiemannianMetric⟩
  let : RiemannianBundle (fun r : F ↦ TangentSpace 𝓘(ℝ, F) r) := ⟨g.toRiemannianMetric⟩
  let := Bundle.instIsContMDiffRiemannianBundle gU
  let := Bundle.instIsContMDiffRiemannianBundle g
  have h := (g.isLocalRiemannianIsometry_restrictOpenTangentSpace U).laplaceBeltrami_comp
    (u := f) (x := x) hf.contMDiffAt
  simp only [Function.comp_def] at h
  rw [h, laplaceBeltrami_eq_laplacian_of_eq
    (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _)
    ((hf.gradient_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]

/-- Restricting the Euclidean metric to an open subset of a finite-dimensional
real inner product space preserves the norm of the gradient. -/
theorem norm_mgradient_restrictOpenTangentSpace_eq_norm_gradient
    (U : Opens F) {f : F → ℝ} {x : U} (hf : DifferentiableAt ℝ f (x : F)) :
    let g := (riemannianMetricVectorSpace F).ofLE (m := ∞) le_top
    let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ, F) r) :=
      ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
    ‖mgradient 𝓘(ℝ, F) (fun r : U ↦ f r) x‖ = ‖∇ f x‖ := by
  dsimp only
  let g := (riemannianMetricVectorSpace F).ofLE (m := ∞) le_top
  let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ, F) r) :=
    ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
  let : RiemannianBundle (fun r : F ↦ TangentSpace 𝓘(ℝ, F) r) := ⟨g.toRiemannianMetric⟩
  have h := (g.isLocalRiemannianIsometry_restrictOpenTangentSpace U).norm_mgradient_comp
    (φ := f) (x := x) hf.mdifferentiableAt
  simp only [Function.comp_def] at h
  rw [h, norm_mgradient_eq_norm_gradient_of_eq
    (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _)]

end TauCeti.Manifold
