/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Restriction.NormedSpace

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
theorem laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv
    (U : Opens ℝ) {f : ℝ → ℝ} {x : U} (hf : ContDiffAt ℝ 2 f (x : ℝ)) :
    let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
    let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
      ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
    laplaceBeltrami 𝓘(ℝ) (fun r : U ↦ f r) x = deriv (deriv f) x := by
  dsimp only
  rw [laplaceBeltrami_restrictOpenTangentSpace_eq_laplacian U hf,
    InnerProductSpace.laplacian_eq_iteratedDeriv_real]
  simp [iteratedDeriv_succ]

/-- The squared gradient norm for the restricted Euclidean metric on an open
subset of `ℝ` is the square of the ordinary derivative. -/
theorem sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv
    (U : Opens ℝ) {f : ℝ → ℝ} {x : U} (hf : DifferentiableAt ℝ f (x : ℝ)) :
    let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
    let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) :=
      ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
    ‖mgradient 𝓘(ℝ) (fun r : U ↦ f r) x‖ ^ 2 = deriv f x ^ 2 := by
  dsimp only
  rw [norm_mgradient_restrictOpenTangentSpace_eq_norm_gradient U hf,
    gradient_eq_deriv', Real.norm_eq_abs, sq_abs]

end TauCeti.Manifold
