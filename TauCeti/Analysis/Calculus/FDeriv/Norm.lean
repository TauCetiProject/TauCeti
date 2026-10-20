/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivatives and norms

A map whose norm is locally constant has derivative orthogonal to its value. In particular, the
derivative of a map into a sphere is tangent to the sphere.
-/

public section

open Filter
open scoped Topology RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A map whose norm is constant near `w` has Fréchet derivative at `w` orthogonal to its
value. In particular, the derivative of a map into a sphere is tangent to the sphere.
At nondifferentiable points, the Fréchet derivative is zero by definition. -/
theorem inner_fderiv_eq_zero_of_eventually_norm_eq {ψ : E → F} {w : E}
    (hψ : ∀ᶠ y in 𝓝 w, ‖ψ y‖ = ‖ψ w‖) (u : E) :
    ⟪ψ w, fderiv ℝ ψ w u⟫ = 0 := by
  by_cases hd : DifferentiableAt ℝ ψ w
  · have h₁ := HasFDerivAt.norm_sq hd.hasFDerivAt
    have h₂ : HasFDerivAt (fun y => ‖ψ y‖ ^ 2) (0 : E →L[ℝ] ℝ) w :=
      (hasFDerivAt_const (‖ψ w‖ ^ 2) w).congr_of_eventuallyEq
        (hψ.mono fun y hy => by simp [hy])
    simpa using congrArg (fun L : E →L[ℝ] ℝ => L u) (h₁.unique h₂)
  · simp [fderiv_zero_of_not_differentiableAt hd]

end TauCeti
