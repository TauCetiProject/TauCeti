/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear

/-!
# Derivatives and norms

A map whose norm is locally constant has derivative orthogonal to its value. In particular, the
derivative of a map into a sphere is tangent to the sphere.

The squared norm of the derivative of a map from `ℂ` to a Euclidean space is at most twice the
sum of the squared partial derivatives of its components along `1` and `I`
(`TauCeti.norm_fderiv_sq_le_two_mul_sum_sq`).
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

/-- The squared operator norm of the derivative of a map from `ℂ` to a Euclidean space is at most
twice the sum, over the components, of the squared partial derivatives along `1` and `I`. -/
theorem norm_fderiv_sq_le_two_mul_sum_sq {ι : Type*} [Fintype ι] (u : ℂ → EuclideanSpace ℝ ι)
    (z : ℂ) :
    ‖fderiv ℝ u z‖ ^ 2 ≤
      2 * ∑ i, (fderiv ℝ (fun w ↦ u w i) z 1 ^ 2 + fderiv ℝ (fun w ↦ u w i) z Complex.I ^ 2) := by
  by_cases hu : DifferentiableAt ℝ u z
  swap
  · rw [fderiv_zero_of_not_differentiableAt hu, norm_zero, zero_pow two_ne_zero]
    positivity
  have hD := (fderiv ℝ u z).opNorm_sq_le_card_mul_sum_norm_apply_sq_orthonormalBasis
    Complex.orthonormalBasisOneI
  simp only [Fintype.card_fin, Nat.cast_ofNat, Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hD
  -- The squared norm of a directional derivative is the sum over the components.
  have hcomp (v : ℂ) : ‖fderiv ℝ u z v‖ ^ 2 = ∑ i, fderiv ℝ (fun w ↦ u w i) z v ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h : HasFDerivAt (fun w ↦ u w i) ((EuclideanSpace.proj i).comp (fderiv ℝ u z)) z :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z hu.hasFDerivAt
    rw [h.fderiv]
    rfl
  rwa [hcomp, hcomp, ← Finset.sum_add_distrib] at hD

end TauCeti
