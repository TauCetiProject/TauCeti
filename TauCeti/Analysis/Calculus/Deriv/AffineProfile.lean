/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Scaled affine reparametrizations of a real profile

For a real profile `φ`, the function `τ ↦ k * φ ((A - τ) / D)` has derivative
`k * (φ' ((A - τ) / D) * (-1 / D))` (`DifferentiableAt.hasDerivAt_mul_comp_sub_div`). If `φ` is
bounded by `L` and vanishes on the negative half-line, then this function is bounded by `|k| * L`
and vanishes for `τ > A` (`TauCeti.abs_mul_comp_sub_div_le`).
-/

public section

/-- The derivative of `τ ↦ k * φ ((A - τ) / D)`, for `φ` differentiable at `(A - τ) / D`. -/
theorem _root_.DifferentiableAt.hasDerivAt_mul_comp_sub_div {φ : ℝ → ℝ} (k A D τ : ℝ)
    (hφ : DifferentiableAt ℝ φ ((A - τ) / D)) :
    HasDerivAt (fun τ => k * φ ((A - τ) / D)) (k * (deriv φ ((A - τ) / D) * (-1 / D))) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => (A - τ) / D) (-1 / D) τ := by
    simpa using ((hasDerivAt_id τ).const_sub A).div_const D
  exact (hφ.hasDerivAt.comp τ h1).const_mul k

namespace TauCeti

/-- A function `φ` bounded by `L` and vanishing on the negative half-line gives
`τ ↦ k * φ ((A - τ) / D)`, which is bounded by `|k| * L` and vanishes for `τ > A`. -/
theorem abs_mul_comp_sub_div_le {φ : ℝ → ℝ} {L : ℝ} (hL : ∀ τ, ‖φ τ‖ ≤ L)
    (hneg : ∀ τ < 0, φ τ = 0) {D : ℝ} (hD : 0 < D) (k A : ℝ) :
    (∀ τ, |k * φ ((A - τ) / D)| ≤ |k| * L) ∧ ∀ τ, A < τ → k * φ ((A - τ) / D) = 0 :=
  ⟨fun τ => by
    rw [abs_mul]
    gcongr
    exact (Real.norm_eq_abs _).symm.le.trans (hL _),
  fun τ hτ => by rw [hneg _ (div_neg_of_neg_of_pos (by linarith) hD), mul_zero]⟩

end TauCeti
