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
import Mathlib.Tactic.Linarith

/-!
# Affine reparametrizations of a real profile

For a real profile `φ`, the function `τ ↦ φ ((A - τ) / D)` has derivative
`φ' ((A - τ) / D) * (-1 / D)` (`DifferentiableAt.hasDerivAt_comp_sub_div`). If `φ` vanishes on the
negative half-line, then `φ ((A - τ) / D) = 0` for `τ > A` (`TauCeti.comp_sub_div_eq_zero_of_lt`).
-/

public section

/-- The derivative of `τ ↦ φ ((A - τ) / D)`, for `φ` differentiable at `(A - τ) / D`. -/
theorem _root_.DifferentiableAt.hasDerivAt_comp_sub_div {φ : ℝ → ℝ} (A D τ : ℝ)
    (hφ : DifferentiableAt ℝ φ ((A - τ) / D)) :
    HasDerivAt (fun τ => φ ((A - τ) / D)) (deriv φ ((A - τ) / D) * (-1 / D)) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => (A - τ) / D) (-1 / D) τ := by
    simpa using ((hasDerivAt_id τ).const_sub A).div_const D
  exact hφ.hasDerivAt.comp τ h1

namespace TauCeti

/-- A function `φ` vanishing on the negative half-line gives `τ ↦ φ ((A - τ) / D)`, which
vanishes for `τ > A` when `D > 0`. -/
theorem comp_sub_div_eq_zero_of_lt {φ : ℝ → ℝ} (hneg : ∀ τ < 0, φ τ = 0) {D : ℝ} (hD : 0 < D)
    {A τ : ℝ} (hτ : A < τ) : φ ((A - τ) / D) = 0 :=
  hneg _ (div_neg_of_neg_of_pos (by linarith) hD)

end TauCeti
