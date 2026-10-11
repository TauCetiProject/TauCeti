/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Directional derivatives of test functions

Mathlib equips the test functions `𝓓(Ω, F)` with the directional derivative `∂_{v}`. This file
evaluates it pointwise as the classical directional derivative, and shows that two directional
derivatives of a test function commute, `∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ)`, because the second
derivative of a smooth function is symmetric. Moving derivatives between the two sides of an
integration-by-parts identity uses exactly this, for instance to show that weak derivatives
commute.

## Main declarations

* `TestFunction.lineDerivOp_apply`: `∂_{v} φ` is the classical directional derivative of `φ`.
* `TestFunction.lineDerivOp_comm` and `TestFunction.lineDeriv_lineDerivOp_comm`: directional
  derivatives of test functions commute.
-/

public section

namespace TestFunction

open LineDeriv TopologicalSpace
open scoped Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- The directional derivative of a test function is its classical directional derivative. -/
@[simp]
theorem lineDerivOp_apply (φ : 𝓓(Ω, F)) (v x : E) : ∂_{v} φ x = lineDeriv ℝ φ x v :=
  lineDerivCLM_apply_of_le le_top

/-- **Directional derivatives of test functions commute.** -/
theorem lineDerivOp_comm (φ : 𝓓(Ω, F)) (v w : E) : ∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ) := by
  have hφ : ∀ u y, lineDeriv ℝ (φ : E → F) y u = fderiv ℝ (φ : E → F) y u := fun u y =>
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv
  have hφ' : ∀ u u' y, lineDeriv ℝ (fun z => fderiv ℝ (φ : E → F) z u) y u' =
      fderiv ℝ (fderiv ℝ (φ : E → F)) y u' u := fun u u' y => by
    have hd : DifferentiableAt ℝ (fderiv ℝ (φ : E → F)) y :=
      (φ.contDiff.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero y
    rw [(hd.clm_apply (differentiableAt_const u)).lineDeriv_eq_fderiv, fderiv_clm_apply hd
      (differentiableAt_const u)]
    simp
  have hcoe : ∀ u, ⇑(∂_{u} φ : 𝓓(Ω, F)) = fun y => fderiv ℝ (φ : E → F) y u := fun u =>
    funext fun y => (lineDerivOp_apply φ u y).trans (hφ u y)
  ext x
  rw [lineDerivOp_apply, lineDerivOp_apply, hcoe, hcoe, hφ', hφ']
  exact ((φ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)).eq v w

/-- The classical directional derivative of `∂_{v} φ` in the direction `w` is that of `∂_{w} φ`
in the direction `v`. -/
theorem lineDeriv_lineDerivOp_comm (φ : 𝓓(Ω, F)) (v w x : E) :
    lineDeriv ℝ (∂_{v} φ : 𝓓(Ω, F)) x w = lineDeriv ℝ (∂_{w} φ : 𝓓(Ω, F)) x v := by
  rw [← lineDerivOp_apply, ← lineDerivOp_apply, lineDerivOp_comm]

end TestFunction
