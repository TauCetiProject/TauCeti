/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Real derivatives of complexified real functions

Composing a real function `f` on a real normed space with the inclusion `ℝ → ℂ` does not change
its real derivative: `D(↑f)(x) v = ↑(Df(x) v)`. No differentiability is assumed, since both
sides vanish when `f` is not differentiable at `x`.

## Main results

* `TauCeti.fderiv_ofReal_comp_apply`: the real derivative of `y ↦ (f y : ℂ)` is the
  complexification of the real derivative of `f`.
-/

public section

open Complex

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Composing a real function with the inclusion `ℝ → ℂ` does not change its real derivative.
No differentiability is assumed: both sides vanish when `f` is not differentiable at `x`. -/
@[simp]
theorem fderiv_ofReal_comp_apply (f : E → ℝ) (x v : E) :
    fderiv ℝ (fun y ↦ (f y : ℂ)) x v = fderiv ℝ f x v := by
  by_cases hf : DifferentiableAt ℝ f x
  · have h : HasFDerivAt (fun y ↦ (f y : ℂ)) (ofRealCLM.comp (fderiv ℝ f x)) x :=
      ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt
    simp [h.fderiv]
  · have hf' : ¬DifferentiableAt ℝ (fun y ↦ (f y : ℂ)) x := fun h ↦ by
      have hre := reCLM.differentiableAt.comp x h
      exact hf (by simpa [Function.comp_def] using hre)
    simp [fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt hf']

end TauCeti
