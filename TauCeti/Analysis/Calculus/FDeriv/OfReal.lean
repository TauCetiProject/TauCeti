/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Real derivatives of complexified real functions

Composing a real function `f` on a real normed space with the inclusion `ℝ → ℂ` does not change
its real derivative: `D(↑f)(x) v = ↑(Df(x) v)`. No differentiability is assumed, since both
sides vanish when `f` is not differentiable at `x`.

## Main results

* `TauCeti.fderiv_ofReal_comp_apply`: the real derivative of `y ↦ (f y : ℂ)` is the
  complexification of the real derivative of `f`.
* `ContDiffAt.hasFDerivAt_fderiv_ofReal_comp_apply`: at a `C²` point of `f`, the complexified
  directional derivative `y ↦ D(↑f)(y) u` has derivative `w ↦ ↑(D²f(x)(w, u))`.
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

/-- At a `C²` point of a real function `f`, the complexified directional derivative
`y ↦ D(↑f)(y) u` has derivative `w ↦ ↑(D²f(x)(w, u))`. -/
theorem _root_.ContDiffAt.hasFDerivAt_fderiv_ofReal_comp_apply {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (u : E) :
    HasFDerivAt (fun y ↦ fderiv ℝ (fun z ↦ (f z : ℂ)) y u)
      (ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip u)) x := by
  simpa only [fderiv_ofReal_comp_apply, Function.comp_def, ofRealCLM_apply] using
    ofRealCLM.hasFDerivAt.comp x (hf.hasFDerivAt_fderiv_apply le_rfl u)

end TauCeti
