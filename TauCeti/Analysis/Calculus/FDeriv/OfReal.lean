/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Real derivatives of complexified real functions

Composing a real function `f` on a real normed space with the inclusion `ℝ → ℂ` does not change
its real derivative: `D(↑f)(x) v = ↑(Df(x) v)`. No differentiability is assumed, since both
sides vanish when `f` is not differentiable at `x`.

## Main results

* `TauCeti.fderiv_ofReal_comp_apply`: the real derivative of `y ↦ (f y : ℂ)` is the
  complexification of the real derivative of `f`.
* `DifferentiableAt.ofReal_comp`, `TauCeti.norm_fderiv_ofReal_comp_le`: `y ↦ (f y : ℂ)` is
  differentiable where `f` is, and its real derivative has norm at most `‖Df(x)‖`.
* `ContDiffAt.hasFDerivAt_fderiv_ofReal_comp_apply`: at a `C²` point of `f`, the complexified
  directional derivative `y ↦ D(↑f)(y) u` has derivative `w ↦ ↑(D²f(x)(w, u))`.
* `DifferentiableAt.fderiv_ofReal_add_ofReal_mul_I_apply`, `ContDiff.ofReal_add_ofReal_mul_I`,
  `HasCompactSupport.ofReal_add_ofReal_mul_I`: the complex function `f + i g` assembled from real
  functions `f, g` has derivative `Df + i Dg`, and inherits the smoothness and compact support of
  `f` and `g`.
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

/-- A real function differentiable at `x` stays differentiable at `x` after composing with the
inclusion `ℝ → ℂ`. -/
theorem _root_.DifferentiableAt.ofReal_comp {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y ↦ (f y : ℂ)) x :=
  ofRealCLM.differentiableAt.comp x hf

/-- The real derivative of `y ↦ (f y : ℂ)` has norm at most that of the real derivative of `f`. -/
theorem norm_fderiv_ofReal_comp_le (f : E → ℝ) (x : E) :
    ‖fderiv ℝ (fun y ↦ (f y : ℂ)) x‖ ≤ ‖fderiv ℝ f x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w ↦ ?_
  rw [fderiv_ofReal_comp_apply, Complex.norm_real]
  exact (fderiv ℝ f x).le_opNorm w

/-- At a `C²` point of a real function `f`, the complexified directional derivative
`y ↦ D(↑f)(y) u` has derivative `w ↦ ↑(D²f(x)(w, u))`. -/
theorem _root_.ContDiffAt.hasFDerivAt_fderiv_ofReal_comp_apply {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (u : E) :
    HasFDerivAt (fun y ↦ fderiv ℝ (fun z ↦ (f z : ℂ)) y u)
      (ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip u)) x := by
  simpa only [fderiv_ofReal_comp_apply, Function.comp_def, ofRealCLM_apply] using
    ofRealCLM.hasFDerivAt.comp x (hf.hasFDerivAt_fderiv_apply le_rfl u)

/-- For real functions `f, g` differentiable at `x`, the real derivative of `f + i g` is
`Df + i Dg`. -/
theorem _root_.DifferentiableAt.fderiv_ofReal_add_ofReal_mul_I_apply {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y ↦ (f y : ℂ) + (g y : ℂ) * I) x v =
      (fderiv ℝ f x v : ℂ) + (fderiv ℝ g x v : ℂ) * I := by
  rw [fderiv_fun_add hf.ofReal_comp (hg.ofReal_comp.mul_const I),
    fderiv_mul_const hg.ofReal_comp]
  simp [mul_comm]

/-- For real `Cⁿ` functions `f, g`, the complex function `f + i g` is `Cⁿ`. -/
theorem _root_.ContDiff.ofReal_add_ofReal_mul_I {n : WithTop ℕ∞} {f g : E → ℝ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n fun y ↦ (f y : ℂ) + (g y : ℂ) * I :=
  (ofRealCLM.contDiff.comp hf).add ((ofRealCLM.contDiff.comp hg).mul contDiff_const)

/-- For compactly supported real functions `f, g`, the complex function `f + i g` is compactly
supported. -/
theorem _root_.HasCompactSupport.ofReal_add_ofReal_mul_I {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport fun y ↦ (f y : ℂ) + (g y : ℂ) * I :=
  (hf.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero).add
    ((hg.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero).mul_right)

end TauCeti
