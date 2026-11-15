/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Real coordinate slices of complex-domain functions

A real Fréchet derivative determines the derivatives of the horizontal and vertical slices.
-/

public section

namespace HasFDerivAt

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousAdd F]
  [ContinuousSMul ℝ F] {P : ℂ → F} {L : ℂ →L[ℝ] F} {z : ℂ}

/-- A real Fréchet derivative gives the derivative of the horizontal coordinate slice. -/
theorem hasDerivAt_re_slice (hP : HasFDerivAt P L z) :
    HasDerivAt (fun x : ℝ ↦ P ⟨x, z.im⟩) (L 1) z.re := by
  have h : HasDerivAt (fun x : ℝ ↦ (⟨x, z.im⟩ : ℂ)) 1 z.re := by
    simpa [Complex.mk_eq_add_mul_I] using
      (Complex.ofRealCLM.hasDerivAt (x := z.re)).add_const (z.im * Complex.I)
  simpa [hasDerivAt_iff_hasFDerivAt, ContinuousLinearMap.comp_toSpanSingleton, Function.comp_def]
    using HasFDerivAt.comp z.re hP h.hasFDerivAt

/-- A real Fréchet derivative gives the derivative of the vertical coordinate slice. -/
theorem hasDerivAt_im_slice (hP : HasFDerivAt P L z) :
    HasDerivAt (fun y : ℝ ↦ P ⟨z.re, y⟩) (L Complex.I) z.im := by
  have h : HasDerivAt (fun y : ℝ ↦ (⟨z.re, y⟩ : ℂ)) Complex.I z.im := by
    simpa [Complex.mk_eq_add_mul_I] using
      ((Complex.ofRealCLM.hasDerivAt (x := z.im)).mul_const Complex.I).const_add (z.re : ℂ)
  simpa [hasDerivAt_iff_hasFDerivAt, ContinuousLinearMap.comp_toSpanSingleton, Function.comp_def]
    using HasFDerivAt.comp z.im hP h.hasFDerivAt

end HasFDerivAt
