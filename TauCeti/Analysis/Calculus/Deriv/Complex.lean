/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Real coordinate slices of complex-domain functions

A real Fréchet derivative determines the derivatives of the horizontal and vertical slices.
-/

public section

namespace HasFDerivAt

/-- A real Fréchet derivative gives the derivative of the horizontal coordinate slice. -/
theorem hasDerivAt_re_slice {P : ℂ → ℝ} {L : ℂ →L[ℝ] ℝ} {z : ℂ}
    (hP : HasFDerivAt P L z) :
    HasDerivAt (fun x : ℝ ↦ P ⟨x, z.im⟩) (L 1) z.re := by
  have hp := Complex.equivRealProdCLM.symm.hasFDerivAt (x := (z.re, z.im)) |>.comp_hasDerivAt z.re
    ((hasDerivAt_id z.re).prodMk (hasDerivAt_const z.re z.im))
  convert hP.comp_hasDerivAt z.re hp using 1
  · ext x
    apply congrArg P
    simp only [Function.comp_apply, id_eq, Complex.equivRealProdCLM_symm_apply]
    apply Complex.ext <;> simp
  · simp [Complex.equivRealProdCLM_symm_apply]

/-- A real Fréchet derivative gives the derivative of the vertical coordinate slice. -/
theorem hasDerivAt_im_slice {P : ℂ → ℝ} {L : ℂ →L[ℝ] ℝ} {z : ℂ}
    (hP : HasFDerivAt P L z) :
    HasDerivAt (fun y : ℝ ↦ P ⟨z.re, y⟩) (L Complex.I) z.im := by
  have hp := Complex.equivRealProdCLM.symm.hasFDerivAt (x := (z.re, z.im)) |>.comp_hasDerivAt z.im
    ((hasDerivAt_const z.im z.re).prodMk (hasDerivAt_id z.im))
  convert hP.comp_hasDerivAt z.im hp using 1
  · ext y
    apply congrArg P
    simp only [Function.comp_apply, Complex.equivRealProdCLM_symm_apply]
    apply Complex.ext <;> simp
  · simp [Complex.equivRealProdCLM_symm_apply]

end HasFDerivAt
