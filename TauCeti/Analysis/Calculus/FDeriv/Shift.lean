/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add

import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# The derivative under a point reflection of the domain

Mathlib computes the derivative of `x ↦ f (x + a)` (`fderiv_comp_add_right`) for maps between
normed spaces, and the derivative of `x ↦ f (a - x)` for functions of one variable
(`deriv_comp_const_sub`). This file records the derivative of `x ↦ f (a - x)` for maps between
normed spaces: it is minus the derivative of `f` at `a - x`, with no differentiability
hypothesis, since `x ↦ a - x` is an affine isomorphism.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x : E}

/-- The derivative of `x ↦ f (a - x)` at `x` is minus the derivative of `f` at `a - x`. -/
theorem fderiv_comp_const_sub (a : E) :
    fderiv 𝕜 (fun x ↦ f (a - x)) x = -fderiv 𝕜 f (a - x) := by
  have h := (ContinuousLinearEquiv.neg 𝕜 : E ≃L[𝕜] E).comp_right_fderiv
    (f := fun y ↦ f (y + a)) (x := x)
  simp only [Function.comp_def, ContinuousLinearEquiv.coe_neg, Pi.neg_apply, id_eq,
    neg_add_eq_sub, fderiv_comp_add_right] at h
  rw [h]
  ext v
  simp

end TauCeti
