/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# The complex `1`-form `dz`

This file defines `TauCeti.dzForm`, the complex-valued real `1`-form `dz` on `ℂ`, so that a complex
function `g` gives the `1`-form `g dz`, and computes the exterior derivative of `g dz`:
`d(g dz)(v, w) = dg(v) w - dg(w) v` (`TauCeti.extDeriv_smul_dzForm_apply`).
-/

public section

noncomputable section

namespace TauCeti

/-- The complex-valued real `1`-form `dz` on `ℂ`: the identity of `ℂ`, as a real linear map. A
complex function `g` gives the `1`-form `g dz`, written `fun z ↦ g z • dzForm`. -/
def dzForm : ℂ [⋀^Fin 1]→L[ℝ] ℂ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℂ (0 : Fin 1) (ContinuousLinearMap.id ℝ ℂ)

@[simp]
theorem dzForm_apply (v : Fin 1 → ℂ) : dzForm v = v 0 := by
  simp [dzForm]

/-- The exterior derivative of `g dz` on a pair of vectors: `d(g dz)(v, w) = dg(v) w - dg(w) v`. -/
theorem extDeriv_smul_dzForm_apply {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z) (v w : ℂ) :
    extDeriv (fun y ↦ g y • dzForm) z ![v, w] = fderiv ℝ g z v * w - fderiv ℝ g z w * v := by
  rw [extDeriv_apply_pair, (hg.hasFDerivAt.smul_const dzForm).fderiv]
  simp

end TauCeti
