/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# The complex `1`-form `dz`

This file defines `TauCeti.dzForm`, the complex-valued real `1`-form `dz` on `ℂ`, so that a complex
function `g` gives the `1`-form `g dz`, and computes the exterior derivative of `g dz`:
`d(g dz)(v, w) = dg(v) w - dg(w) v` (`TauCeti.extDeriv_smul_dzForm_apply`). In particular `g dz` is
closed where `g` is complex differentiable (`DifferentiableAt.extDeriv_smul_dzForm`).
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

/-- The exterior derivative of `g dz` on a pair of vectors: `d(g dz)(v, w) = dg(v) w - dg(w) v`.
Both sides vanish when `g` is not real differentiable at `z`. -/
theorem extDeriv_smul_dzForm_apply (g : ℂ → ℂ) (z v w : ℂ) :
    extDeriv (fun y ↦ g y • dzForm) z ![v, w] = fderiv ℝ g z v * w - fderiv ℝ g z w * v := by
  by_cases hg : DifferentiableAt ℝ g z
  · rw [extDeriv_apply_pair, (hg.hasFDerivAt.smul_const dzForm).fderiv]
    simp
  · have hφ : ¬ DifferentiableAt ℝ (fun y ↦ g y • dzForm) z := fun h ↦
      hg (by simpa using h.continuousAlternatingMap_apply_const fun _ ↦ (1 : ℂ))
    simp [extDeriv_zero_of_not_differentiableAt hφ, fderiv_zero_of_not_differentiableAt hg]

/-- A `1`-form `g dz` with `g` complex differentiable at `z` is closed at `z`. -/
theorem _root_.DifferentiableAt.extDeriv_smul_dzForm {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) : extDeriv (fun y ↦ g y • dzForm) z = 0 := by
  ext v
  rw [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, show v = ![v 0, v 1] from
    funext fun i ↦ by fin_cases i <;> rfl, extDeriv_smul_dzForm_apply,
    hg.fderiv_restrictScalars_eq_smul_deriv ℝ, hg.fderiv_restrictScalars_eq_smul_deriv ℝ]
  simp only [smul_eq_mul]
  ring

end TauCeti
