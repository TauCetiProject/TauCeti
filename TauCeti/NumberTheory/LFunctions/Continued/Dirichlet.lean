/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Dirichlet.Basic

/-!
# The continued function of a primitive Dirichlet record

For every primitive Dirichlet character `χ` modulo `N`, removing the conductor and gamma factors
from `dirichletData χ hχ` gives Mathlib's `χ.LFunction` at every point of `ℂ`.

* At `N = 1` the record is `riemannZetaData` and `χ.LFunction = riemannZeta`, including the
  removable value `-1 / 2` at zero.
* At `N ≠ 1` the record has no poles, so the continued function is the raw product, which is
  `χ.completedLFunction s / χ.gammaFactor s` by Mathlib's
  `DirichletCharacter.LFunction_eq_completed_div_gammaFactor`, also at the gamma poles.

The comparison follows Christian Merten's earlier construction in Tau Ceti PR #41996,
transported to the canonical `AnalyticLFunctionData.continuedL`.
-/

public section

open Complex

namespace TauCeti.LFunctions

/-- **The continued function of a primitive Dirichlet record is `χ.LFunction`**, for the
principal character modulo `1` as well as every nonprincipal primitive character. -/
@[simp]
theorem dirichletData_continuedL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) : (dirichletData χ hχ).continuedL = χ.LFunction := by
  by_cases hN : N = 1
  · subst N
    rw [dirichletData_modOne, riemannZetaData_continuedL, DirichletCharacter.LFunction_modOne_eq]
  · funext s
    rw [(dirichletData_hasMeromorphicContinuation χ hχ).continuedL_eq (by simp [hN]),
      χ.LFunction_eq_completed_div_gammaFactor s (.inr hN)]
    simp [AnalyticLFunctionData.uncompletedProduct_def, AnalyticLFunctionData.invGammaFactor_def,
      ← mul_assoc, ← cpow_add _ _ (Nat.cast_ne_zero.mpr (NeZero.ne N)), div_eq_mul_inv]

/-! ### Checks -/

/-- For a nonprincipal primitive character the continued function is entire. -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    Differentiable ℂ (dirichletData χ hχ).continuedL := by
  rw [dirichletData_continuedL]
  exact DirichletCharacter.differentiable_LFunction hne

/-- The dual record recovers the L-function of the inverse character. -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (dirichletData χ hχ).dual.continuedL = χ⁻¹.LFunction := by
  rw [dirichletData_dual, dirichletData_continuedL]

/-- At `N = 1` the cancelled pole at zero carries the value `ζ(0) = -1 / 2`. -/
example (χ : DirichletCharacter ℂ 1) (hχ : χ.IsPrimitive) :
    (dirichletData χ hχ).continuedL 0 = -1 / 2 := by
  simp [riemannZeta_zero]

end TauCeti.LFunctions
