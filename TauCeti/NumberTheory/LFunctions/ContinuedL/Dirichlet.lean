/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.ContinuedL.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Dirichlet.Basic

/-!
# The continued L-function of a primitive Dirichlet record

For every primitive Dirichlet character `χ` modulo `N`, `(dirichletData χ hχ).continuedL` equals
Mathlib's `χ.LFunction` on all of `ℂ`:

* When `N = 1`, `dirichletData χ hχ = riemannZetaData` and `χ.LFunction = riemannZeta`.
* When `N ≠ 1`, `(dirichletData χ hχ).polarOrder = 0`, so `continuedL` reduces to the pointwise
  quotient `χ.completedLFunction s / χ.gammaFactor s`, matching
  `DirichletCharacter.LFunction_eq_completed_div_gammaFactor` everywhere (including at gamma poles).
-/

public section

open Complex

namespace TauCeti.LFunctions

/-- **The continued L-function of `dirichletData χ hχ` is `χ.LFunction`**, for every primitive
Dirichlet character `χ` (both principal modulo `1` and nonprincipal). -/
@[simp]
theorem dirichletData_continuedL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) : (dirichletData χ hχ).continuedL = χ.LFunction := by
  by_cases hN : N = 1
  · subst N
    rw [dirichletData_modOne, riemannZetaData_continuedL, DirichletCharacter.LFunction_modOne_eq]
  · ext s
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have hpow : (N : ℂ) ^ (-s / 2) * (N : ℂ) ^ (s / 2) = 1 := by
      rw [← cpow_add _ _ hN0]
      have hz : -s / 2 + s / 2 = 0 := by ring
      rw [hz, cpow_zero]
    rw [(dirichletData χ hχ).continuedL_eq_of_polarOrder_eq_zero (by simp [hN]),
      dirichletData_conductor, PNat.mk_coe, dirichletData_completed,
      AnalyticLFunctionData.invGammaFactor_def, dirichletData_gammaFactor, ← mul_assoc, hpow,
      one_mul, ← div_eq_mul_inv, ← χ.LFunction_eq_completed_div_gammaFactor s (.inr hN)]

/-! ### Checks -/

/-- For a nonprincipal primitive character `χ ≠ 1`, `(dirichletData χ hχ).continuedL` is entire. -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    Differentiable ℂ (dirichletData χ hχ).continuedL := by
  rw [dirichletData_continuedL]
  exact DirichletCharacter.differentiable_LFunction hne

/-- On the dual record `(dirichletData χ hχ).dual`, `continuedL` recovers the L-function
`χ⁻¹.LFunction` of the inverse character. -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (dirichletData χ hχ).dual.continuedL = χ⁻¹.LFunction := by
  rw [dirichletData_dual, dirichletData_continuedL]

end TauCeti.LFunctions
