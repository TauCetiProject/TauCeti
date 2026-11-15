/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.ContinuedL.Basic
public import TauCeti.NumberTheory.LFunctions.ContinuedL.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Dirichlet.Basic

/-!
# The continued L-function of a primitive Dirichlet record

For every primitive Dirichlet character `χ` modulo `N`, `(dirichletData χ hχ).continuedL` equals
Mathlib's `χ.LFunction` on all of `ℂ`:

* When `N = 1`, `dirichletData χ hχ = riemannZetaData` and `χ.LFunction = riemannZeta`.
* When `N ≠ 1`, `χ ≠ 1` has `polarOrder = 0`, so both `(dirichletData χ hχ).continuedL` and
  `χ.LFunction` are entire and agree with the Dirichlet series `LSeries (↗χ)` on `1 < s.re`.
-/

public section

open Complex Set Topology

namespace TauCeti.LFunctions

section General

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-- **The continued L-function of `dirichletData χ hχ` is `χ.LFunction`**, for every primitive
Dirichlet character `χ` (both principal modulo `1` and nonprincipal). -/
@[simp]
theorem dirichletData_continuedL : (dirichletData χ hχ).continuedL = χ.LFunction := by
  by_cases hN : N = 1
  · subst N
    rw [dirichletData_modOne, riemannZetaData_continuedL, DirichletCharacter.LFunction_modOne_eq]
  · have hne : χ ≠ 1 := fun h1 ↦ hN (hχ.eq_one_iff.mp h1)
    have hmc := dirichletData_hasMeromorphicContinuation χ hχ
    have hda := dirichletData_hasDirichletAgreement χ hχ
    have han_cont : AnalyticOnNhd ℂ (dirichletData χ hχ).continuedL univ := fun z _ ↦
      hmc.analyticAt_continuedL_of_polarOrder_eq_zero (by simp [hN])
    have han_L : AnalyticOnNhd ℂ χ.LFunction univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (DirichletCharacter.differentiable_LFunction hne)
    have hev : (dirichletData χ hχ).continuedL =ᶠ[𝓝 (2 : ℂ)] χ.LFunction := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
      rw [hda.continuedL_eq_LSeries hmc hz, DirichletCharacter.LFunction_eq_LSeries χ hz]
      exact LSeries_congr (fun {n} hn ↦ dirichletData_coeff_of_ne_zero χ hχ hn) z
    exact funext fun s ↦
      han_cont.eqOn_of_preconnected_of_eventuallyEq han_L isPreconnected_univ (mem_univ (2 : ℂ))
        hev (mem_univ s)

/-- Pointwise form of `dirichletData_continuedL`. -/
theorem dirichletData_continuedL_apply (s : ℂ) :
    (dirichletData χ hχ).continuedL s = χ.LFunction s :=
  congrFun (dirichletData_continuedL χ hχ) s

/-- For a nonprincipal primitive character `χ ≠ 1`, `(dirichletData χ hχ).continuedL` is entire. -/
theorem differentiable_dirichletData_continuedL (hne : χ ≠ 1) :
    Differentiable ℂ (dirichletData χ hχ).continuedL := by
  rw [dirichletData_continuedL]
  exact DirichletCharacter.differentiable_LFunction hne

end General

/-! ### Checks -/

/-- For a non-real primitive character (such as a character whose square is nontrivial), `d.dual`
carries the conjugate character `χ⁻¹ ≠ χ`, so the asymmetric functional equation relates `χ` to
`χ⁻¹` rather than to `χ` itself. -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (dirichletData χ hχ).dual.continuedL = χ⁻¹.LFunction := by
  rw [dirichletData_dual, dirichletData_continuedL]

end TauCeti.LFunctions
