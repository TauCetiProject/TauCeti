/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import TauCeti.NumberTheory.LFunctions.Data.Basic
public import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta

/-!
# The completed L-function card of the Riemann zeta function

The Riemann zeta function is the basic example of completed L-function data: its coefficients
are those of the arithmetic function `ArithmeticFunction.zeta`, that is, `1` at every positive
index, its conductor is `1`, it has the single real gamma shift `0` and no complex one, so
its gamma factor is `Γ_ℝ(s) = π^(-s/2) Γ(s/2)` and its degree is `1`, its root number is `1`, its
completed function is Mathlib's `completedRiemannZeta`, and its polar divisor consists of the
simple poles at `0` and `1`.

This file defines that card, `TauCeti.LFunctions.riemannZetaData`, shows that it is its own dual,
and proves that it satisfies `HasDirichletAgreement`, `HasMeromorphicContinuation` and
`HasFunctionalEquation`. The analytic input is the meromorphy and the simple poles of
`completedRiemannZeta` (`TauCeti.NumberTheory.LSeries.CompletedRiemannZeta`) and, from Mathlib,
the functional equation `completedRiemannZeta_one_sub`, the reflection symmetry
`completedRiemannZeta_conj`, and the Dirichlet series
`ArithmeticFunction.LSeries_zeta_eq_riemannZeta`.

## Main results

* `TauCeti.LFunctions.riemannZetaData`: the card of the Riemann zeta function.
* `riemannZetaData_dual`: the card is self-dual.
* `riemannZetaData_hasDirichletAgreement`, `riemannZetaData_hasMeromorphicContinuation`,
  `riemannZetaData_hasFunctionalEquation`.
-/

public section

open Complex ComplexConjugate

namespace TauCeti.LFunctions

/-- **The Riemann zeta card.** Coefficients `ArithmeticFunction.zeta`, conductor `1`, the single
real gamma shift `0` and no complex gamma shift, root number `1`, completed function
`completedRiemannZeta`, and simple poles at `0` and `1`. -/
noncomputable def riemannZetaData : AnalyticLFunctionData where
  coeff n := ArithmeticFunction.zeta n
  conductor := 1
  gammaR := {0}
  gammaC := 0
  rootNumber := 1
  completed := completedRiemannZeta
  polarOrder := Finsupp.single 0 1 + Finsupp.single 1 1

@[simp]
theorem riemannZetaData_coeff (n : ℕ) :
    riemannZetaData.coeff n = ArithmeticFunction.zeta n := (rfl)

@[simp]
theorem riemannZetaData_conductor : riemannZetaData.conductor = 1 := (rfl)

@[simp]
theorem riemannZetaData_gammaR : riemannZetaData.gammaR = {0} := (rfl)

@[simp]
theorem riemannZetaData_gammaC : riemannZetaData.gammaC = 0 := (rfl)

@[simp]
theorem riemannZetaData_rootNumber : riemannZetaData.rootNumber = 1 := (rfl)

@[simp]
theorem riemannZetaData_completed : riemannZetaData.completed = completedRiemannZeta := (rfl)

@[simp]
theorem riemannZetaData_polarOrder :
    riemannZetaData.polarOrder = Finsupp.single 0 1 + Finsupp.single 1 1 := (rfl)

@[simp]
theorem riemannZetaData_degree : riemannZetaData.degree = 1 := by
  simp [AnalyticLFunctionData.degree_def]

@[simp]
theorem riemannZetaData_gammaFactor (s : ℂ) : riemannZetaData.gammaFactor s = Gammaℝ s := by
  simp [AnalyticLFunctionData.gammaFactor_def]

/-- The Riemann zeta card is its own dual. -/
@[simp]
theorem riemannZetaData_dual : riemannZetaData.dual = riemannZetaData := by
  ext
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp [completedRiemannZeta_conj]
  · simp [Finsupp.single_apply, eq_comm (a := (0 : ℂ)), eq_comm (a := (1 : ℂ)),
      map_eq_one_iff _ (starRingEnd ℂ).injective]

/-- On `Re s > 1`, the completed Riemann zeta function is `Γ_ℝ(s) ζ(s)`, the completion of the
Dirichlet series with all coefficients `1`. -/
theorem riemannZetaData_hasDirichletAgreement : riemannZetaData.HasDirichletAgreement where
  coeff_one := by simp
  degree_pos := by simp
  completed_eq s hs := by
    have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hs0 : s ≠ 0 := by
      rintro rfl
      norm_num at hs
    have hL : LSeries riemannZetaData.coeff s = riemannZeta s :=
      ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
    rw [hL, riemannZeta_def_of_ne_zero hs0]
    simp [field]

/-- The completed Riemann zeta function is meromorphic, with simple poles at `0` and `1` and no
others. -/
theorem riemannZetaData_hasMeromorphicContinuation :
    riemannZetaData.HasMeromorphicContinuation where
  meromorphic := meromorphic_completedRiemannZeta
  meromorphicOrderAt_eq p hp := by
    by_cases h0 : p = 0
    · subst h0
      simp [meromorphicOrderAt_completedRiemannZeta_zero]
    by_cases h1 : p = 1
    · subst h1
      simp [meromorphicOrderAt_completedRiemannZeta_one]
    simp [Ne.symm h0, Ne.symm h1] at hp
  analyticAt p hp := by
    refine analyticAt_completedRiemannZeta ?_ ?_ <;> rintro rfl <;> simp at hp

/-- The functional equation `Λ(s) = Λ(1 - s)` of the completed Riemann zeta function, with root
number `1`. -/
theorem riemannZetaData_hasFunctionalEquation : riemannZetaData.HasFunctionalEquation where
  norm_rootNumber := by simp
  polarOrder_one_sub_conj s := by
    have hconj (z : ℂ) : riemannZetaData.polarOrder (conj z) = riemannZetaData.polarOrder z := by
      rw [← AnalyticLFunctionData.dual_polarOrder_apply, riemannZetaData_dual]
    have e0 : (0 : ℂ) = 1 - s ↔ 1 = s := by rw [eq_comm, sub_eq_zero]
    have e1 : (1 : ℂ) = 1 - s ↔ 0 = s := by rw [eq_comm, sub_eq_self, eq_comm]
    rw [← map_one (starRingEnd ℂ), ← map_sub, hconj]
    simp only [riemannZetaData_polarOrder, Finsupp.add_apply, Finsupp.single_apply, e0, e1]
    rw [add_comm]
  completed_eq s _ _ := by
    rw [riemannZetaData_dual, riemannZetaData_rootNumber, one_mul, riemannZetaData_completed,
      completedRiemannZeta_one_sub]

end TauCeti.LFunctions
