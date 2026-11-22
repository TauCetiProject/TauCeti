/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import TauCeti.NumberTheory.LFunctions.Data.Series
public import TauCeti.NumberTheory.LFunctions.Data.Growth
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
and proves that it satisfies `HasDirichletAgreement`, `HasMeromorphicContinuation`,
`HasFunctionalEquation` and `HasAverageCoefficientGrowth`. The analytic input is the meromorphy
and the simple poles of `completedRiemannZeta`
(`TauCeti.NumberTheory.LSeries.CompletedRiemannZeta`) and, from Mathlib, the functional equation
`completedRiemannZeta_one_sub`, the reflection symmetry `completedRiemannZeta_conj`,
and the Dirichlet series
`ArithmeticFunction.LSeries_zeta_eq_riemannZeta`.

## Main results

* `TauCeti.LFunctions.riemannZetaData`: the card of the Riemann zeta function.
* `riemannZetaData_dual`: the card is self-dual.
* `riemannZetaData_hasDirichletAgreement`, `riemannZetaData_hasMeromorphicContinuation`,
  `riemannZetaData_hasFunctionalEquation`.
* `ofSeries_riemannZetaData`: the canonical series construction recovers this card after
  normalizing the completed function at its poles; in particular its root number is `1`.
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

/-- The Riemann zeta coefficients satisfy the average absolute growth bound. -/
theorem riemannZetaData_hasAverageCoefficientGrowth :
    riemannZetaData.HasAverageCoefficientGrowth := by
  apply AnalyticLFunctionData.hasAverageCoefficientGrowth_of_norm_coeff_le
  exact ⟨1, fun n hn ↦ by simp [hn]⟩

/-- The support of the simple-pole divisor `Finsupp.single 0 1 + Finsupp.single 1 1` is
`{0, 1}`. -/
theorem support_single_zero_add_single_one {α : Type*} [Zero α] [One α] [DecidableEq α] :
    (Finsupp.single (0 : α) (1 : ℕ) + Finsupp.single 1 1).support = {0, 1} := by
  ext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> simp [Finsupp.single_apply, h0, h1]

/-- The simple-pole divisor `Finsupp.single 0 1 + Finsupp.single 1 1` is nonzero exactly at `0`
and `1`. -/
theorem single_zero_add_single_one_ne_zero_iff {α : Type*} [Zero α] [One α] (x : α) :
    (Finsupp.single (0 : α) (1 : ℕ) + Finsupp.single 1 1 : α →₀ ℕ) x ≠ 0 ↔ x = 0 ∨ x = 1 := by
  classical
  simp only [← Finsupp.mem_support_iff, support_single_zero_add_single_one, Finset.mem_insert,
    Finset.mem_singleton]

/-- The simple-pole divisor `Finsupp.single 0 1 + Finsupp.single 1 1` vanishes away from `0` and
`1`. -/
theorem single_zero_add_single_one_eq_zero_iff {α : Type*} [Zero α] [One α] (x : α) :
    (Finsupp.single (0 : α) (1 : ℕ) + Finsupp.single 1 1 : α →₀ ℕ) x = 0 ↔ x ≠ 0 ∧ x ≠ 1 := by
  simpa only [ne_eq, not_not, not_or] using not_congr (single_zero_add_single_one_ne_zero_iff x)

/-- Conjugation preserves the simple-pole divisor at `0` and `1`. -/
theorem mapDomain_conj_single_zero_add_single_one :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1).mapDomain conj =
      Finsupp.single 0 1 + Finsupp.single 1 1 := by
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single, map_zero, map_one]

/-- Evaluation of `Finsupp.single 0 1 + Finsupp.single 1 1` is invariant under conjugation. -/
theorem single_zero_add_single_one_conj (s : ℂ) :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) (conj s) =
      (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) s := by
  have h := congrArg (fun d : ℂ →₀ ℕ ↦ d (conj s)) mapDomain_conj_single_zero_add_single_one.symm
  rwa [Finsupp.mapDomain_apply_of_injective (starRingEnd ℂ).injective] at h

/-- The simple-pole divisor at `0` and `1` is invariant under `s ↦ 1 - conj s`. -/
theorem single_zero_add_single_one_one_sub_conj (s : ℂ) :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) (1 - conj s) =
      (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) s := by
  have h0 : (0 : ℂ) = 1 - conj s ↔ (1 : ℂ) = s := by
    rw [eq_comm, sub_eq_zero, eq_comm]
    exact (map_eq_one_iff _ (starRingEnd ℂ).injective).trans eq_comm
  have h1 : (1 : ℂ) = 1 - conj s ↔ (0 : ℂ) = s := by
    rw [eq_comm, sub_eq_self]
    exact (map_eq_zero_iff _ (starRingEnd ℂ).injective).trans eq_comm
  simp only [Finsupp.add_apply, Finsupp.single_apply, h0, h1]
  rw [add_comm]

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
  · rw [AnalyticLFunctionData.dual_polarOrder_apply]
    exact single_zero_add_single_one_conj _

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
    rcases (single_zero_add_single_one_ne_zero_iff p).mp hp with rfl | rfl
    · simp [meromorphicOrderAt_completedRiemannZeta_zero]
    · simp [meromorphicOrderAt_completedRiemannZeta_one]
  analyticAt p hp := by
    obtain ⟨h0, h1⟩ := (single_zero_add_single_one_eq_zero_iff p).mp hp
    exact analyticAt_completedRiemannZeta h0 h1

/-- The functional equation `Λ(s) = Λ(1 - s)` of the completed Riemann zeta function, with root
number `1`. -/
theorem riemannZetaData_hasFunctionalEquation : riemannZetaData.HasFunctionalEquation where
  norm_rootNumber := by simp
  polarOrder_one_sub_conj s := single_zero_add_single_one_one_sub_conj s
  completed_eq s _ _ := by
    rw [riemannZetaData_dual, riemannZetaData_rootNumber, one_mul, riemannZetaData_completed,
      completedRiemannZeta_one_sub]

/-- Constructing the Riemann-zeta card from its series recovers every field, with the completed
function put in meromorphic normal form. In particular, the extracted root number is `1`.
No equality with Mathlib's representative at its poles is asserted. -/
theorem ofSeries_riemannZetaData :
    AnalyticLFunctionData.ofSeries riemannZetaData.coeff riemannZetaData.conductor
      riemannZetaData.gammaR riemannZetaData.gammaC riemannZetaData.polarOrder =
      { riemannZetaData with completed := toMeromorphicNFOn completedRiemannZeta Set.univ } := by
  apply AnalyticLFunctionData.ofSeries_eq_normalized
    riemannZetaData_hasDirichletAgreement riemannZetaData_hasMeromorphicContinuation
    riemannZetaData_hasFunctionalEquation
  · intro s hs
    exact (single_zero_add_single_one_eq_zero_iff s).mpr
      ⟨by rintro rfl; norm_num at hs, by rintro rfl; norm_num at hs⟩
  · have heq : riemannZetaData.completed 2 = Gammaℝ 2 * LSeries riemannZetaData.coeff 2 := by
      simpa using riemannZetaData_hasDirichletAgreement.completed_eq 2 (by norm_num)
    have hL : LSeries riemannZetaData.coeff 2 = riemannZeta 2 :=
      ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by norm_num)
    rw [heq, hL]
    exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos (by norm_num))
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))

-- The all-one presentation differs from the arithmetic-function presentation at index zero.
-- Comparison transports every analytic property while retaining this distinction of records.
example : ∃ e : AnalyticLFunctionData, riemannZetaData.EqOffZero e ∧ riemannZetaData ≠ e ∧
    e.HasDirichletAgreement ∧ e.HasMeromorphicContinuation ∧ e.HasFunctionalEquation := by
  let e : AnalyticLFunctionData :=
    { riemannZetaData with coeff := Function.update riemannZetaData.coeff 0 1 }
  have h : riemannZetaData.EqOffZero e :=
    AnalyticLFunctionData.eqOffZero_update_coeff_zero riemannZetaData 1
  refine ⟨e, h, ?_, h.hasDirichletAgreement riemannZetaData_hasDirichletAgreement,
    h.hasMeromorphicContinuation riemannZetaData_hasMeromorphicContinuation,
    h.hasFunctionalEquation riemannZetaData_hasFunctionalEquation⟩
  intro heq
  have hzero := congrArg (fun d : AnalyticLFunctionData ↦ d.coeff 0) heq
  simp [e] at hzero

end TauCeti.LFunctions
