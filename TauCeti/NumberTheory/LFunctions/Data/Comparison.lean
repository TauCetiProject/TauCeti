/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Basic

/-!
# Comparing completed L-function cards

`AnalyticLFunctionData.EqOffZero` compares every field of two completed L-function cards,
except for the coefficient at index zero. Mathlib's `LSeries` ignores that coefficient, so
independently constructed cards can describe the same completed L-function without being equal.
The relation preserves the degree, gamma factor, Dirichlet series and its convergence, all three
basic analytic predicates, and duality. If the coefficients at zero also agree, it gives equality.

The characterization `eqOffZero_iff_exists_update` says precisely how much freedom remains:
one card is obtained from the other by changing its zeroth coefficient. No completed-function
values, including values at poles, are discarded by this relation.

The proofs use Mathlib's `LSeries_congr` and `LSeriesSummable_congr` for the unused coefficient.
The completed-function conventions are those of Iwaniec–Kowalski, *Analytic Number Theory*, §5.1.
-/

public section

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- Equality of all card data except the coefficient at zero, which `LSeries` does not read. -/
structure EqOffZero (d e : AnalyticLFunctionData) : Prop where
  /-- The coefficients agree at every positive index. -/
  coeff_eq : ∀ n : ℕ, n ≠ 0 → d.coeff n = e.coeff n
  /-- The conductors agree. -/
  conductor_eq : d.conductor = e.conductor
  /-- The real gamma shifts agree. -/
  gammaR_eq : d.gammaR = e.gammaR
  /-- The complex gamma shifts agree. -/
  gammaC_eq : d.gammaC = e.gammaC
  /-- The root numbers agree. -/
  rootNumber_eq : d.rootNumber = e.rootNumber
  /-- The completed functions agree as total functions. -/
  completed_eq : d.completed = e.completed
  /-- The polar divisors agree. -/
  polarOrder_eq : d.polarOrder = e.polarOrder

variable {d e f : AnalyticLFunctionData}

@[refl, simp]
theorem EqOffZero.refl (d : AnalyticLFunctionData) : d.EqOffZero d :=
  ⟨fun _ _ ↦ rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[symm]
theorem EqOffZero.symm (h : d.EqOffZero e) : e.EqOffZero d :=
  ⟨fun n hn ↦ (h.coeff_eq n hn).symm, h.conductor_eq.symm, h.gammaR_eq.symm,
    h.gammaC_eq.symm, h.rootNumber_eq.symm, h.completed_eq.symm, h.polarOrder_eq.symm⟩

@[trans]
theorem EqOffZero.trans (h : d.EqOffZero e) (h' : e.EqOffZero f) : d.EqOffZero f :=
  ⟨fun n hn ↦ (h.coeff_eq n hn).trans (h'.coeff_eq n hn),
    h.conductor_eq.trans h'.conductor_eq, h.gammaR_eq.trans h'.gammaR_eq,
    h.gammaC_eq.trans h'.gammaC_eq, h.rootNumber_eq.trans h'.rootNumber_eq,
    h.completed_eq.trans h'.completed_eq, h.polarOrder_eq.trans h'.polarOrder_eq⟩

/-- Agreement of the unused coefficients upgrades comparison to equality of cards. -/
theorem EqOffZero.eq (h : d.EqOffZero e) (hzero : d.coeff 0 = e.coeff 0) : d = e := by
  apply AnalyticLFunctionData.ext
  · exact funext fun n ↦ by
      by_cases hn : n = 0
      · simpa [hn] using hzero
      · exact h.coeff_eq n hn
  · exact h.conductor_eq
  · exact h.gammaR_eq
  · exact h.gammaC_eq
  · exact h.rootNumber_eq
  · exact h.completed_eq
  · exact h.polarOrder_eq

/-- Exact equality also checks the coefficient at zero. -/
theorem eq_iff_eqOffZero_and_coeff_zero :
    d = e ↔ d.EqOffZero e ∧ d.coeff 0 = e.coeff 0 := by
  constructor
  · rintro rfl
    exact ⟨EqOffZero.refl _, rfl⟩
  · rintro ⟨h, hzero⟩
    exact h.eq hzero

/-- Changing only the unused coefficient preserves comparison. -/
@[simp]
theorem eqOffZero_update_coeff_zero (d : AnalyticLFunctionData) (z : ℂ) :
    d.EqOffZero { d with coeff := Function.update d.coeff 0 z } := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro n hn
  simp [hn]

/-- Two cards compare exactly when one changes only the other's coefficient at zero. -/
theorem eqOffZero_iff_exists_update :
    d.EqOffZero e ↔ ∃ z : ℂ, e = { d with coeff := Function.update d.coeff 0 z } := by
  constructor
  · intro h
    refine ⟨e.coeff 0, ?_⟩
    exact (h.symm.trans (eqOffZero_update_coeff_zero d (e.coeff 0))).eq (by simp)
  · rintro ⟨z, rfl⟩
    exact eqOffZero_update_coeff_zero d z

/-- Comparing cards also compares their dual cards. -/
theorem EqOffZero.dual (h : d.EqOffZero e) : d.dual.EqOffZero e.dual where
  coeff_eq n hn := by simp [h.coeff_eq n hn]
  conductor_eq := by simp [h.conductor_eq]
  gammaR_eq := by simp [h.gammaR_eq]
  gammaC_eq := by simp [h.gammaC_eq]
  rootNumber_eq := by simp [h.rootNumber_eq]
  completed_eq := by simp [h.completed_eq]
  polarOrder_eq := by ext s; simp [h.polarOrder_eq]

@[simp]
theorem eqOffZero_dual_iff : d.dual.EqOffZero e.dual ↔ d.EqOffZero e :=
  ⟨fun h ↦ by simpa using h.dual, EqOffZero.dual⟩

/-- Compared cards have the same degree. -/
theorem EqOffZero.degree_eq (h : d.EqOffZero e) : d.degree = e.degree := by
  simp only [degree_def, h.gammaR_eq, h.gammaC_eq]

/-- Compared cards have the same gamma factor. -/
theorem EqOffZero.gammaFactor_eq (h : d.EqOffZero e) : d.gammaFactor = e.gammaFactor := by
  funext s
  simp only [gammaFactor_def, h.gammaR_eq, h.gammaC_eq]

/-- Compared cards have the same Dirichlet series, including where it is not summable. -/
theorem EqOffZero.LSeries_eq (h : d.EqOffZero e) (s : ℂ) :
    LSeries d.coeff s = LSeries e.coeff s :=
  LSeries_congr (fun hn ↦ h.coeff_eq _ hn) s

/-- Absolute convergence is independent of the unused coefficient. -/
theorem EqOffZero.LSeriesSummable_iff (h : d.EqOffZero e) (s : ℂ) :
    LSeriesSummable d.coeff s ↔ LSeriesSummable e.coeff s :=
  LSeriesSummable_congr s (fun hn ↦ h.coeff_eq _ hn)

/-- Dirichlet-series agreement transports across comparison of cards. -/
theorem EqOffZero.hasDirichletAgreement (h : d.EqOffZero e) (hd : d.HasDirichletAgreement) :
    e.HasDirichletAgreement where
  coeff_one := (h.coeff_eq 1 one_ne_zero).symm.trans hd.coeff_one
  degree_pos := h.degree_eq ▸ hd.degree_pos
  completed_eq s hs := by
    rw [← h.completed_eq, ← h.conductor_eq, ← h.gammaFactor_eq, ← h.LSeries_eq]
    exact hd.completed_eq s hs

/-- Meromorphic continuation, its exact poles and analyticity transport across comparison. -/
theorem EqOffZero.hasMeromorphicContinuation (h : d.EqOffZero e)
    (hd : d.HasMeromorphicContinuation) : e.HasMeromorphicContinuation := by
  rcases hd with ⟨hm, ho, ha⟩
  exact ⟨h.completed_eq ▸ hm, by simpa only [← h.completed_eq, ← h.polarOrder_eq] using ho,
    by simpa only [← h.completed_eq, ← h.polarOrder_eq] using ha⟩

/-- The root-number, polar-symmetry and value clauses all transport across comparison. -/
theorem EqOffZero.hasFunctionalEquation (h : d.EqOffZero e) (hd : d.HasFunctionalEquation) :
    e.HasFunctionalEquation where
  norm_rootNumber := h.rootNumber_eq ▸ hd.norm_rootNumber
  polarOrder_one_sub_conj s := by
    simpa only [← h.polarOrder_eq] using hd.polarOrder_one_sub_conj s
  completed_eq s hs hs' := by
    rw [← h.completed_eq, ← h.rootNumber_eq, ← h.dual.completed_eq]
    exact hd.completed_eq s (h.polarOrder_eq ▸ hs) (h.polarOrder_eq ▸ hs')

/-- Dirichlet-series agreement is invariant under comparison. -/
theorem EqOffZero.hasDirichletAgreement_iff (h : d.EqOffZero e) :
    d.HasDirichletAgreement ↔ e.HasDirichletAgreement :=
  ⟨h.hasDirichletAgreement, h.symm.hasDirichletAgreement⟩

/-- Meromorphic continuation with exact poles is invariant under comparison. -/
theorem EqOffZero.hasMeromorphicContinuation_iff (h : d.EqOffZero e) :
    d.HasMeromorphicContinuation ↔ e.HasMeromorphicContinuation :=
  ⟨h.hasMeromorphicContinuation, h.symm.hasMeromorphicContinuation⟩

/-- The full functional equation is invariant under comparison. -/
theorem EqOffZero.hasFunctionalEquation_iff (h : d.EqOffZero e) :
    d.HasFunctionalEquation ↔ e.HasFunctionalEquation :=
  ⟨h.hasFunctionalEquation, h.symm.hasFunctionalEquation⟩

end TauCeti.LFunctions.AnalyticLFunctionData
