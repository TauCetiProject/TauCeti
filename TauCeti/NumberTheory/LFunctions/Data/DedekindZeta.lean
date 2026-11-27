/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.Basic
public import TauCeti.NumberTheory.LFunctions.Data.Growth
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates

/-!
# Analytic L-function data for Dedekind zeta

The Dedekind zeta card records the ideal-counting coefficients, the absolute discriminant as
conductor, and one gamma factor with shift zero at each infinite place. It is self-dual, with
root number one and simple poles of the completion at zero and one. The card exposes the
continued Dedekind zeta function to the general theory of completed L-functions, including
pole clearing and the functional equation.

The completion and functional equation are those of Neukirch, *Algebraic Number Theory*,
Chapter VII, §5, formalized here in `TauCeti.LFunctions.completedDedekindZeta`.
The card follows the interface of `TauCeti.LFunctions.riemannZetaData`.
-/

public section

open Complex NumberField NumberField.InfinitePlace
open scoped ComplexConjugate

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- The Dedekind zeta card of a number field, with the coefficients of Mathlib's
`NumberField.dedekindZeta` and the meromorphic-normal-form completion. -/
noncomputable def dedekindZetaData : AnalyticLFunctionData where
  coeff n := dedekindZetaCoeff K n
  conductor := ⟨(discr K).natAbs, Int.natAbs_pos.mpr (discr_ne_zero K)⟩
  gammaR := Multiset.replicate (nrRealPlaces K) 0
  gammaC := Multiset.replicate (nrComplexPlaces K) 0
  rootNumber := 1
  completed := completedDedekindZeta K
  polarOrder := Finsupp.single 0 1 + Finsupp.single 1 1

/-- The coefficient at `n` counts integral ideals of absolute norm `n`. -/
@[simp] theorem dedekindZetaData_coeff (n : ℕ) :
    (dedekindZetaData K).coeff n = (dedekindZetaCoeff K n : ℂ) := (rfl)

/-- The conductor is the absolute discriminant. -/
@[simp] theorem dedekindZetaData_conductor :
    ((dedekindZetaData K).conductor : ℕ) = (discr K).natAbs := (rfl)

/-- Every real place contributes one real gamma shift zero. -/
@[simp] theorem dedekindZetaData_gammaR :
    (dedekindZetaData K).gammaR = Multiset.replicate (nrRealPlaces K) 0 := (rfl)

/-- Every complex place contributes one complex gamma shift zero. -/
@[simp] theorem dedekindZetaData_gammaC :
    (dedekindZetaData K).gammaC = Multiset.replicate (nrComplexPlaces K) 0 := (rfl)

/-- The functional equation has root number one. -/
@[simp] theorem dedekindZetaData_rootNumber : (dedekindZetaData K).rootNumber = 1 := (rfl)

/-- The card uses the canonical completed Dedekind zeta function. -/
@[simp] theorem dedekindZetaData_completed :
    (dedekindZetaData K).completed = completedDedekindZeta K := (rfl)

/-- The polar divisor records one simple pole at each of zero and one. -/
@[simp] theorem dedekindZetaData_polarOrder :
    (dedekindZetaData K).polarOrder = Finsupp.single 0 1 + Finsupp.single 1 1 := (rfl)

/-- The degree of the card is the absolute degree of the number field. -/
@[simp] theorem dedekindZetaData_degree : (dedekindZetaData K).degree = Module.finrank ℚ K := by
  simpa [AnalyticLFunctionData.degree_def] using card_add_two_mul_card_eq_rank K

/-- The archimedean factor has one `Γ_ℝ` per real place and one `Γ_ℂ` per complex place. -/
@[simp] theorem dedekindZetaData_gammaFactor (s : ℂ) :
    (dedekindZetaData K).gammaFactor s =
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K := by
  simp [AnalyticLFunctionData.gammaFactor_def]

/-- The Dedekind zeta coefficients have average absolute coefficient growth. -/
theorem dedekindZetaData_hasAverageCoefficientGrowth :
    (dedekindZetaData K).HasAverageCoefficientGrowth := by
  rw [AnalyticLFunctionData.hasAverageCoefficientGrowth_iff_abscissaOfAbsConv_le,
    funext (dedekindZetaData_coeff K), abscissaOfAbsConv_dedekindZetaCoeff]

/-- The completed Dedekind zeta function agrees with the completed Dirichlet series on
`Re s > 1`. -/
theorem dedekindZetaData_hasDirichletAgreement : (dedekindZetaData K).HasDirichletAgreement where
  coeff_one := by simp
  degree_pos := by simpa only [dedekindZetaData_degree] using Module.finrank_pos (R := ℚ) (M := K)
  completed_eq s hs := by
    simp only [dedekindZetaData_completed, completedDedekindZeta_eq_mul_dedekindZeta K hs,
      dedekindZetaData_conductor, Int.abs_eq_natAbs, Int.cast_natCast, dedekindZetaData_gammaFactor,
      dedekindZeta_eq_LSeries_dedekindZetaCoeff, funext (dedekindZetaData_coeff K), mul_assoc]

/-- The completion is meromorphic with exactly the recorded poles at zero and one. -/
theorem dedekindZetaData_hasMeromorphicContinuation :
    (dedekindZetaData K).HasMeromorphicContinuation where
  meromorphic := dedekindZetaData_completed K ▸ meromorphic_completedDedekindZeta K
  meromorphicOrderAt_eq p hp := by
    rcases eq_or_ne p 0 with rfl | h0
    · simp [meromorphicOrderAt_completedDedekindZeta_zero]
    rcases eq_or_ne p 1 with rfl | h1
    · simp [meromorphicOrderAt_completedDedekindZeta_one]
    simp [Ne.symm h0, Ne.symm h1] at hp
  analyticAt p hp := by
    rw [dedekindZetaData_completed, analyticAt_completedDedekindZeta_iff]
    exact ⟨fun h ↦ by simp [h] at hp, fun h ↦ by simp [h] at hp⟩

/-- The Dedekind zeta card is its own dual. -/
@[simp] theorem dedekindZetaData_dual : (dedekindZetaData K).dual = dedekindZetaData K := by
  ext
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp [Finsupp.single_apply, eq_comm (a := (0 : ℂ)), eq_comm (a := (1 : ℂ)),
      map_eq_one_iff _ (starRingEnd ℂ).injective]

/-- The completed card satisfies `Λ(s) = Λ(1 - s)`, with root number one. -/
theorem dedekindZetaData_hasFunctionalEquation : (dedekindZetaData K).HasFunctionalEquation where
  norm_rootNumber := by simp
  polarOrder_one_sub_conj s := by
    have hconj (z : ℂ) : (dedekindZetaData K).polarOrder (conj z) =
        (dedekindZetaData K).polarOrder z := by
      rw [← AnalyticLFunctionData.dual_polarOrder_apply, dedekindZetaData_dual]
    have h0 : (0 : ℂ) = 1 - s ↔ 1 = s := by rw [eq_comm, sub_eq_zero]
    have h1 : (1 : ℂ) = 1 - s ↔ 0 = s := by rw [eq_comm, sub_eq_self, eq_comm]
    rw [← map_one (starRingEnd ℂ), ← map_sub, hconj]
    simp only [dedekindZetaData_polarOrder, Finsupp.add_apply, Finsupp.single_apply,
      h0, h1, add_comm]
  completed_eq s _ _ := by
    simp [completedDedekindZeta_one_sub]

/-- Removing the conductor and gamma factors recovers the canonical Dedekind zeta
continuation, with the same normal-form value at the pole. -/
@[simp] theorem dedekindZetaData_continuedL :
    (dedekindZetaData K).continuedL = dedekindZetaC K := by
  have hNF : MeromorphicNFOn (dedekindZetaData K).completed Set.univ := by
    simpa only [dedekindZetaData_completed] using meromorphicNFOn_completedDedekindZeta K
  rw [(dedekindZetaData_hasDirichletAgreement K).continuedL_eq_meromorphicContinuation hNF,
    funext (dedekindZetaData_coeff K), ← funext (dedekindZeta_eq_LSeries_dedekindZetaCoeff K),
    dedekindZetaC_def]

end TauCeti.LFunctions
