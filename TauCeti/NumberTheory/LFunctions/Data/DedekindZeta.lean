/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.Basic
public import TauCeti.NumberTheory.LFunctions.Data.Growth
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
import TauCeti.Data.Finsupp.Order
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.LFunctions.Data.PolarDivisor

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
    rw [dedekindZetaData_polarOrder] at hp ⊢
    rcases (Finsupp.single_add_single_ne_zero_iff one_ne_zero one_ne_zero p).mp hp with rfl | rfl
    · simp [meromorphicOrderAt_completedDedekindZeta_zero]
    · simp [meromorphicOrderAt_completedDedekindZeta_one]
  analyticAt p hp := by
    rw [dedekindZetaData_polarOrder] at hp
    obtain ⟨h0, h1⟩ := (Finsupp.single_add_single_eq_zero_iff one_ne_zero one_ne_zero p).mp hp
    simpa only [dedekindZetaData_completed] using analyticAt_completedDedekindZeta K h0 h1

/-- The Dedekind zeta card is its own dual. -/
@[simp] theorem dedekindZetaData_dual : (dedekindZetaData K).dual = dedekindZetaData K := by
  ext
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · rw [AnalyticLFunctionData.dual_polarOrder_apply, dedekindZetaData_polarOrder]
    exact single_zero_add_single_one_conj _

/-- The completed card satisfies `Λ(s) = Λ(1 - s)`, with root number one. -/
theorem dedekindZetaData_hasFunctionalEquation : (dedekindZetaData K).HasFunctionalEquation where
  norm_rootNumber := by simp
  polarOrder_one_sub_conj s := by
    rw [dedekindZetaData_polarOrder]
    exact single_zero_add_single_one_one_sub_conj s
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

/-- Constructing the Dedekind-zeta card from its Dirichlet series recovers `dedekindZetaData K`
verbatim, because `completedDedekindZeta K` is already in meromorphic normal form. In particular,
the extracted root number is `1`. -/
theorem ofSeries_dedekindZetaData :
    AnalyticLFunctionData.ofSeries (dedekindZetaData K).coeff (dedekindZetaData K).conductor
      (dedekindZetaData K).gammaR (dedekindZetaData K).gammaC (dedekindZetaData K).polarOrder =
      dedekindZetaData K := by
  refine AnalyticLFunctionData.ofSeries_eq
    (dedekindZetaData_hasDirichletAgreement K) (dedekindZetaData_hasFunctionalEquation K)
    (meromorphicNFOn_completedDedekindZeta K) ?_ ?_
  · rw [dedekindZetaData_polarOrder]
    exact (Finsupp.single_add_single_eq_zero_iff one_ne_zero one_ne_zero 2).mpr
      ⟨by norm_num, by norm_num⟩
  rw [dedekindZetaData_completed, completedDedekindZeta_eq_mul_dedekindZeta K (by norm_num)]
  have hdiscr : ((|discr K| : ℤ) : ℂ) ^ ((2 : ℂ) / 2) ≠ 0 := by
    rw [div_self two_ne_zero, Complex.cpow_one]
    exact Int.cast_ne_zero.mpr (abs_ne_zero.mpr (discr_ne_zero K))
  have hGℝ : Gammaℝ 2 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hGℂ : Gammaℂ 2 ≠ 0 := Gammaℂ_ne_zero_of_re_pos (by norm_num)
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero hdiscr (pow_ne_zero _ hGℝ)) (pow_ne_zero _ hGℂ))
    (dedekindZeta_ne_zero_of_one_lt_re (by norm_num))

end TauCeti.LFunctions
