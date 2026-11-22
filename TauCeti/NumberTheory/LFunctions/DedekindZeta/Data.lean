/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completion
import TauCeti.Data.Finsupp.Single
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.LFunctions.Data.PolarDivisor

/-!
# The completed L-function card of the Dedekind zeta function

For a number field `K`, this file packages `TauCeti.LFunctions.completedDedekindZeta K` into an
`AnalyticLFunctionData` card `TauCeti.LFunctions.dedekindZetaData K` of degree `[K : ℚ]`,
conductor `|d_K|`, `r₁` real and `r₂` complex gamma factors with shift `0`, root number `1`,
and simple poles at `0` and `1` (Iwaniec--Kowalski §5.1; Neukirch VII §5).

It proves that `dedekindZetaData K` is self-dual, satisfies `HasAverageCoefficientGrowth`,
`HasDirichletAgreement`, `HasMeromorphicContinuation`, and `HasFunctionalEquation`, and is
recovered verbatim by `AnalyticLFunctionData.ofSeries`. Over `K = ℚ`, it compares
`dedekindZetaData ℚ` with `TauCeti.LFunctions.riemannZetaData`.

## Main definitions

* `TauCeti.LFunctions.dedekindZetaData`: the completed L-function card of `ζ_K`.

## Main results

* `TauCeti.LFunctions.dedekindZetaData_degree`, `TauCeti.LFunctions.dedekindZetaData_gammaFactor`,
  `TauCeti.LFunctions.dedekindZetaData_dual`: basic invariants and self-duality of the card.
* `TauCeti.LFunctions.dedekindZetaData_hasAverageCoefficientGrowth`,
  `TauCeti.LFunctions.dedekindZetaData_hasDirichletAgreement`,
  `TauCeti.LFunctions.dedekindZetaData_hasMeromorphicContinuation`,
  `TauCeti.LFunctions.dedekindZetaData_hasFunctionalEquation`: the four analytic predicates.
* `TauCeti.LFunctions.ofSeries_dedekindZetaData`: exact recovery by
  `AnalyticLFunctionData.ofSeries`.
* `TauCeti.LFunctions.dedekindZetaData_rat_eqOffZero`: comparison over `ℚ` with `riemannZetaData`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section
noncomputable section

open Complex ComplexConjugate NumberField NumberField.InfinitePlace Set

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- **The Dedekind zeta card** of a number field `K`: coefficients `dedekindZetaCoeff K`,
conductor `|d_K|`, `r₁` real and `r₂` complex gamma factors with shift `0`, root number `1`,
completed function `completedDedekindZeta K`, and simple poles at `0` and `1`. -/
def dedekindZetaData : AnalyticLFunctionData where
  coeff n := (dedekindZetaCoeff K n : ℂ)
  conductor := ⟨(discr K).natAbs, Int.natAbs_pos.mpr (discr_ne_zero K)⟩
  gammaR := Multiset.replicate (nrRealPlaces K) 0
  gammaC := Multiset.replicate (nrComplexPlaces K) 0
  rootNumber := 1
  completed := completedDedekindZeta K
  polarOrder := Finsupp.single 0 1 + Finsupp.single 1 1

@[simp]
theorem dedekindZetaData_coeff (n : ℕ) :
    (dedekindZetaData K).coeff n = (dedekindZetaCoeff K n : ℂ) := (rfl)

@[simp]
theorem dedekindZetaData_conductor :
    (dedekindZetaData K).conductor = ⟨(discr K).natAbs, Int.natAbs_pos.mpr (discr_ne_zero K)⟩ :=
  (rfl)

@[simp]
theorem dedekindZetaData_gammaR :
    (dedekindZetaData K).gammaR = Multiset.replicate (nrRealPlaces K) 0 := (rfl)

@[simp]
theorem dedekindZetaData_gammaC :
    (dedekindZetaData K).gammaC = Multiset.replicate (nrComplexPlaces K) 0 := (rfl)

@[simp]
theorem dedekindZetaData_rootNumber : (dedekindZetaData K).rootNumber = 1 := (rfl)

@[simp]
theorem dedekindZetaData_completed :
    (dedekindZetaData K).completed = completedDedekindZeta K := (rfl)

@[simp]
theorem dedekindZetaData_polarOrder :
    (dedekindZetaData K).polarOrder = Finsupp.single 0 1 + Finsupp.single 1 1 := (rfl)

@[simp]
theorem dedekindZetaData_degree : (dedekindZetaData K).degree = Module.finrank ℚ K := by
  simp [AnalyticLFunctionData.degree_def, InfinitePlace.card_add_two_mul_card_eq_rank]

@[simp]
theorem dedekindZetaData_gammaFactor (s : ℂ) :
    (dedekindZetaData K).gammaFactor s =
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K := by
  simp [AnalyticLFunctionData.gammaFactor_def]

/-- The Dedekind zeta card is its own dual. -/
@[simp]
theorem dedekindZetaData_dual : (dedekindZetaData K).dual = dedekindZetaData K := by
  ext
  · simp
  · exact AnalyticLFunctionData.dual_conductor _
  · simp
  · simp
  · simp
  · simp
  · rw [AnalyticLFunctionData.dual_polarOrder_apply, dedekindZetaData_polarOrder]
    exact single_zero_add_single_one_conj _

/-- The Dedekind zeta coefficients satisfy the average absolute growth bound `O(n ^ (1 + ε))`. -/
theorem dedekindZetaData_hasAverageCoefficientGrowth :
    (dedekindZetaData K).HasAverageCoefficientGrowth := by
  rw [AnalyticLFunctionData.hasAverageCoefficientGrowth_iff_abscissaOfAbsConv_le]
  exact le_of_eq (abscissaOfAbsConv_dedekindZetaCoeff K)

/-- On `Re s > 1`, `completedDedekindZeta K` agrees with the completed Dirichlet series of
`dedekindZetaCoeff K`. -/
theorem dedekindZetaData_hasDirichletAgreement :
    (dedekindZetaData K).HasDirichletAgreement where
  coeff_one := by simp
  degree_pos := by simp [Module.finrank_pos]
  completed_eq s hs := by
    have hdiscr : (((dedekindZetaData K).conductor : ℕ) : ℂ) = ((|discr K| : ℤ) : ℂ) := by
      rw [dedekindZetaData_conductor, PNat.mk_coe, ← Int.cast_natCast, Int.natCast_natAbs]
    have hL : LSeries (dedekindZetaData K).coeff s = dedekindZeta K s := by
      rw [dedekindZeta_eq_LSeries_dedekindZetaCoeff]
      exact congrArg (LSeries · s) (funext (dedekindZetaData_coeff K))
    rw [dedekindZetaData_completed, dedekindZetaData_gammaFactor, hdiscr, hL,
      completedDedekindZeta_eq hs]
    ring

/-- The completed Dedekind zeta function is meromorphic, with simple poles at `0` and `1` and no
others. -/
theorem dedekindZetaData_hasMeromorphicContinuation :
    (dedekindZetaData K).HasMeromorphicContinuation where
  meromorphic := meromorphic_completedDedekindZeta K
  meromorphicOrderAt_eq p hp := by
    rw [dedekindZetaData_polarOrder] at hp ⊢
    rcases (Finsupp.single_add_single_ne_zero_iff one_ne_zero one_ne_zero p).mp hp with rfl | rfl
    · simp [meromorphicOrderAt_completedDedekindZeta_zero]
    · simp [meromorphicOrderAt_completedDedekindZeta_one]
  analyticAt p hp := by
    rw [dedekindZetaData_polarOrder] at hp
    obtain ⟨h0, h1⟩ := (Finsupp.single_add_single_eq_zero_iff one_ne_zero one_ne_zero p).mp hp
    exact analyticAt_completedDedekindZeta h0 h1

/-- The functional equation `Λ_K(1 - s) = Λ_K(s)` of the completed Dedekind zeta function, with
root number `1`. -/
theorem dedekindZetaData_hasFunctionalEquation :
    (dedekindZetaData K).HasFunctionalEquation where
  norm_rootNumber := by simp
  polarOrder_one_sub_conj s := by
    rw [dedekindZetaData_polarOrder]
    exact single_zero_add_single_one_one_sub_conj s
  completed_eq s _ _ := by
    simp [completedDedekindZeta_one_sub]

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
  rw [dedekindZetaData_completed, completedDedekindZeta_eq (by norm_num)]
  have hdiscr : ((|discr K| : ℤ) : ℂ) ^ ((2 : ℂ) / 2) ≠ 0 := by
    rw [div_self two_ne_zero, Complex.cpow_one]
    exact_mod_cast (abs_pos.mpr (discr_ne_zero K)).ne'
  have hGℝ : Gammaℝ 2 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hGℂ : Gammaℂ 2 ≠ 0 := Gammaℂ_ne_zero_of_re_pos (by norm_num)
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero hdiscr (pow_ne_zero _ hGℝ)) (pow_ne_zero _ hGℂ))
    (dedekindZeta_ne_zero_of_one_lt_re (by norm_num))

/-! ### Comparison over `ℚ` with the Riemann zeta function -/

/-- Over `ℚ`, `dedekindZetaData ℚ` agrees off index zero with the normal-form version of
`riemannZetaData`. The two differ at index zero because `dedekindZetaCoeff ℚ 0 = 1` whereas
`ArithmeticFunction.zeta 0 = 0`. -/
theorem dedekindZetaData_rat_eqOffZero :
    (dedekindZetaData ℚ).EqOffZero
      { riemannZetaData with completed := toMeromorphicNFOn completedRiemannZeta univ } where
  coeff_eq n hn := by simp [hn]
  conductor_eq := by
    apply PNat.eq
    simp
  gammaR_eq := by
    simp [nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ)]
  gammaC_eq := by simp
  rootNumber_eq := by simp
  completed_eq := completedDedekindZeta_rat_eq_toMeromorphicNFOn
  polarOrder_eq := by simp

end TauCeti.LFunctions
