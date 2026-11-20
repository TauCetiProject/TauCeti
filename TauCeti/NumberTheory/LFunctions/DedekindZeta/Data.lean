/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.LFunctions.Data.Growth
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Data.Series
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completion
import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic

/-!
# The completed L-function card of the Dedekind zeta function

For a number field `K`, this file packages `TauCeti.LFunctions.completedDedekindZeta K` into an
`AnalyticLFunctionData` card `TauCeti.LFunctions.dedekindZetaData K` of degree `[K : ℚ]`,
conductor `|d_K|`, `r₁` real and `r₂` complex gamma factors with shift `0`, root number `1`,
and simple poles at `0` and `1` (Iwaniec--Kowalski §5.1; Neukirch VII §5).

It proves that `dedekindZetaData K` is self-dual, satisfies `HasAverageCoefficientGrowth`,
`HasDirichletAgreement`, `HasMeromorphicContinuation`, and `HasFunctionalEquation`, and is
recovered verbatim by `AnalyticLFunctionData.ofSeries`. Over `K = ℚ`, it compares
`completedDedekindZeta ℚ` and `dedekindZetaData ℚ` with Mathlib's `completedRiemannZeta` and
`TauCeti.LFunctions.riemannZetaData`.

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
* `TauCeti.LFunctions.completedDedekindZeta_rat_eq`,
  `TauCeti.LFunctions.dedekindZetaData_rat_eqOffZero`: comparison over `ℚ` with the completed
  Riemann zeta function and `riemannZetaData`.

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
  · simp [completedDedekindZeta_conj]
  · simp [Finsupp.single_apply, eq_comm (a := (0 : ℂ)), eq_comm (a := (1 : ℂ)),
      map_eq_one_iff _ (starRingEnd ℂ).injective]

/-- The Dedekind zeta coefficients satisfy the average absolute growth bound `O(n ^ (1 + ε))`. -/
theorem dedekindZetaData_hasAverageCoefficientGrowth :
    (dedekindZetaData K).HasAverageCoefficientGrowth := by
  rw [AnalyticLFunctionData.hasAverageCoefficientGrowth_iff_abscissaOfAbsConv_le]
  exact le_of_eq (abscissaOfAbsConv_dedekindZetaCoeff K)

/-- The unit ideal is the unique integral ideal of absolute norm `1`. -/
private theorem dedekindZetaCoeff_one : dedekindZetaCoeff K 1 = 1 := by
  rw [← card_normFiber_eq_dedekindZetaCoeff K one_ne_zero, normFiber_one, Finset.card_singleton]

/-- On `Re s > 1`, `completedDedekindZeta K` agrees with the completed Dirichlet series of
`dedekindZetaCoeff K`. -/
theorem dedekindZetaData_hasDirichletAgreement :
    (dedekindZetaData K).HasDirichletAgreement where
  coeff_one := by simp [dedekindZetaCoeff_one]
  degree_pos := by
    rw [dedekindZetaData_degree]
    exact Module.finrank_pos
  completed_eq s hs := by
    have hdiscr : (((discr K).natAbs : ℕ) : ℂ) = ((|discr K| : ℤ) : ℂ) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs]
    have hcoeff : (dedekindZetaData K).coeff = fun n ↦ (dedekindZetaCoeff K n : ℂ) := rfl
    rw [dedekindZetaData_completed, dedekindZetaData_conductor, PNat.mk_coe, hdiscr,
      dedekindZetaData_gammaFactor, hcoeff, completedDedekindZeta_eq hs,
      dedekindZeta_eq_LSeries_dedekindZetaCoeff]
    ring

/-- The completed Dedekind zeta function is meromorphic, with simple poles at `0` and `1` and no
others. -/
theorem dedekindZetaData_hasMeromorphicContinuation :
    (dedekindZetaData K).HasMeromorphicContinuation where
  meromorphic := meromorphic_completedDedekindZeta K
  meromorphicOrderAt_eq p hp := by
    by_cases h0 : p = 0
    · subst h0
      simp [meromorphicOrderAt_completedDedekindZeta_zero]
    by_cases h1 : p = 1
    · subst h1
      simp [meromorphicOrderAt_completedDedekindZeta_one]
    simp [Ne.symm h0, Ne.symm h1] at hp
  analyticAt p hp := by
    refine analyticAt_completedDedekindZeta ?_ ?_ <;> rintro rfl <;> simp at hp

/-- The functional equation `Λ_K(1 - s) = Λ_K(s)` of the completed Dedekind zeta function, with
root number `1`. -/
theorem dedekindZetaData_hasFunctionalEquation :
    (dedekindZetaData K).HasFunctionalEquation where
  norm_rootNumber := by simp
  polarOrder_one_sub_conj s := by
    have hconj (z : ℂ) :
        (dedekindZetaData K).polarOrder (conj z) = (dedekindZetaData K).polarOrder z := by
      rw [← AnalyticLFunctionData.dual_polarOrder_apply, dedekindZetaData_dual]
    have e0 : (0 : ℂ) = 1 - s ↔ 1 = s := by rw [eq_comm, sub_eq_zero]
    have e1 : (1 : ℂ) = 1 - s ↔ 0 = s := by rw [eq_comm, sub_eq_self, eq_comm]
    rw [← map_one (starRingEnd ℂ), ← map_sub, hconj]
    simp only [dedekindZetaData_polarOrder, Finsupp.add_apply, Finsupp.single_apply, e0, e1]
    rw [add_comm]
  completed_eq s _ _ := by
    rw [dedekindZetaData_dual, dedekindZetaData_rootNumber, one_mul, dedekindZetaData_completed,
      completedDedekindZeta_one_sub]

/-- Constructing the Dedekind-zeta card from its Dirichlet series recovers `dedekindZetaData K`
verbatim, because `completedDedekindZeta K` is already in meromorphic normal form. In particular,
the extracted root number is `1`. -/
theorem ofSeries_dedekindZetaData :
    AnalyticLFunctionData.ofSeries (dedekindZetaData K).coeff (dedekindZetaData K).conductor
      (dedekindZetaData K).gammaR (dedekindZetaData K).gammaC (dedekindZetaData K).polarOrder =
      dedekindZetaData K := by
  refine AnalyticLFunctionData.ofSeries_eq
    (dedekindZetaData_hasDirichletAgreement K) (dedekindZetaData_hasFunctionalEquation K)
    (meromorphicNFOn_completedDedekindZeta K) (by norm_num [Finsupp.single_apply]) ?_
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

/-- Over `ℚ`, `completedDedekindZeta ℚ` is the meromorphic normal form of
`completedRiemannZeta`. -/
theorem completedDedekindZeta_rat_eq_toMeromorphicNFOn :
    completedDedekindZeta ℚ = toMeromorphicNFOn completedRiemannZeta univ := by
  refine eq_of_meromorphicNFOn_of_eqOn_halfPlane (meromorphicNFOn_completedDedekindZeta ℚ)
    (meromorphicNFOn_toMeromorphicNFOn _ _) fun s (hs : 1 < s.re) ↦ ?_
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hGℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [toMeromorphicNFOn_apply_of_analyticAt meromorphic_completedRiemannZeta
      (analyticAt_completedRiemannZeta h0 h1),
    completedDedekindZeta_eq hs, discr_rat,
    nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ),
    nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ),
    dedekindZeta_rat_eq_riemannZeta hs, riemannZeta_def_of_ne_zero h0]
  simp [field]

/-- Over `ℚ`, `completedDedekindZeta ℚ` agrees with Mathlib's `completedRiemannZeta` away from
its poles `0` and `1`. -/
theorem completedDedekindZeta_rat_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedDedekindZeta ℚ s = completedRiemannZeta s := by
  rw [completedDedekindZeta_rat_eq_toMeromorphicNFOn]
  exact toMeromorphicNFOn_apply_of_analyticAt meromorphic_completedRiemannZeta
    (analyticAt_completedRiemannZeta h0 h1)

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
