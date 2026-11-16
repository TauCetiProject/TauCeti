/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.LFunctions.Data.Growth
public import TauCeti.NumberTheory.LFunctions.Data.Series
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completion
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic

/-!
# The completed L-function card of the Dedekind zeta function

For a number field `K` of degree `n = r₁ + 2 r₂` and discriminant `d_K`, the Dedekind zeta
function defines an analytic L-function card `TauCeti.LFunctions.dedekindZetaData K`:

* Dirichlet coefficients `normCoeff K (1 : IdealArithmeticFunction K)`, counting nonzero integral
  ideals of each positive norm (and vanishing at `0`),
* conductor `|d_K|`,
* `r₁` real gamma shifts `0` and `r₂` complex gamma shifts `0`, giving degree `[K : ℚ]` and
  gamma factor `Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂`,
* root number `1`,
* completed function `TauCeti.LFunctions.completedDedekindZeta K`,
* polar divisor consisting of simple poles at `0` and `1`.

This file defines `dedekindZetaData K`, proves that it is self-dual and satisfies
`HasAverageCoefficientGrowth`, `HasDirichletAgreement`, `HasMeromorphicContinuation`, and
`HasFunctionalEquation`, and shows that `AnalyticLFunctionData.ofSeries` recovers it identically
(including the canonical normal-form values at `0` and `1` and the root number `1`).

## Main definitions

* `TauCeti.LFunctions.dedekindZetaData`: the analytic L-function card of `ζ_K`.

## Main results

* `TauCeti.LFunctions.dedekindZetaData_degree`, `TauCeti.LFunctions.dedekindZetaData_gammaFactor`,
  `TauCeti.LFunctions.dedekindZetaData_dual`: degree, gamma factor, and self-duality.
* `TauCeti.LFunctions.dedekindZetaData_hasAverageCoefficientGrowth`,
  `TauCeti.LFunctions.dedekindZetaData_hasDirichletAgreement`,
  `TauCeti.LFunctions.dedekindZetaData_hasMeromorphicContinuation`,
  `TauCeti.LFunctions.dedekindZetaData_hasFunctionalEquation`: the analytic L-function axioms.
* `TauCeti.LFunctions.ofSeries_dedekindZetaData`: exact recovery by
  `AnalyticLFunctionData.ofSeries`.
-/

public section

noncomputable section

open Complex ComplexConjugate NumberField NumberField.InfinitePlace

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- **The Dedekind zeta card** of a number field `K`. Coefficients
`normCoeff K (1 : IdealArithmeticFunction K)`, conductor `|d_K|`, `r₁` real gamma shifts `0` and
`r₂` complex gamma shifts `0`, root number `1`, completed function `completedDedekindZeta K`, and
simple poles at `0` and `1`. -/
def dedekindZetaData : AnalyticLFunctionData where
  coeff n := normCoeff K (1 : IdealArithmeticFunction K) n
  conductor := ⟨(discr K).natAbs, Int.natAbs_pos.mpr (discr_ne_zero K)⟩
  gammaR := Multiset.replicate (nrRealPlaces K) 0
  gammaC := Multiset.replicate (nrComplexPlaces K) 0
  rootNumber := 1
  completed := completedDedekindZeta K
  polarOrder := Finsupp.single 0 1 + Finsupp.single 1 1

@[simp]
theorem dedekindZetaData_coeff (n : ℕ) :
    (dedekindZetaData K).coeff n = normCoeff K (1 : IdealArithmeticFunction K) n := (rfl)

@[simp]
theorem dedekindZetaData_conductor :
    (dedekindZetaData K).conductor =
      ⟨(discr K).natAbs, Int.natAbs_pos.mpr (discr_ne_zero K)⟩ := (rfl)

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

/-- The degree of the Dedekind zeta card is the field degree `[K : ℚ] = r₁ + 2 r₂`. -/
@[simp]
theorem dedekindZetaData_degree : (dedekindZetaData K).degree = Module.finrank ℚ K := by
  simp only [AnalyticLFunctionData.degree_def, dedekindZetaData_gammaR, dedekindZetaData_gammaC,
    Multiset.card_replicate]
  exact InfinitePlace.card_add_two_mul_card_eq_rank K

/-- The gamma factor of the Dedekind zeta card is `Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂`. -/
@[simp]
theorem dedekindZetaData_gammaFactor (s : ℂ) :
    (dedekindZetaData K).gammaFactor s =
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K := by
  simp [AnalyticLFunctionData.gammaFactor_def]

/-- The Dedekind zeta coefficients satisfy the average absolute growth bound. -/
theorem dedekindZetaData_hasAverageCoefficientGrowth :
    (dedekindZetaData K).HasAverageCoefficientGrowth := by
  rw [AnalyticLFunctionData.hasAverageCoefficientGrowth_iff_abscissaOfAbsConv_le]
  have h : (dedekindZetaData K).coeff = ⇑(normCoeff K (1 : IdealArithmeticFunction K)) := rfl
  rw [h, abscissaOfAbsConv_normCoeff_one K]

/-- The Dedekind zeta card is self-dual. -/
@[simp]
theorem dedekindZetaData_dual : (dedekindZetaData K).dual = dedekindZetaData K := by
  ext
  · simp only [AnalyticLFunctionData.dual_coeff, dedekindZetaData_coeff, normCoeff_one_apply]
    split_ifs <;> simp
  · exact AnalyticLFunctionData.dual_conductor _
  · simp
  · simp
  · simp
  · simp [completedDedekindZeta_conj]
  · simp [Finsupp.single_apply, eq_comm (a := (0 : ℂ)), eq_comm (a := (1 : ℂ)),
      map_eq_one_iff _ (starRingEnd ℂ).injective]

/-- On `Re s > 1`, `completedDedekindZeta K` agrees with the completed Dirichlet series of
`dedekindZetaData K`. -/
theorem dedekindZetaData_hasDirichletAgreement :
    (dedekindZetaData K).HasDirichletAgreement where
  coeff_one := by
    simp [normCoeff_apply_one]
  degree_pos := by
    rw [dedekindZetaData_degree]
    exact Module.finrank_pos
  completed_eq s hs := by
    have hcoeff : (dedekindZetaData K).coeff = ⇑(normCoeff K (1 : IdealArithmeticFunction K)) := rfl
    have hcond : (((dedekindZetaData K).conductor : ℕ) : ℂ) = ((|discr K| : ℤ) : ℂ) := by
      simp only [dedekindZetaData_conductor, PNat.mk_coe]
      rw [← Int.cast_natCast, Int.natCast_natAbs]
    rw [dedekindZetaData_completed, completedDedekindZeta_eq hs, hcond,
      dedekindZetaData_gammaFactor, hcoeff, dedekindZeta_eq_LSeries_normCoeff_one K s]
    ring

/-- The completed Dedekind zeta function is meromorphic on `ℂ` with simple poles at `0` and `1`
and no other singularities. -/
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

/-- The completed Dedekind zeta function satisfies the functional equation `Λ_K(s) = Λ_K(1 - s)`
with root number `1`. -/
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

/-- Constructing the Dedekind zeta card from its Dirichlet series via
`AnalyticLFunctionData.ofSeries` recovers `dedekindZetaData K` identically, because
`completedDedekindZeta K` is already in meromorphic normal form on `ℂ`. In particular, the
extracted root number is `1`. -/
theorem ofSeries_dedekindZetaData :
    AnalyticLFunctionData.ofSeries (dedekindZetaData K).coeff (dedekindZetaData K).conductor
      (dedekindZetaData K).gammaR (dedekindZetaData K).gammaC (dedekindZetaData K).polarOrder =
      dedekindZetaData K := by
  refine AnalyticLFunctionData.ofSeries_eq (dedekindZetaData_hasDirichletAgreement K)
    (dedekindZetaData_hasFunctionalEquation K) (meromorphicNFOn_completedDedekindZeta K)
    (by simp) ?_
  rw [dedekindZetaData_completed, completedDedekindZeta_eq (by norm_num : 1 < (2 : ℂ).re)]
  have hd : ((|discr K| : ℤ) : ℂ) ^ ((2 : ℂ) / 2) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (Int.cast_ne_zero.mpr (abs_ne_zero.mpr (discr_ne_zero K))))
  have hΓℝ : Gammaℝ 2 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hΓℂ : Gammaℂ 2 ≠ 0 := by
    rw [← Gammaℝ_mul_Gammaℝ_add_one]
    exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos (by norm_num))
      (Gammaℝ_ne_zero_of_re_pos (by norm_num))
  have hζ : NumberField.dedekindZeta K 2 ≠ 0 :=
    TauCeti.dedekindZeta_ne_zero_of_one_lt_re (by norm_num)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hd (pow_ne_zero _ hΓℝ)) (pow_ne_zero _ hΓℂ)) hζ

end TauCeti.LFunctions
