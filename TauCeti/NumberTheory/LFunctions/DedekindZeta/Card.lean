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
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.NumberField.Discriminant.Basic

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
`HasFunctionalEquation`, and shows that supplying its coefficients, conductor, gamma shifts, and
polar divisor to `AnalyticLFunctionData.ofSeries` recovers both the completed function (including
canonical normal-form values at `0` and `1`) and the root number `1`.

The card definition and the self-duality, meromorphic-continuation, functional-equation, and
`ofSeries`-recovery proofs are closely adapted from `TauCeti.LFunctions.riemannZetaData`
(`TauCeti.NumberTheory.LFunctions.Data.RiemannZeta`) as their formal template.

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
  rw [AnalyticLFunctionData.hasAverageCoefficientGrowth_iff_abscissaOfAbsConv_le,
    funext (dedekindZetaData_coeff K), abscissaOfAbsConv_normCoeff_one K]

/-- The Dedekind zeta card is self-dual. -/
@[simp]
theorem dedekindZetaData_dual : (dedekindZetaData K).dual = dedekindZetaData K := by
  ext s
  · simp only [AnalyticLFunctionData.dual_coeff, dedekindZetaData_coeff, normCoeff_one_apply]
    split_ifs <;> simp
  · exact AnalyticLFunctionData.dual_conductor _
  · simp
  · simp
  · simp
  · simp [completedDedekindZeta_conj]
  · simp [AnalyticLFunctionData.single_zero_add_single_one_conj]

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
    have hcoeff : (dedekindZetaData K).coeff = ⇑(normCoeff K (1 : IdealArithmeticFunction K)) :=
      funext (dedekindZetaData_coeff K)
    have hcond : (((dedekindZetaData K).conductor : ℕ) : ℂ) = ((|discr K| : ℤ) : ℂ) := by
      simp only [dedekindZetaData_conductor, PNat.mk_coe]
      rw [← Int.cast_natCast, Int.natCast_natAbs]
    rw [dedekindZetaData_completed, completedDedekindZeta_eq hs, hcond,
      dedekindZetaData_gammaFactor, hcoeff, dedekindZeta_eq_LSeries_normCoeff_one K s]
    ring

/-- The completed Dedekind zeta function is meromorphic on `ℂ` with simple poles at `0` and `1`
and no other singularities. -/
theorem dedekindZetaData_hasMeromorphicContinuation :
    (dedekindZetaData K).HasMeromorphicContinuation :=
  AnalyticLFunctionData.hasMeromorphicContinuation_of_simple_poles_zero_one
    (dedekindZetaData_polarOrder K) (meromorphic_completedDedekindZeta K)
    (meromorphicOrderAt_completedDedekindZeta_zero K)
    (meromorphicOrderAt_completedDedekindZeta_one K)
    fun _ h0 h1 ↦ analyticAt_completedDedekindZeta h0 h1

/-- The completed Dedekind zeta function satisfies the functional equation `Λ_K(s) = Λ_K(1 - s)`
with root number `1`. -/
theorem dedekindZetaData_hasFunctionalEquation :
    (dedekindZetaData K).HasFunctionalEquation where
  norm_rootNumber := by simp
  polarOrder_one_sub_conj s := by
    simpa only [dedekindZetaData_polarOrder] using
      AnalyticLFunctionData.single_zero_add_single_one_one_sub_conj s
  completed_eq s _ _ := by
    rw [dedekindZetaData_dual, dedekindZetaData_rootNumber, one_mul, dedekindZetaData_completed,
      completedDedekindZeta_one_sub]

/-- Supplying the coefficients, conductor, gamma shifts, and polar divisor of `dedekindZetaData K`
to `AnalyticLFunctionData.ofSeries` recovers `dedekindZetaData K` identically, including both the
completed function (in meromorphic normal form at `0` and `1`) and the root number `1`. -/
theorem ofSeries_dedekindZetaData :
    AnalyticLFunctionData.ofSeries (dedekindZetaData K).coeff (dedekindZetaData K).conductor
      (dedekindZetaData K).gammaR (dedekindZetaData K).gammaC (dedekindZetaData K).polarOrder =
      dedekindZetaData K := by
  refine AnalyticLFunctionData.ofSeries_eq (dedekindZetaData_hasDirichletAgreement K)
    (dedekindZetaData_hasFunctionalEquation K) (meromorphicNFOn_completedDedekindZeta K)
    (by simp) ?_
  rw [dedekindZetaData_completed, completedDedekindZeta_eq (by norm_num : 1 < (2 : ℂ).re)]
  have hd : ((|discr K| : ℤ) : ℂ) ^ ((2 : ℂ) / 2) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (NumberField.cast_abs_discr_ne_zero K))
  have hΓℝ : Gammaℝ 2 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hΓℂ : Gammaℂ 2 ≠ 0 := Gammaℂ_ne_zero_of_re_pos (by norm_num)
  have hζ : NumberField.dedekindZeta K 2 ≠ 0 :=
    TauCeti.dedekindZeta_ne_zero_of_one_lt_re (by norm_num)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hd (pow_ne_zero _ hΓℝ)) (pow_ne_zero _ hΓℂ)) hζ

end TauCeti.LFunctions
