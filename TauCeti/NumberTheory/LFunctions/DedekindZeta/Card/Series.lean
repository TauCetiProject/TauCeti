/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Growth
public import TauCeti.NumberTheory.LFunctions.Data.Series
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Card
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.NumberField.Discriminant.Basic

/-!
# Average growth and `ofSeries` recovery for the Dedekind zeta card

This downstream module proves that `TauCeti.LFunctions.dedekindZetaData K` satisfies
`HasAverageCoefficientGrowth` and is recovered identically by `AnalyticLFunctionData.ofSeries`.
Keeping these results separate from `TauCeti.NumberTheory.LFunctions.DedekindZeta.Card` avoids
loading coefficient-growth and Euler-product machinery when importing the analytic continuation.

The `ofSeries` recovery proof is adapted from `TauCeti.LFunctions.ofSeries_riemannZetaData`
(`TauCeti.NumberTheory.LFunctions.Data.RiemannZeta`).

## Main results

* `TauCeti.LFunctions.dedekindZetaData_hasAverageCoefficientGrowth`: average coefficient growth of
  `dedekindZetaData K`.
* `TauCeti.LFunctions.ofSeries_dedekindZetaData`: exact normal-form recovery via
  `AnalyticLFunctionData.ofSeries`.
-/

public section

noncomputable section

open Complex NumberField

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- The Dedekind zeta coefficients satisfy the average absolute growth bound. -/
theorem dedekindZetaData_hasAverageCoefficientGrowth :
    (dedekindZetaData K).HasAverageCoefficientGrowth := by
  rw [AnalyticLFunctionData.hasAverageCoefficientGrowth_iff_abscissaOfAbsConv_le,
    funext (dedekindZetaData_coeff K), abscissaOfAbsConv_normCoeff_one K]

/-- Supplying the coefficients, conductor, gamma shifts, and polar divisor of `dedekindZetaData K`
to `AnalyticLFunctionData.ofSeries` recovers `dedekindZetaData K` identically, including both the
completed function (in meromorphic normal form at `0` and `1`) and the root number `1`. -/
theorem ofSeries_dedekindZetaData :
    AnalyticLFunctionData.ofSeries (dedekindZetaData K).coeff (dedekindZetaData K).conductor
      (dedekindZetaData K).gammaR (dedekindZetaData K).gammaC (dedekindZetaData K).polarOrder =
      dedekindZetaData K := by
  refine AnalyticLFunctionData.ofSeries_eq (dedekindZetaData_hasDirichletAgreement K)
    (dedekindZetaData_hasFunctionalEquation K)
    (by rw [dedekindZetaData_completed]; exact meromorphicNFOn_completedDedekindZeta K)
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
