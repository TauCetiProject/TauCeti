/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Growth
public import TauCeti.NumberTheory.LFunctions.Data.Series
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Card
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic

/-!
# Average growth and `ofSeries` recovery for the Dedekind zeta card

This downstream module proves that `TauCeti.LFunctions.dedekindZetaData K` satisfies
`HasAverageCoefficientGrowth` and is recovered identically by `AnalyticLFunctionData.ofSeries`,
keeping the card's growth and `ofSeries` results separate from
`TauCeti.NumberTheory.LFunctions.DedekindZeta.Card`.

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
  rw [(dedekindZetaData_hasDirichletAgreement K).completed_eq 2 (by norm_num)]
  have hN : ((((dedekindZetaData K).conductor : ℕ) : ℂ) ^ ((2 : ℂ) / 2)) ≠ 0 :=
    (dedekindZetaData K).conductor_cpow_ne_zero _
  have hγ : (dedekindZetaData K).gammaFactor 2 ≠ 0 :=
    dedekindZetaData_gammaFactor_ne_zero K (by norm_num)
  have hL : LSeries (dedekindZetaData K).coeff 2 ≠ 0 := by
    rw [funext (dedekindZetaData_coeff K), ← dedekindZeta_eq_LSeries_normCoeff_one K 2]
    exact TauCeti.dedekindZeta_ne_zero_of_one_lt_re (by norm_num)
  exact mul_ne_zero (mul_ne_zero hN hγ) hL

end TauCeti.LFunctions
