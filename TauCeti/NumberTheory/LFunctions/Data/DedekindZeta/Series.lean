/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.DedekindZeta
public import TauCeti.NumberTheory.LFunctions.Data.Series
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic

/-!
# `ofSeries` recovery for the Dedekind zeta card

This downstream module proves that `TauCeti.LFunctions.dedekindZetaData K` is uniquely
reconstructed from its Dirichlet coefficients, conductor, gamma shifts, and polar divisor via
`AnalyticLFunctionData.ofSeries`, recovering the same completed function (in meromorphic normal
form at `0` and `1`) and root number `1` while keeping the Euler-product nonvanishing dependency
separate from `TauCeti.NumberTheory.LFunctions.Data.DedekindZeta`.

## Main results

* `TauCeti.LFunctions.ofSeries_dedekindZetaData`: exact normal-form and root-number recovery via
  `AnalyticLFunctionData.ofSeries`.
-/

public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/- Adapted from `TauCeti.LFunctions.ofSeries_riemannZetaData`
(`TauCeti.NumberTheory.LFunctions.Data.RiemannZeta`). -/

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
  have hγ : (dedekindZetaData K).gammaFactor 2 ≠ 0 := by
    rw [dedekindZetaData_gammaFactor]
    exact mul_ne_zero (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos (by norm_num)))
      (pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos (by norm_num)))
  have hL : LSeries (dedekindZetaData K).coeff 2 ≠ 0 := by
    rw [funext (dedekindZetaData_coeff K), ← dedekindZeta_eq_LSeries_dedekindZetaCoeff K 2]
    exact TauCeti.dedekindZeta_ne_zero_of_one_lt_re (by norm_num)
  exact mul_ne_zero (mul_ne_zero hN hγ) hL

end TauCeti.LFunctions
