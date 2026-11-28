/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.DedekindZeta
public import TauCeti.NumberTheory.LFunctions.Data.Series
import TauCeti.NumberTheory.LFunctions.DedekindZeta.TrivialZeros

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
  rw [dedekindZetaData_completed, ← completedDedekindZeta_one_sub K (2 : ℂ)]
  exact completedDedekindZeta_ne_zero_of_re_neg K (by norm_num)

end TauCeti.LFunctions
