/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
public import TauCeti.NumberTheory.LFunctions.PrimeIdealBoundary

/-!
# Prime ideal boundary series for the continued Dedekind zeta function

`primeIdealVonMangoldtBoundary_series_eq` identifies the series in the boundary datum for
the prime ideal theorem with the negative logarithmic derivative of the continued Dedekind
zeta function. The Dirichlet-series formula
`TauCeti.LFunctions.primeIdealVonMangoldtBoundary_series` transfers to the continuation by
Mathlib's `logDeriv_congr_nhds` and
`TauCeti.LFunctions.dedekindZetaC_eventuallyEq_dedekindZeta`.
-/

public section

open Filter NumberField

namespace TauCeti.LFunctions

/-- On `Re s > 1`, the series in the prime ideal boundary datum equals the negative
logarithmic derivative of the continued Dedekind zeta function. -/
theorem primeIdealVonMangoldtBoundary_series_eq {K : Type*} [Field K] [NumberField K]
    (s : {s : ℂ // 1 < s.re}) :
    (primeIdealVonMangoldtBoundary K).series s = -logDeriv (dedekindZetaC K) (s : ℂ) := by
  rw [primeIdealVonMangoldtBoundary_series, neg_div, ← logDeriv_apply,
    (logDeriv_congr_nhds (dedekindZetaC_eventuallyEq_dedekindZeta K s.property)).eq_of_nhds]

end TauCeti.LFunctions
