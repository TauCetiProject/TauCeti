/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import TauCeti.Analysis.Complex.NegNatTopology

/-!
# Complex analyticity of digamma

`Complex.digamma = logDeriv Complex.Gamma` is complex analytic away from the nonpositive integers
(`Complex.analyticAt_digamma`).

## Main results

* `Complex.analyticAt_digamma`: `AnalyticAt ℂ Complex.digamma s` wherever `∀ n : ℕ, s ≠ -(n : ℂ)`.
-/

public section

namespace Complex

/-- Complex digamma is analytic away from the nonpositive integers. -/
@[fun_prop]
theorem analyticAt_digamma {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) : AnalyticAt ℂ digamma s := by
  have hΓ : AnalyticAt ℂ Gamma s :=
    DifferentiableOn.analyticAt
      (fun z hz ↦ (differentiableAt_Gamma z hz).differentiableWithinAt)
      (isOpen_ne_neg_natCast.mem_nhds hs)
  simpa only [digamma_def, logDeriv, Pi.div_def] using hΓ.deriv.div hΓ (Gamma_ne_zero hs)

end Complex
