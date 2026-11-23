/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Analytic.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Order

/-!
# Analyticity of the complex digamma function

Mathlib's complex digamma function `ψ = Complex.digamma` is the logarithmic derivative of `Γ`.
Away from the nonpositive integers `Γ` is analytic and nonzero, so `ψ = Γ′/Γ` is analytic there,
in particular on the right half-plane.

## Main results

* `Complex.analyticAt_digamma`: complex digamma is analytic away from the nonpositive integers.
* `Complex.analyticOnNhd_digamma_re_pos`: complex digamma is analytic on the right half-plane.
-/

public section

namespace Complex

/-- The digamma function is analytic at every `s` that is not a nonpositive integer. -/
theorem analyticAt_digamma {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) : AnalyticAt ℂ digamma s := by
  have h := (analyticAt_Gamma hs).deriv.div (analyticAt_Gamma hs) (Gamma_ne_zero hs)
  simpa only [digamma_def, logDeriv, Pi.div_def] using h

/-- The digamma function is analytic on the right half-plane `0 < Re s`. -/
theorem analyticOnNhd_digamma_re_pos : AnalyticOnNhd ℂ digamma {s : ℂ | 0 < s.re} :=
  fun _ hs => analyticAt_digamma (ne_neg_natCast_of_re_pos hs)

end Complex
