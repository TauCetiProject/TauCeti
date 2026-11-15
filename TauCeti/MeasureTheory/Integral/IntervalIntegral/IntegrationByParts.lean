/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Substituting `u = x²` in an interval integral

On an interval of nonnegative reals the map `x ↦ x²` is monotone with derivative `2 x ≥ 0`, so
Mathlib's change of variables `intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg` applies
to any integrand `g`, with no continuity or integrability hypothesis on `g`:
`∫ x in a..b, g (x²) * (2 x) = ∫ u in a²..b², g u`.

## Main declarations

* `TauCeti.intervalIntegral.integral_comp_sq_mul`
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace intervalIntegral

/-- **Substituting `u = x²`.** For `0 ≤ a` and `0 ≤ b`,
`∫ x in a..b, g (x²) * (2 x) = ∫ u in a²..b², g u` for every `g : ℝ → ℝ`. -/
theorem integral_comp_sq_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (g : ℝ → ℝ) :
    ∫ x in a..b, g (x ^ 2) * (2 * x) = ∫ u in a ^ 2..b ^ 2, g u :=
  _root_.intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (f := fun x => x ^ 2)
    (by fun_prop) (fun x _ => by simpa using hasDerivAt_pow 2 x) fun x hx => by
      linarith [(le_min ha hb).trans_lt hx.1]

end intervalIntegral

end TauCeti
