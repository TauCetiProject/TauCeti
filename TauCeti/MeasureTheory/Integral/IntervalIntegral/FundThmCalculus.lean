/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The fundamental theorem of calculus for nonnegative derivatives

Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` evaluates `∫ x in a..b, f x` as
`F b - F a` for an antiderivative `F` that is continuous on `[a, b]`, provided `f` is interval
integrable. When `f` is nonnegative on `(a, b)` the integrability is automatic
(`intervalIntegral.integrableOn_deriv_of_nonneg`), which matters for integrands that are unbounded
at an endpoint, such as `1 / √(x - a)`. This file records the combined statement.

## Main declarations

* `TauCeti.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg`
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace intervalIntegral

/-- **FTC-2 for a nonnegative derivative.** If `F` is continuous on `[a, b]` and has derivative
`f x ≥ 0` at every `x ∈ (a, b)`, then `∫ x in a..b, f x = F b - F a`; the integrability of `f`
is a consequence rather than a hypothesis. -/
theorem integral_eq_sub_of_hasDerivAt_of_le_of_nonneg {F f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hf : ∀ x ∈ Ioo a b, 0 ≤ f x) : ∫ x in a..b, f x = F b - F a :=
  _root_.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF hd
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (_root_.intervalIntegral.integrableOn_deriv_of_nonneg hF hd hf))

end intervalIntegral

end TauCeti
