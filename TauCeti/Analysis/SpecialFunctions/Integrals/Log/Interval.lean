/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Closed-form logarithmic interval integrals

When the closed unordered interval `[[a, b]]` avoids `0`, the substitution `u = log t` evaluates
`∫ t in a..b, (log t) ^ k / t` in closed form as
`((log b) ^ (k + 1) - (log a) ^ (k + 1)) / (k + 1)`.

## Main declarations

* `TauCeti.integral_log_pow_div_self`:
  `∫ t in a..b, (log t) ^ k / t = ((log b) ^ (k + 1) - (log a) ^ (k + 1)) / (k + 1)` when
  `0 ∉ [[a, b]]`.
-/

public section

namespace TauCeti

/-- When the interval `[[a, b]]` avoids `0`, the interval integral
`∫ t in a..b, (log t) ^ k / t` evaluates to `((log b) ^ (k + 1) - (log a) ^ (k + 1)) / (k + 1)`. -/
theorem integral_log_pow_div_self (k : ℕ) {a b : ℝ} (h : (0 : ℝ) ∉ Set.uIcc a b) :
    ∫ t : ℝ in a..b, Real.log t ^ k / t =
      (Real.log b ^ (k + 1) - Real.log a ^ (k + 1)) / (k + 1 : ℝ) := by
  have hne (t : ℝ) (ht : t ∈ Set.uIcc a b) : t ≠ 0 := fun ht0 ↦ h (ht0 ▸ ht)
  simpa [div_eq_mul_inv] using
    (intervalIntegral.integral_comp_mul_deriv (f := Real.log) (f' := fun t ↦ t⁻¹)
      (g := fun u ↦ u ^ k) (fun t ht ↦ Real.hasDerivAt_log (hne t ht))
      (continuousOn_inv₀.mono fun t ht ↦ hne t ht) (continuous_pow k)).trans
      (integral_pow (a := Real.log a) (b := Real.log b) k)

end TauCeti
