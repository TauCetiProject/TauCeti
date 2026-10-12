/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

import Mathlib.Data.ZMod.Basic

/-!
# A congruence between the divisor sums `σ₃` and `σ₅`

For every `n`, the integer `5 σ₃(n) + 7 σ₅(n)` is divisible by `12`. Termwise,
`5 d³ + 7 d⁵ = d³ (5 + 7 d²)` is divisible by `12` for every `d`: modulo `3` either `d ≡ 0` or
`d² ≡ 1`, and modulo `4` either `d` is even, so `8 ∣ d³`, or `d² ≡ 1`; in both cases
`5 + 7 = 12`.

This is what makes `-(5 s₃(q) + 7 s₅(q)) / 12`, the coefficient `a₆` of the Tate curve, a power
series with integer coefficients, so that the Tate curve is defined over `ℤ⟦q⟧` and specialises
to every ring, residue characteristics `2` and `3` included.

## Main results

* `TauCeti.twelve_dvd_five_mul_sigma_three_add_seven_mul_sigma_five`:
  `12 ∣ 5 σ₃(n) + 7 σ₅(n)`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, §V.3.
-/

public section

namespace TauCeti

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- **`5 σ₃(n) + 7 σ₅(n)` is divisible by `12`.** -/
theorem twelve_dvd_five_mul_sigma_three_add_seven_mul_sigma_five (n : ℕ) :
    12 ∣ 5 * σ 3 n + 7 * σ 5 n := by
  have key : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  rw [← ZMod.natCast_eq_zero_iff, sigma_apply, sigma_apply, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  push_cast
  exact Finset.sum_eq_zero fun d _ ↦ key d

end TauCeti

end
