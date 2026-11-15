/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# A congruence between the divisor sums `σₖ` and `σₖ₊₂`

For every `k ≥ 2` and every `n`, the integer `5 σₖ(n) + 7 σₖ₊₂(n)` is divisible by `12`.
Termwise, `5 dᵏ + 7 dᵏ⁺² = dᵏ (5 + 7 d²)` is divisible by `12` for every `d`: modulo `3` either
`d ≡ 0` or `d² ≡ 1`, and modulo `4` either `d` is even, so `4 ∣ dᵏ`, or `d² ≡ 1`; in both cases
`5 + 7 = 12`. The case `k = 3` reads `12 ∣ 5 σ₃(n) + 7 σ₅(n)`.

This is what makes `-(5 s₃(q) + 7 s₅(q)) / 12`, the coefficient `a₆` of the Tate curve, a power
series with integer coefficients, so that the Tate curve is defined over `ℤ⟦q⟧` and specialises
to every ring, residue characteristics `2` and `3` included.

## Main results

* `TauCeti.twelve_dvd_five_mul_sigma_add_seven_mul_sigma_add_two`:
  `12 ∣ 5 σₖ(n) + 7 σₖ₊₂(n)` for `k ≥ 2`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, §V.3.
-/

public section

namespace TauCeti

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- **`5 σₖ(n) + 7 σₖ₊₂(n)` is divisible by `12` for `k ≥ 2`.** The case `k = 3` is the
congruence `12 ∣ 5 σ₃(n) + 7 σ₅(n)`. -/
theorem twelve_dvd_five_mul_sigma_add_seven_mul_sigma_add_two {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    12 ∣ 5 * σ k n + 7 * σ (k + 2) n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have key (x : ZMod 12) : 5 * x ^ (k + 2) + 7 * x ^ (k + 2 + 2) = 0 := by
    have h : 5 * x ^ 2 + 7 * x ^ 4 = 0 := by revert x; decide
    linear_combination x ^ k * h
  simp [← ZMod.natCast_eq_zero_iff, sigma_apply, Finset.mul_sum, ← Finset.sum_add_distrib, key]

end TauCeti

end
