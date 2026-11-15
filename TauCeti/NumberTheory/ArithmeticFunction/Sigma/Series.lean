/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Divisor-sum power series

This file defines the generating series `s_k(q) = ∑_{n ≥ 1} σ_k(n) qⁿ` of the divisor-sum
function `σ k`.

## Main definitions

* `TauCeti.divisorSumSeries k`: the power series over a semiring with `n`-th coefficient
  `σ k n`.
-/

public section

open PowerSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

variable {R : Type*} [Semiring R]

/-- The divisor-sum series `s_k(q) = ∑_{n ≥ 1} σ_k(n) qⁿ` in `R⟦q⟧`, which over any semiring
equals `∑_{n ≥ 1} nᵏ ∑_{m ≥ 1} q^{nm}`; over a ring this is the expansion of the Lambert series
`∑_{n ≥ 1} nᵏ qⁿ / (1 - qⁿ)`. Its constant coefficient is `σ_k(0) = 0`. The coefficient
semiring `R` is implicit, determined by the expected type, as for `PowerSeries.X`. -/
noncomputable def divisorSumSeries (k : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun n ↦ (σ k n : R)

@[simp]
theorem coeff_divisorSumSeries (k n : ℕ) : coeff n (divisorSumSeries k : R⟦X⟧) = σ k n :=
  coeff_mk _ _

@[simp]
theorem constantCoeff_divisorSumSeries (k : ℕ) :
    constantCoeff (divisorSumSeries k : R⟦X⟧) = 0 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

end TauCeti

end
