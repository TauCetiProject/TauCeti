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

* `TauCeti.divisorSumSeries k`: the power series with `n`-th coefficient `σ k n`.
-/

public section

open PowerSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

/-- The divisor-sum series `s_k(q) = ∑_{n ≥ 1} σ_k(n) qⁿ` in `ℤ⟦q⟧`, the power series expansion of
the Lambert series `∑_{n ≥ 1} nᵏ qⁿ / (1 - qⁿ)`. Its constant coefficient is `σ_k(0) = 0`. -/
noncomputable def divisorSumSeries (k : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n ↦ (σ k n : ℤ)

@[simp]
theorem coeff_divisorSumSeries (k n : ℕ) : coeff n (divisorSumSeries k) = σ k n := by
  simp [divisorSumSeries]

@[simp]
theorem constantCoeff_divisorSumSeries (k : ℕ) : constantCoeff (divisorSumSeries k) = 0 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

end TauCeti

end
