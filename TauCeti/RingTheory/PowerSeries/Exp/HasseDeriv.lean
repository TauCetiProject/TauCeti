/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.HasseDeriv.Basic
public import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Hasse derivatives of the formal exponential

Over any `ℚ`-algebra, the `k`th Hasse derivative multiplies the formal exponential by `1 / k!`.
Combined with the chain rule for rescaling, this computes the divided derivatives
`D⁽ᵏ⁾ exp(xX) = (xᵏ / k!) exp(xX)` of rescaled exponentials, and hence of exponential sums
`∑ᵢ aᵢ exp(xᵢX)`.
-/

public section

open PowerSeries
open scoped Nat

namespace PowerSeries

/-- The exponential series is an eigenvector of every Hasse derivative: `D⁽ᵏ⁾ exp = exp / k!`. -/
@[simp]
theorem hasseDeriv_exp {A : Type*} [Ring A] [Algebra ℚ A] (k : ℕ) :
    hasseDeriv k (exp A) = (k ! : ℚ)⁻¹ • exp A := by
  have hQ : hasseDeriv k (exp ℚ) = (k ! : ℚ)⁻¹ • exp ℚ := by
    have h := factorial_smul_hasseDeriv k (exp ℚ)
    rw [Function.iterate_fixed (derivative_exp ℚ) k] at h
    have h' : (k ! : ℚ) • hasseDeriv k (exp ℚ) = exp ℚ := by
      simpa only [Nat.cast_smul_eq_nsmul] using h
    have hne : (k ! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using congrArg ((k ! : ℚ)⁻¹ • ·) h'
  rw [← map_exp (algebraMap ℚ A), hasseDeriv_map, hQ]
  ext n
  simp only [coeff_map, coeff_smul]
  simp [Algebra.smul_def]

end PowerSeries
