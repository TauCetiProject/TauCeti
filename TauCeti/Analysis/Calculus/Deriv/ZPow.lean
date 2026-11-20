/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Derivatives of reciprocal powers

The reciprocal power `w ↦ (w ^ n)⁻¹` is the integer power `w ^ (-n)`, so away from `0` its
derivative is `-n (w ^ (n + 1))⁻¹`. This is the form in which the terms `aₙ z⁻ⁿ` of a Poincaré
expansion at infinity are differentiated.

## Main results

* `hasDerivAt_inv_pow`: the derivative of `w ↦ (w ^ n)⁻¹` at `z ≠ 0` is `-n (z ^ (n + 1))⁻¹`.
-/

public section

/-- The derivative of `z ↦ (z ^ n)⁻¹` at `z ≠ 0` is `-n (z ^ (n + 1))⁻¹`. -/
theorem hasDerivAt_inv_pow {𝕜 : Type*} [NontriviallyNormedField 𝕜] {z : 𝕜} (hz : z ≠ 0)
    (n : ℕ) : HasDerivAt (fun w : 𝕜 => (w ^ n)⁻¹) (-(n : 𝕜) * (z ^ (n + 1))⁻¹) z := by
  convert hasDerivAt_zpow (-(n : ℤ)) z (Or.inl hz) using 1
  · funext w
    rw [zpow_neg, zpow_natCast]
  · have hexp : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
    rw [hexp, zpow_neg, zpow_natCast]
    push_cast
    ring
