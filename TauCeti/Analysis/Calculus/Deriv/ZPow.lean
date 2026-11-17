/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Derivative steps for iterated derivatives of `x ↦ x⁻¹`

This file records the one-step `HasDerivAt` identity for the explicit iterated derivatives of
`x ↦ x⁻¹`, continuing Mathlib's `Mathlib/Analysis/Calculus/Deriv/ZPow.lean` and complementing
`iter_deriv_inv` (which gives `deriv^[k]` without proving `HasDerivAt`).

## Main results

* `TauCeti.hasDerivAt_neg_one_pow_mul_factorial_mul_zpow`: at every nonzero `x` in a
  nontrivially normed field, `y ↦ (-1) ^ i * i ! * y ^ (-(i + 1 : ℤ))` has derivative
  `(-1) ^ (i + 1) * (i + 1)! * x ^ (-((i + 1 : ℕ) + 1 : ℤ))`.
-/

public section

open scoped Nat

namespace TauCeti

/-- Derivative step for the `i`-th derivative of `y ↦ y⁻¹`: at every nonzero `x` in a
nontrivially normed field, `y ↦ (-1) ^ i * i ! * y ^ (-(i + 1 : ℤ))` has derivative
`(-1) ^ (i + 1) * (i + 1)! * x ^ (-((i + 1 : ℕ) + 1 : ℤ))`. -/
theorem hasDerivAt_neg_one_pow_mul_factorial_mul_zpow {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (i : ℕ) {x : 𝕜} (hx : x ≠ 0) :
    HasDerivAt (fun y : 𝕜 => (-1 : 𝕜) ^ i * i ! * y ^ (-(i + 1 : ℤ)))
      ((-1 : 𝕜) ^ (i + 1) * (i + 1)! * x ^ (-((i + 1 : ℕ) + 1 : ℤ))) x := by
  have hd := (hasDerivAt_zpow (-(i + 1 : ℤ)) x (Or.inl hx)).const_mul ((-1 : 𝕜) ^ i * i !)
  refine hd.congr_deriv ?_
  rw [Nat.factorial_succ, pow_succ,
    show (-(i + 1 : ℤ) - 1 : ℤ) = -((i + 1 : ℕ) + 1 : ℤ) by omega]
  push_cast
  ring

end TauCeti
