/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Derivatives of integer powers and reciprocal powers

This file extends `Mathlib.Analysis.Calculus.Deriv.ZPow` with the derivative rule for `c / f y ^ m`
(`HasDerivAt.const_div_pow`), computed via `hasDerivAt_zpow`.
-/

public section

/-- The derivative of `y ↦ c / f y ^ m` at a point `x` where `f x ≠ 0` and `f` has derivative
`f'`, computed via `hasDerivAt_zpow`. -/
theorem HasDerivAt.const_div_pow {𝕜' 𝕜 : Type*} [NontriviallyNormedField 𝕜']
    [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜' 𝕜] {f : 𝕜' → 𝕜} {f' : 𝕜} {x : 𝕜'}
    (hf : HasDerivAt f f' x) (hfx : f x ≠ 0) (c : 𝕜) (m : ℕ) :
    HasDerivAt (fun y ↦ c / f y ^ m) (-(m : 𝕜) * c * f' / f x ^ (m + 1)) x := by
  have hz := ((hasDerivAt_zpow (-(m : ℤ)) (f x) (Or.inl hfx)).scomp x hf).const_mul c
  refine (hz.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)).congr_deriv ?_
  · simp [zpow_neg, zpow_natCast, div_eq_mul_inv]
  · have hexp : -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) := by omega
    rw [hexp, smul_eq_mul, zpow_neg, zpow_natCast]
    simp only [Int.cast_neg, Int.cast_natCast]
    ring
