/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Smoothness and derivatives of real powers of `1 - k² sin² θ`

For every real exponent `p`, the map `(k, θ) ↦ (1 - k² sin² θ) ^ p` is smooth on the open set
`{(k, θ) | k ^ 2 < 1}`, where its base is positive, and its partial derivative in `k` there is
`-2 p k sin² θ (1 - k² sin² θ) ^ (p - 1)`. The exponents `p = -1/2` and `p = 1/2` give the
integrands of Legendre's elliptic integrals of the first and second kind.
-/

public section

open Real

namespace TauCeti

/-- For every real exponent `p`, the map `(k, θ) ↦ (1 - k² sin² θ) ^ p` is smooth on
`{(k, θ) | k ^ 2 < 1}`. -/
theorem contDiffOn_one_sub_sq_mul_sin_sq_rpow {n : WithTop ℕ∞} (p : ℝ) :
    ContDiffOn ℝ n (fun z : ℝ × ℝ ↦ (1 - z.1 ^ 2 * sin z.2 ^ 2) ^ p)
      {z : ℝ × ℝ | z.1 ^ 2 < 1} :=
  (by fun_prop : ContDiff ℝ n fun z : ℝ × ℝ ↦ 1 - z.1 ^ 2 * sin z.2 ^ 2).contDiffOn
    |>.rpow_const_of_ne fun z hz ↦ (one_sub_mul_sin_sq_pos hz z.2).ne'

/-- For `k ^ 2 < 1` and every real exponent `p`, the derivative in `k` of
`(1 - k² sin² θ) ^ p` is `-2 p k sin² θ (1 - k² sin² θ) ^ (p - 1)`. -/
theorem hasDerivAt_one_sub_sq_mul_sin_sq_rpow {k : ℝ} (hk : k ^ 2 < 1) (p θ : ℝ) :
    HasDerivAt (fun k ↦ (1 - k ^ 2 * sin θ ^ 2) ^ p)
      (-(2 * p * k * sin θ ^ 2 * (1 - k ^ 2 * sin θ ^ 2) ^ (p - 1))) k := by
  have h := (((hasDerivAt_pow 2 k).mul_const (sin θ ^ 2)).const_sub 1).rpow_const
    (p := p) (Or.inl (one_sub_mul_sin_sq_pos hk θ).ne')
  exact h.congr_deriv (by push_cast; ring)

end TauCeti
