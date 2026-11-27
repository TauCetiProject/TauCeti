/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Derivatives of power-logarithm products

Away from zero, differentiating the product of a real or complex power with the real natural
logarithm yields `(r * log x + 1) * x ^ (r - 1)`. Because both `Real.hasDerivAt_log` and
`Real.hasDerivAt_rpow_const` / `hasDerivAt_ofReal_cpow_const` hold at every nonzero real point,
no sign restriction on `x` is needed; the case `r = 0` also holds without extra hypothesis since
`(x : ℂ) ^ 0 = 1` and `(x : ℂ) ^ (-1) = x⁻¹`.

These identities arise directly as antiderivatives when integrating by parts against logarithmic
weights, for instance in Abel summation of Dirichlet-series derivatives and in evaluating
improper integrals of `t ^ a * log t`.

## Main results

* `Real.hasDerivAt_rpow_mul_log`: derivative of `y ↦ y ^ r * Real.log y` for any `r : ℝ` and
  `x ≠ 0`.
* `Complex.hasDerivAt_ofReal_cpow_mul_log`: derivative of `y ↦ (y : ℂ) ^ r * Real.log y` for any
  `r : ℂ` and `x ≠ 0`.
-/

public section

namespace Real

/-- For any real exponent `r` and nonzero `x : ℝ`, the derivative of `y ↦ y ^ r * log y` at `x`
is `(r * log x + 1) * x ^ (r - 1)`. -/
theorem hasDerivAt_rpow_mul_log (r : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ y ^ r * Real.log y) ((r * Real.log x + 1) * x ^ (r - 1)) x := by
  have hpow := Real.hasDerivAt_rpow_const (x := x) (p := r) (Or.inl hx)
  have hlog := Real.hasDerivAt_log hx
  refine (hpow.mul hlog).congr_deriv ?_
  have hinv : x ^ r * x⁻¹ = x ^ (r - 1) := by
    rw [Real.rpow_sub_one hx, div_eq_mul_inv]
  rw [hinv]
  ring

end Real

namespace Complex

/-- For any complex exponent `r` and nonzero `x : ℝ`, the derivative of
`y ↦ (y : ℂ) ^ r * log y` at `x` is `(r * log x + 1) * (x : ℂ) ^ (r - 1)`. -/
theorem hasDerivAt_ofReal_cpow_mul_log (r : ℂ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ r * Real.log y)
      ((r * Real.log x + 1) * (x : ℂ) ^ (r - 1)) x := by
  have hlog : HasDerivAt (fun y : ℝ ↦ (Real.log y : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
    (Real.hasDerivAt_log hx).ofReal_comp
  rcases eq_or_ne r 0 with rfl | hr
  · simpa [Complex.cpow_neg_one] using hlog
  · have hpow := hasDerivAt_ofReal_cpow_const hx hr
    refine (hpow.mul hlog).congr_deriv ?_
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    have hinv : (x : ℂ) ^ r * ((x⁻¹ : ℝ) : ℂ) = (x : ℂ) ^ (r - 1) := by
      rw [Complex.ofReal_inv, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hxC,
        ← sub_eq_add_neg]
    rw [hinv]
    ring

end Complex
