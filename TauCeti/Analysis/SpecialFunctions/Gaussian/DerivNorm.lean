/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gaussian.Harmonic
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.SpecialFunctions.Gaussian.Moments

/-!
# The `L²` norm of the derivative of a Gaussian on `ℝ`

For the Gaussian `g(x) = exp(-b x²)` on `ℝ`, `0 < Re b`, the derivative is `g' = -2b x g`
(`SchwartzMap.lineDerivOp_gaussian`) and `|g|² = exp(-2 Re b x²)`, so the second Gaussian moment
gives `‖g'‖²_{L²} = √(π / (2 Re b)) |b|² / Re b`. Together with the squared `L²` norm
`√(π / (2 Re b))` of `g` (`TauCeti.norm_toLp_gaussian_sq`), this evaluates the weak-derivative
norm `‖g‖²_{L²} + ‖g'‖²_{L²} = √(π / (2 Re b)) (1 + |b|² / Re b)`.

## Main results

* `TauCeti.norm_toLp_lineDerivOp_one_gaussian_sq`: `‖g'‖²_{L²} = √(π / (2 Re b)) |b|² / Re b`.
* `TauCeti.norm_toLp_gaussian_sq_add_norm_toLp_lineDerivOp_one_gaussian_sq`:
  `‖g‖²_{L²} + ‖g'‖²_{L²} = √(π / (2 Re b)) (1 + |b|² / Re b)`.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap LineDeriv Real

namespace TauCeti

/-- **The `L²` norm of the derivative of a Gaussian.** For `g(x) = exp(-b x²)` on `ℝ`,
`0 < Re b`, `‖g'‖²_{L²} = ∫ |∂ₓ exp(-b x²)|² dx = √(π / (2 Re b)) |b|² / Re b`. -/
theorem norm_toLp_lineDerivOp_one_gaussian_sq {b : ℂ} (hb : 0 < b.re) :
    ‖(∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb : 𝓢(ℝ, ℂ))).toLp 2‖ ^ 2 =
      √(π / (2 * b.re)) * (‖b‖ ^ 2 / b.re) := by
  rw [SchwartzMap.norm_toLp_sq]
  have h (x : ℝ) : ‖∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb : 𝓢(ℝ, ℂ)) x‖ ^ 2 =
      4 * ‖b‖ ^ 2 * (x ^ (2 * 1) * Real.exp (-(2 * b.re) * x ^ 2)) := by
    -- `∂ₓ g = -2b x g`, and `|g|² = exp (-2 Re b x²)`; the power `x ^ (2 * 1)` matches the
    -- case `m = 1` of `integral_pow_two_mul_mul_exp_neg_mul_sq`.
    rw [SchwartzMap.lineDerivOp_gaussian, smul_apply,
      SchwartzMap.innerMulGaussian_apply, ← SchwartzMap.gaussian_apply hb]
    simp only [smul_eq_mul, norm_mul, mul_pow, SchwartzMap.norm_gaussian_apply_sq]
    norm_num
  rw [funext h, integral_const_mul, integral_pow_two_mul_mul_exp_neg_mul_sq]
  simp only [mul_one, Nat.factorial_two, Nat.factorial_one, Nat.cast_ofNat, Nat.cast_one, pow_one]
  field_simp
  ring

/-- **The `W^{1,2}` norm of a Gaussian.** For `g(x) = exp(-b x²)` on `ℝ`, `0 < Re b`,
`‖g‖²_{L²} + ‖g'‖²_{L²} = √(π / (2 Re b)) (1 + |b|² / Re b)`. Compared with
`TauCeti.norm_toBesselPotentialSpaceCLM_one_gaussian_sq`, the derivative term carries the factor
`(2π)²`. -/
theorem norm_toLp_gaussian_sq_add_norm_toLp_lineDerivOp_one_gaussian_sq {b : ℂ}
    (hb : 0 < b.re) :
    ‖(SchwartzMap.gaussian (V := ℝ) hb).toLp 2‖ ^ 2 +
        ‖(∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb : 𝓢(ℝ, ℂ))).toLp 2‖ ^ 2 =
      √(π / (2 * b.re)) * (1 + ‖b‖ ^ 2 / b.re) := by
  rw [norm_toLp_gaussian_sq, Module.finrank_self, Nat.cast_one, ← Real.sqrt_eq_rpow,
    norm_toLp_lineDerivOp_one_gaussian_sq]
  ring

end TauCeti
