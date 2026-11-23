/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Gaussian
import TauCeti.Analysis.SpecialFunctions.Gaussian.Harmonic

/-!
# The `2π` witness for `H^{1,2}(ℝ)`

For the Gaussian `g(x) = exp(-π x²)`, whose Fourier transform is itself, Mathlib's
Bessel-potential norm and the weak-derivative norm differ by the factor `(2π)²` on the derivative
term:

* `‖g‖²_{H^{1,2}} = (1 + 1 / (4π)) / √2`
  (`TauCeti.Examples.BesselPotential.norm_toBesselPotentialSpaceCLM_one_gaussian_pi_sq`);
* `‖g‖²_{L²} + ‖g'‖²_{L²} = (1 + π) / √2`
  (`TauCeti.Examples.BesselPotential.norm_toLp_gaussian_pi_sq_add_norm_toLp_lineDerivOp_sq`).

Both are the case `b = π` of the computations for `exp(-b x²)`, `0 < Re b`:
`TauCeti.norm_toBesselPotentialSpaceCLM_one_gaussian_sq` and
`TauCeti.Examples.BesselPotential.norm_toLp_gaussian_sq_add_norm_toLp_lineDerivOp_one_gaussian_sq`.
-/

public section

open scoped SchwartzMap BesselPotentialSpace LineDeriv Real

namespace TauCeti.Examples.BesselPotential

/-- **The `W^{1,2}` norm of a Gaussian.** For `g(x) = exp(-b x²)` on `ℝ`, `0 < Re b`,
`‖g‖²_{L²} + ‖g'‖²_{L²} = √(π / (2 Re b)) (1 + |b|² / Re b)`. Compared with
`TauCeti.norm_toBesselPotentialSpaceCLM_one_gaussian_sq`, the derivative term carries the factor
`(2π)²`. -/
theorem norm_toLp_gaussian_sq_add_norm_toLp_lineDerivOp_one_gaussian_sq {b : ℂ}
    (hb : 0 < b.re) :
    ‖(SchwartzMap.gaussian (V := ℝ) hb).toLp 2‖ ^ 2 +
        ‖(∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb : 𝓢(ℝ, ℂ))).toLp 2‖ ^ 2 =
      √(π / (2 * b.re)) * (1 + ‖b‖ ^ 2 / b.re) := by
  rw [norm_toLp_gaussian_sq, norm_toLp_lineDerivOp_one_gaussian_sq]
  ring

/-- The Gaussian `exp(-π x²)` on `ℝ` has `‖g‖²_{H^{1,2}} = (1 + 1 / (4π)) / √2`. -/
theorem norm_toBesselPotentialSpaceCLM_one_gaussian_pi_sq :
    ‖SchwartzMap.toBesselPotentialSpaceCLM (1 : ℝ) 2
        (SchwartzMap.gaussian (V := ℝ) (b := (π : ℂ)) Real.pi_pos)‖ ^ 2 =
      (1 + (4 * π)⁻¹) / √2 := by
  rw [norm_toBesselPotentialSpaceCLM_one_gaussian_sq, Complex.ofReal_re,
    div_mul_cancel_right₀ Real.pi_ne_zero, Real.sqrt_inv, Complex.norm_of_nonneg Real.pi_pos.le]
  field_simp

/-- The Gaussian `exp(-π x²)` on `ℝ` has `‖g‖²_{L²} + ‖g'‖²_{L²} = (1 + π) / √2`. -/
theorem norm_toLp_gaussian_pi_sq_add_norm_toLp_lineDerivOp_sq :
    ‖(SchwartzMap.gaussian (V := ℝ) (b := (π : ℂ)) Real.pi_pos).toLp 2‖ ^ 2 +
        ‖(∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) (b := (π : ℂ))
          Real.pi_pos : 𝓢(ℝ, ℂ))).toLp 2‖ ^ 2 =
      (1 + π) / √2 := by
  rw [norm_toLp_gaussian_sq_add_norm_toLp_lineDerivOp_one_gaussian_sq, Complex.ofReal_re,
    div_mul_cancel_right₀ Real.pi_ne_zero, Real.sqrt_inv, Complex.norm_of_nonneg Real.pi_pos.le]
  field_simp

end TauCeti.Examples.BesselPotential
