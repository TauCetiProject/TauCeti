/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.OneDimensional

/-!
# The `2π` witness for `H^{1,2}(ℝ)`

For the Gaussian `g(x) = exp(-π x²)`, whose Fourier transform is itself, Mathlib's
Bessel-potential norm and the weak-derivative norm differ by the factor `(2π)²` on the derivative
term:

* `‖g‖²_{H^{1,2}} = (1 + 1 / (4π)) / √2`
  (`TauCeti.Examples.BesselPotential.norm_toBesselPotentialSpaceCLM_one_gaussian_pi_sq`);
* `‖g‖²_{L²} + ‖g'‖²_{L²} = (1 + π) / √2`
  (`TauCeti.Examples.BesselPotential.norm_toLp_gaussian_pi_sq_add_norm_toLp_lineDerivOp_sq`).

Both are the case `b = π` of the general Gaussian computations
`TauCeti.norm_toBesselPotentialSpaceCLM_one_gaussian_sq` and
`TauCeti.norm_toLp_gaussian_sq_add_norm_toLp_lineDerivOp_one_gaussian_sq`.
-/

public section

open scoped SchwartzMap BesselPotentialSpace LineDeriv Real

namespace TauCeti.Examples.BesselPotential

/-- The Gaussian `exp(-π x²)` on `ℝ` has `‖g‖²_{H^{1,2}} = (1 + 1 / (4π)) / √2`. -/
theorem norm_toBesselPotentialSpaceCLM_one_gaussian_pi_sq :
    ‖SchwartzMap.toBesselPotentialSpaceCLM (1 : ℝ) 2
        (SchwartzMap.gaussian (V := ℝ) (b := (π : ℂ)) (by simpa using Real.pi_pos))‖ ^ 2 =
      (1 + (4 * π)⁻¹) / √2 := by
  rw [norm_toBesselPotentialSpaceCLM_one_gaussian_sq, Complex.ofReal_re, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, show π / (2 * π) = 2⁻¹ by field_simp, Real.sqrt_inv]
  have := Real.pi_pos
  field_simp

/-- The Gaussian `exp(-π x²)` on `ℝ` has `‖g‖²_{L²} + ‖g'‖²_{L²} = (1 + π) / √2`. -/
theorem norm_toLp_gaussian_pi_sq_add_norm_toLp_lineDerivOp_sq :
    ‖(SchwartzMap.gaussian (V := ℝ) (b := (π : ℂ)) (by simpa using Real.pi_pos)).toLp 2‖ ^ 2 +
        ‖(∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) (b := (π : ℂ))
          (by simpa using Real.pi_pos) : 𝓢(ℝ, ℂ))).toLp 2‖ ^ 2 =
      (1 + π) / √2 := by
  rw [norm_toLp_gaussian_sq_add_norm_toLp_lineDerivOp_one_gaussian_sq, Complex.ofReal_re,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, show π / (2 * π) = 2⁻¹ by field_simp,
    Real.sqrt_inv]
  have := Real.pi_pos
  field_simp

end TauCeti.Examples.BesselPotential
