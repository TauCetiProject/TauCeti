/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Basic

/-!
# Covariance of the upper half-plane Poisson integral

The Poisson kernel `P(z, x) = Im z / (π |x - z| ^ 2)` of the upper half-plane is covariant under
the affine maps of the real line. Translating the boundary point by `u ∈ ℝ` is translating the pole
by `-u`, and rescaling the boundary point by `c⁻¹` is rescaling the pole by `c`, up to the factor
`c`:

`P(z, x + u) = P(z - u, x)`,   `P(z, x / c) = c P(c z, x)`   (`c ≠ 0`).

For the Poisson integral `P[ν](z) = ∫ P(z, x) dν(x)` this says that the translate `ν_u` of `ν` by
`u` and the image `ν^c` of `ν` under `x ↦ x / c` satisfy

`P[ν_u](z) = P[ν](z - u)`,   `P[ν^c](z) = c P[ν](c z)`.

## Main results

* `TauCeti.upperHalfPlanePoissonKernel_add`, `TauCeti.upperHalfPlanePoissonKernel_div`: covariance
  of the Poisson kernel.
* `TauCeti.upperHalfPlanePoissonIntegral_map_add`, `TauCeti.upperHalfPlanePoissonIntegral_map_div`:
  translation and dilation covariance of the Poisson integral.
-/

public section

noncomputable section

namespace TauCeti

open Complex MeasureTheory

/-- Translating the boundary point of the Poisson kernel by `u` is translating the pole by `-u`. -/
theorem upperHalfPlanePoissonKernel_add (z : ℂ) (u x : ℝ) :
    upperHalfPlanePoissonKernel z (x + u) = upperHalfPlanePoissonKernel (z - u) x := by
  rw [upperHalfPlanePoissonKernel_eq, upperHalfPlanePoissonKernel_eq, sub_im, ofReal_im, sub_zero]
  push_cast
  ring_nf

/-- Rescaling the boundary point of the Poisson kernel by `c⁻¹` is rescaling the pole by `c`, up
to the factor `c`: `P(z, x / c) = c P(c z, x)` for `c ≠ 0`. -/
theorem upperHalfPlanePoissonKernel_div (z : ℂ) {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    upperHalfPlanePoissonKernel z (x / c) = c * upperHalfPlanePoissonKernel (c * z) x := by
  rw [upperHalfPlanePoissonKernel_eq, upperHalfPlanePoissonKernel_eq]
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
  have h : ((x / c : ℝ) : ℂ) - z = (c : ℂ)⁻¹ * ((x : ℂ) - c * z) := by
    push_cast
    field_simp
  rw [h, normSq_mul, normSq_inv, normSq_ofReal]
  simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  field_simp

/-- **Translation covariance of the Poisson integral.** For the translate of `ν` by `u ∈ ℝ`,
`P[ν_u](z) = P[ν](z - u)`. -/
theorem upperHalfPlanePoissonIntegral_map_add (ν : Measure ℝ) (u : ℝ) (z : ℂ) :
    upperHalfPlanePoissonIntegral (ν.map (· + u)) z = upperHalfPlanePoissonIntegral ν (z - u) := by
  rw [upperHalfPlanePoissonIntegral_def, upperHalfPlanePoissonIntegral_def,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [upperHalfPlanePoissonKernel_add]

/-- **Dilation covariance of the Poisson integral.** For `c ≠ 0` and the image `ν^c` of `ν` under
`x ↦ x / c`, `P[ν^c](z) = c P[ν](c z)`. -/
theorem upperHalfPlanePoissonIntegral_map_div (ν : Measure ℝ) {c : ℝ} (hc : c ≠ 0) (z : ℂ) :
    upperHalfPlanePoissonIntegral (ν.map (· / c)) z =
      c * upperHalfPlanePoissonIntegral ν (c * z) := by
  rw [upperHalfPlanePoissonIntegral_def, upperHalfPlanePoissonIntegral_def,
    integral_map (by fun_prop) (by fun_prop), ← integral_const_mul]
  simp_rw [upperHalfPlanePoissonKernel_div z hc]

end TauCeti
