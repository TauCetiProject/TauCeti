/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Bochner.CharFun.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Smoothness of characteristic-function inversion densities

Polynomially weighted integrability of a characteristic function gives differentiability of
its inversion density. This transfers Mathlib's Fourier differentiation theorem to the
characteristic-function convention with kernel `exp (-i t x)`, rather than `exp (-2πi t x)`.
In particular, integrability at every natural weight gives a smooth density for a finite
measure with integrable characteristic function.

The proof uses `VectorFourier.contDiff_fourierIntegral` with the rescaled bilinear pairing,
so no regularity of the characteristic function itself is required.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley (1971), Section XV.3.
-/

public section

noncomputable section

open Complex
open scoped Real

namespace MeasureTheory.Measure

/-- If the characteristic function is integrable with polynomial weights through order `N`,
its inversion density is `C^N`. Taking `N = ∞` gives smoothness. -/
theorem contDiff_charFunDensity {μ : Measure ℝ} {N : ℕ∞}
    (h : ∀ n : ℕ, n ≤ N → Integrable (fun t : ℝ ↦ ‖t‖ ^ n * ‖charFun μ t‖)) :
    ContDiff ℝ N (charFunDensity μ) := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := (2 * π)⁻¹ • ContinuousLinearMap.mul ℝ ℝ
  have hL (t x : ℝ) : L.toLinearMap₁₂ t x = (2 * π)⁻¹ * (t * x) := by
    simp [L]
  have heq : charFunDensity μ = fun x ↦ (2 * π)⁻¹ *
      (VectorFourier.fourierIntegral Real.fourierChar volume L.toLinearMap₁₂
        (charFun μ) x).re := by
    ext x
    rw [charFunDensity_def, VectorFourier.fourierIntegral]
    congr 2
    apply integral_congr_ae
    filter_upwards with t
    simp only [hL, Real.fourierChar_apply, Circle.smul_def, smul_eq_mul]
    congr 2
    push_cast
    field_simp
  rw [heq]
  exact contDiff_const.mul
    (Complex.reCLM.contDiff.comp (VectorFourier.contDiff_fourierIntegral L h))

end MeasureTheory.Measure
