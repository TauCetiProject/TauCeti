/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.Convolution

/-!
# Fourier multipliers with Schwartz symbols are convolutions

For a Schwartz symbol `σ : 𝓢(E, ℂ)`, the Fourier multiplier `φ ↦ 𝓕⁻ (σ • 𝓕 φ)` on Schwartz
functions (Mathlib's `SchwartzMap.fourierMultiplierCLM`) is convolution with the Schwartz function
`𝓕⁻ σ`:

`𝓕⁻ (σ • 𝓕 φ) x = ∫ 𝓕⁻ σ (x - y) • φ y`.

This is the convolution theorem `SchwartzMap.fourier_convolution` read backwards. It identifies
the kernel of a multiplier whose symbol is smooth and rapidly decreasing, which is the form taken
by the truncated symbols in the Littlewood–Paley proof of the Mihlin–Hörmander multiplier theorem.

## Main declarations

* `SchwartzMap.fourierMultiplierCLM_eq_convolution`: the multiplier with symbol `σ` is
  `SchwartzMap.convolution` with `𝓕⁻ σ`.
* `SchwartzMap.fourierMultiplierCLM_apply_eq_integral`: the same, pointwise, as an integral.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Sections 2.2 and 2.5.
-/

public section

open scoped FourierTransform SchwartzMap
open FourierTransform ContinuousLinearMap MeasureTheory

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- On Schwartz functions, the multiplier with a Schwartz symbol `σ` is convolution with the
Schwartz function `𝓕⁻ σ`. -/
theorem fourierMultiplierCLM_eq_convolution (σ : 𝓢(E, ℂ)) :
    fourierMultiplierCLM F σ = convolution (lsmul ℂ ℂ) (𝓕⁻ σ) := by
  ext1 φ
  rw [← FourierPair.fourierInv_fourier_eq (F := 𝓢(E, F))
      (convolution (lsmul ℂ ℂ) (𝓕⁻ σ) φ),
    fourier_convolution, fourier_fourierInv_eq, fourierMultiplierCLM_apply]
  congr 1
  ext ξ
  simp [smulLeftCLM_apply_apply σ.hasTemperateGrowth]

/-- The multiplier with a Schwartz symbol `σ` on Schwartz functions, as an integral against the
kernel `𝓕⁻ σ`: `T_σ φ x = ∫ 𝓕⁻ σ (x - y) • φ y`. -/
theorem fourierMultiplierCLM_apply_eq_integral (σ : 𝓢(E, ℂ)) (φ : 𝓢(E, F)) (x : E) :
    fourierMultiplierCLM F σ φ x = ∫ y, 𝓕⁻ σ (x - y) • φ y := by
  rw [fourierMultiplierCLM_eq_convolution, convolution_apply, MeasureTheory.convolution_eq_swap]
  simp only [lsmul_apply]

end SchwartzMap
