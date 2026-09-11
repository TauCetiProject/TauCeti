/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The total integral of a Fourier transform

Fourier inversion evaluated at the origin says that the total integral of `𝓕 f` is `f 0`, because
the inverse transform at the origin is nothing but integration. This file records that reading of
Mathlib's `MeasureTheory.Integrable.fourierInv_fourier_eq`, together with the rescaled form
`∫ u, 𝓕 f (u / c) = |c| • f 0` on the line, which is what a Fourier variable normalized by a
factor of `2π` produces.

## Main declarations

* `TauCeti.integral_fourier`: the total integral of `𝓕 f` is `f 0`.
* `TauCeti.integral_fourier_comp_div`: its rescaling `∫ u, 𝓕 f (u / c) = |c| • f 0` on the line.
-/

public section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace TauCeti

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The total integral of a Fourier transform is the value of the original function at the
origin, since the inverse Fourier transform at the origin is integration. -/
theorem integral_fourier {f : V → E} (hf : Continuous f) (hfi : Integrable f)
    (hFi : Integrable (𝓕 f)) :
    (∫ v : V, 𝓕 f v) = f 0 := by
  have hinv : 𝓕⁻ (𝓕 f) 0 = f 0 := hfi.fourierInv_fourier_eq hFi hf.continuousAt
  rw [Real.fourierInv_eq] at hinv
  simpa using hinv

/-- Rescaling the Fourier variable by `c` multiplies the total integral of a Fourier transform on
the line by `|c|`. -/
theorem integral_fourier_comp_div {f : ℝ → E} (hf : Continuous f) (hfi : Integrable f)
    (hFi : Integrable (𝓕 f)) (c : ℝ) :
    (∫ u : ℝ, 𝓕 f (u / c)) = |c| • f 0 := by
  rw [Measure.integral_comp_div, integral_fourier hf hfi hFi]

end TauCeti
