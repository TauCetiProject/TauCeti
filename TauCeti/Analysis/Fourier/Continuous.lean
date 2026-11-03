/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Continuity of the Fourier transform of an integrable function

On a finite-dimensional real inner-product space, the Fourier transform `𝓕 f` of an integrable
`f` with values in a complex normed space is continuous, and so is the inverse transform `𝓕⁻ f`.
These are Mathlib's `VectorFourier.fourierIntegral_continuous` specialized to the inner-product
pairing and its negation, packaged so that consumers do not repeat the pairing-continuity bridge
at every call site.

## Main declarations

* `MeasureTheory.Integrable.continuous_fourier`: `𝓕 f` is continuous for integrable `f`.
* `MeasureTheory.Integrable.continuous_fourierInv`: `𝓕⁻ f` is continuous for integrable `f`.
-/

public section

open scoped FourierTransform

namespace MeasureTheory.Integrable

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

/-- The Fourier transform of an integrable function is continuous. This is Mathlib's
`VectorFourier.fourierIntegral_continuous` specialized to the inner-product pairing. -/
theorem continuous_fourier (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

/-- The inverse Fourier transform of an integrable function is continuous. This is Mathlib's
`VectorFourier.fourierIntegral_continuous` specialized to the negated inner-product pairing. -/
theorem continuous_fourierInv (hf : Integrable f) : Continuous (𝓕⁻ f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (-innerSL ℝ).continuous₂ hf

end MeasureTheory.Integrable
