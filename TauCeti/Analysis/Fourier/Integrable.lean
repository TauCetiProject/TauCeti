/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Integrability of Fourier transforms of smooth compactly supported functions

A smooth compactly supported function is a Schwartz function, so its Fourier transform is also a
Schwartz function and hence integrable with respect to any measure of temperate growth, in
particular Lebesgue measure. This supplies the Fourier-integrability hypotheses needed
in dominated-convergence arguments, such as the Wiener--Ikehara boundary identity.

## Main declarations

* `ContDiff.integrable_fourier_of_hasCompactSupport`: the Fourier transform of a smooth
  compactly supported function on a finite-dimensional real inner product space is integrable.
-/

public section

open MeasureTheory
open scoped ContDiff FourierTransform

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}
  {μ : Measure V} [μ.HasTemperateGrowth]

/-- The Fourier transform of a smooth compactly supported function is integrable with respect to
any measure of temperate growth, in particular Lebesgue measure. -/
theorem ContDiff.integrable_fourier_of_hasCompactSupport (hf : ContDiff ℝ ∞ f)
    (hsupp : HasCompactSupport f) : Integrable (𝓕 f) μ := by
  simpa [SchwartzMap.fourier_coe] using (𝓕 (hsupp.toSchwartzMap hf)).integrable (μ := μ)
