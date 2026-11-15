/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Fourier transform identities on tempered distributions

Companion identities to Mathlib's `TemperedDistribution.fourier_delta_zero`:
* `TemperedDistribution.fourierInv_delta_zero`: `𝓕⁻ δ₀ = volume.toTemperedDistribution`.
* `TemperedDistribution.fourier_toTemperedDistribution_volume`:
  `𝓕 volume.toTemperedDistribution = δ₀`.
-/

public section

noncomputable section

open FourierTransform MeasureTheory
open scoped SchwartzMap

namespace TemperedDistribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The inverse Fourier transform of `δ₀` is Lebesgue measure (the constant distribution `1`). -/
theorem fourierInv_delta_zero :
    𝓕⁻ (delta (0 : E)) = (volume : Measure E).toTemperedDistribution := by
  ext f; simp [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]

/-- The Fourier transform of Lebesgue measure (the constant distribution `1`) is `δ₀`. -/
@[simp] theorem fourier_toTemperedDistribution_volume :
    𝓕 (volume : Measure E).toTemperedDistribution = delta 0 := by
  rw [← fourierInv_delta_zero, FourierTransform.fourier_fourierInv_eq]

end TemperedDistribution
