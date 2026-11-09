/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.Inversion

/-!
# Uniqueness of the Fourier transform of a continuous integrable function

On a finite-dimensional real inner product space, a continuous integrable function whose Fourier
transform vanishes is zero. The vanishing transform is trivially integrable, so Mathlib's Fourier
inversion formula `Continuous.fourierInv_fourier_eq` applies and recovers the function as the
inverse transform of zero.

## Main results

* `Continuous.eq_zero_of_fourier_eq_zero`: a continuous integrable function with vanishing Fourier
  transform is zero.
-/

public section

open MeasureTheory
open scoped FourierTransform

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : V → E}

/-- A continuous integrable function whose Fourier transform vanishes is zero. -/
theorem Continuous.eq_zero_of_fourier_eq_zero (h : Continuous f) (hf : Integrable f)
    (hF : 𝓕 f = 0) : f = 0 := by
  have hinv := h.fourierInv_fourier_eq hf (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  ext v
  simp [Real.fourierInv_eq]
