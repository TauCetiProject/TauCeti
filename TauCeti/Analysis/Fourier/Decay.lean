/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Decay of Fourier transforms of smooth compactly supported functions

A smooth compactly supported function is a Schwartz function, so its Fourier transform is again a
Schwartz function and therefore decays faster than every negative power of `‖v‖`. This file records
that decay in the elementary form `‖v‖ ^ k * ‖𝓕 f v‖ ≤ C`, which is the shape a Fourier transform
is used in when it weights a comparison test.

## Main declarations

* `TauCeti.exists_norm_pow_mul_norm_fourier_le`: for every exponent `k`, the Fourier transform of a
  smooth compactly supported function on a finite-dimensional real inner product space satisfies
  `‖v‖ ^ k * ‖𝓕 f v‖ ≤ C` for some `C > 0`.
-/

public section

open scoped ContDiff FourierTransform

namespace TauCeti

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

/-- The Fourier transform of a smooth compactly supported function decays faster than every power
of `‖v‖⁻¹`, because it is a Schwartz function. -/
theorem exists_norm_pow_mul_norm_fourier_le (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f)
    (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ v : V, ‖v‖ ^ k * ‖𝓕 f v‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := (𝓕 (hsupp.toSchwartzMap hf) : SchwartzMap V E).decay k 0
  refine ⟨C, hC0, fun v ↦ ?_⟩
  have hcoe0 : ⇑(hsupp.toSchwartzMap hf) = f := by
    ext u
    simp
  have hcoe : ((𝓕 (hsupp.toSchwartzMap hf) : SchwartzMap V E) : V → E) = 𝓕 f := by
    rw [SchwartzMap.fourier_coe, hcoe0]
  have h := hC v
  rwa [norm_iteratedFDeriv_zero, hcoe] at h

end TauCeti
