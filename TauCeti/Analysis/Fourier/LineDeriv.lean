/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Directional derivatives of the Fourier phase

On a real inner-product space, the phase `ζ ↦ exp(2πi ⟪ζ, x⟫)` of the Fourier transform has
directional derivative `2πi ⟪v, x⟫ exp(2πi ⟪ζ, x⟫)` in the direction `v`. This is Mathlib's
`Real.hasDerivAt_fourierChar` composed with the affine line `t ↦ ⟪ζ + t v, x⟫`.

## Main declarations

* `Real.hasLineDerivAt_fourierChar_inner`: the line derivative of `ζ ↦ 𝐞 ⟪ζ, x⟫`.
-/

public section

open scoped FourierTransform RealInnerProductSpace

namespace Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The line derivative of the phase `ζ ↦ exp(2πi ⟪ζ, x⟫)` in the direction `v`. -/
theorem hasLineDerivAt_fourierChar_inner (x v ζ : E) :
    HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ))
      ((2 * π * Complex.I * ⟪v, x⟫) * 𝐞 ⟪ζ, x⟫) ζ v := by
  have h : HasDerivAt (fun t : ℝ ↦ ⟪ζ, x⟫ + t * ⟪v, x⟫) ⟪v, x⟫ 0 := by
    simpa using (hasDerivAt_mul_const ⟪v, x⟫).const_add ⟪ζ, x⟫
  have h' := (hasDerivAt_fourierChar (⟪ζ, x⟫ + 0 * ⟪v, x⟫)).scomp 0 h
  simp only [zero_mul, add_zero] at h'
  unfold HasLineDerivAt
  convert h' using 1
  · funext t
    simp [inner_add_left, inner_smul_left]
  · rw [Complex.real_smul]
    ring

end Real
