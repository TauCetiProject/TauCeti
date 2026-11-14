/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Directional derivatives of the Fourier phases

On a real inner-product space, the phases `ζ ↦ 𝐞 ⟪ζ, x⟫` and `y ↦ 𝐞 (-⟪y, ζ⟫)` of the inverse and
direct Fourier integrals have directional derivatives `2πi ⟪v, x⟫ 𝐞 ⟪ζ, x⟫` and
`-2πi ⟪v, ζ⟫ 𝐞 (-⟪y, ζ⟫)` in the direction `v`. These are Mathlib's derivatives
`Real.hasFDerivAt_fourierChar_neg_bilinear_right` and
`Real.hasFDerivAt_fourierChar_neg_bilinear_left` of the Fourier character composed with a
bilinear map, specialized to the inner product and evaluated in a direction, which is the form
used to integrate by parts against the phase.

## Main results

* `Real.hasLineDerivAt_fourierChar_inner`: the directional derivative of `ζ ↦ 𝐞 ⟪ζ, x⟫`.
* `Real.hasLineDerivAt_fourierChar_neg_inner`: the directional derivative of
  `y ↦ 𝐞 (-⟪y, ζ⟫)`.
-/

public section

open scoped FourierTransform RealInnerProductSpace

namespace Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The line derivative in the direction `v` of the phase `ζ ↦ 𝐞 ⟪ζ, x⟫` is
`2πi ⟪v, x⟫ 𝐞 ⟪ζ, x⟫`. This is Mathlib's derivative of `ζ ↦ 𝐞 (-L x ζ)` with `L = -innerSL ℝ`. -/
theorem hasLineDerivAt_fourierChar_inner (x v ζ : E) :
    HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ)) ((2 * π * Complex.I * ⟪v, x⟫) * 𝐞 ⟪ζ, x⟫) ζ v := by
  convert (hasFDerivAt_fourierChar_neg_bilinear_right (-innerSL ℝ) x ζ).hasLineDerivAt v
    using 1 <;> simp [innerSL_apply_apply ℝ, real_inner_comm x]
  ring

/-- The line derivative in the direction `v` of the phase `y ↦ 𝐞 (-⟪y, ζ⟫)` is
`-2πi ⟪v, ζ⟫ 𝐞 (-⟪y, ζ⟫)`. This is Mathlib's derivative of `y ↦ 𝐞 (-L y ζ)` with
`L = innerSL ℝ`. -/
theorem hasLineDerivAt_fourierChar_neg_inner (ζ v y : E) :
    HasLineDerivAt ℝ (fun y ↦ (𝐞 (-⟪y, ζ⟫) : ℂ))
      ((-2 * π * Complex.I * ⟪v, ζ⟫) * 𝐞 (-⟪y, ζ⟫)) y v := by
  convert (hasFDerivAt_fourierChar_neg_bilinear_left (innerSL ℝ) y ζ).hasLineDerivAt v
    using 1 <;> simp [innerSL_apply_apply ℝ, real_inner_comm ζ]
  ring

end Real
