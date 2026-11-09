/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Line derivatives of the Fourier character of an inner product

On a real inner product space, the phase `ζ ↦ 𝐞 ⟪ζ, x⟫ = exp(2πi ⟪ζ, x⟫)` has line derivative
`2πi ⟪v, x⟫ 𝐞 ⟪ζ, x⟫` in the direction `v`. This is Mathlib's
`Real.hasFDerivAt_fourierChar_neg_bilinear_right` for the bilinear form `-⟪·, ·⟫`, rewritten in
the form used for integration by parts in the frequency variable of a Fourier integral.

## Main declarations

* `TauCeti.hasLineDerivAt_fourierChar_inner`: the line derivative of `ζ ↦ 𝐞 ⟪ζ, x⟫`.
-/

public section

open scoped FourierTransform RealInnerProductSpace
open Real

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The line derivative in the direction `v` of the phase `ζ ↦ 𝐞 ⟪ζ, x⟫` is
`2πi ⟪v, x⟫ 𝐞 ⟪ζ, x⟫`. This is Mathlib's derivative of `ζ ↦ 𝐞 (-L x ζ)` with `L = -innerSL ℝ`. -/
theorem hasLineDerivAt_fourierChar_inner (x v ζ : E) :
    HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ)) ((2 * π * Complex.I * ⟪v, x⟫) * 𝐞 ⟪ζ, x⟫) ζ v := by
  convert (hasFDerivAt_fourierChar_neg_bilinear_right (-innerSL ℝ) x ζ).hasLineDerivAt v
    using 1 <;> simp [innerSL_apply_apply ℝ, real_inner_comm x]
  ring

end TauCeti
