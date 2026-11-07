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
# Line derivatives of the Fourier character

On a real inner-product space, the character `ζ ↦ exp(2πi ⟪ζ, z⟫)` has line derivative
`2πi ⟪v, z⟫ exp(2πi ⟪ζ, z⟫)` in the direction `v`. This is Mathlib's
`Real.hasDerivAt_fourierChar` composed with the linear functional `⟪·, z⟫`, stated in the form
used by Mathlib's line-derivative integration by parts.

## Main results

* `TauCeti.hasLineDerivAt_fourierChar_inner`: the line derivative of `ζ ↦ 𝐞 ⟪ζ, z⟫`.
-/

public section

open Real
open scoped FourierTransform RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The character `ζ ↦ exp(2πi ⟪ζ, z⟫)` has line derivative `2πi ⟪v, z⟫ exp(2πi ⟪ζ, z⟫)` in the
direction `v`. -/
theorem hasLineDerivAt_fourierChar_inner (z ζ v : E) :
    HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, z⟫ : ℂ)) (2 * π * Complex.I * ⟪v, z⟫ * 𝐞 ⟪ζ, z⟫) ζ v := by
  have h := ((hasDerivAt_fourierChar ⟪ζ, z⟫).hasFDerivAt.comp ζ
    ((innerSL ℝ z).hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun ζ' ↦ real_inner_comm z ζ'))).hasLineDerivAt v
  convert h using 1
  · funext ζ'
    simp
  · simp [real_inner_comm z v]
    ring

end TauCeti
