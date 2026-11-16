/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# Derivatives of the Fourier phases

On a real inner-product space, the phases `ζ ↦ 𝐞 ⟪ζ, x⟫` and `y ↦ 𝐞 (-⟪y, ζ⟫)` of the inverse and
direct Fourier integrals have directional derivatives `2πi ⟪v, x⟫ 𝐞 ⟪ζ, x⟫` and
`-2πi ⟪v, ζ⟫ 𝐞 (-⟪y, ζ⟫)` in the direction `v`. These are Mathlib's derivatives
`Real.hasFDerivAt_fourierChar_neg_bilinear_right` and
`Real.hasFDerivAt_fourierChar_neg_bilinear_left` of the Fourier character composed with a
bilinear map, specialized to the inner product and evaluated in a direction, which is the form
used to integrate by parts against the phase.

The plane wave `x ↦ 𝐞 ⟪η, x⟫ = exp(2πi ⟪η, x⟫)` of frequency `η` is smooth, with derivatives of
order `k` bounded by `(2π ‖η‖) ^ k` at every point; in particular it has temperate growth, so it
multiplies Schwartz functions and tempered distributions.

## Main results

* `Real.hasLineDerivAt_fourierChar_inner`: the directional derivative of `ζ ↦ 𝐞 ⟪ζ, x⟫`.
* `Real.hasLineDerivAt_fourierChar_neg_inner`: the directional derivative of
  `y ↦ 𝐞 (-⟪y, ζ⟫)`.
* `Real.norm_iteratedFDeriv_fourierChar_inner_le`: `‖D^k 𝐞 ⟪η, ·⟫‖ ≤ (2π ‖η‖) ^ k`.
* `Real.hasTemperateGrowth_fourierChar_inner`: the plane waves have temperate growth.
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

/-- The plane wave `x ↦ 𝐞 ⟪η, x⟫` is the Fourier atom `TauCeti.fourierAtom (-η)`. -/
private theorem fourierChar_inner_eq_fourierAtom (η : E) :
    (fun x : E ↦ (𝐞 ⟪η, x⟫ : ℂ)) = TauCeti.fourierAtom (-η) := by
  funext x
  rw [TauCeti.fourierAtom_eq_fourierChar, inner_neg_right, neg_neg, real_inner_comm]

/-- The plane wave `x ↦ 𝐞 ⟪η, x⟫` is smooth. -/
theorem contDiff_fourierChar_inner (η : E) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun x : E ↦ (𝐞 ⟪η, x⟫ : ℂ) := by
  rw [fourierChar_inner_eq_fourierAtom]
  exact TauCeti.contDiff_fourierAtom (-η)

/-- The plane waves `𝐞 ⟪η, x⟫` depend continuously on the frequency and the position jointly. -/
theorem continuous_fourierChar_inner :
    Continuous fun p : E × E ↦ (𝐞 ⟪p.1, p.2⟫ : ℂ) :=
  continuous_subtype_val.comp (continuous_fourierChar.comp continuous_inner)

/-- **Derivatives of a plane wave.** The derivative of order `k` of the plane wave
`x ↦ 𝐞 ⟪η, x⟫ = exp(2πi ⟪η, x⟫)` is bounded by `(2π ‖η‖) ^ k` at every point. -/
theorem norm_iteratedFDeriv_fourierChar_inner_le (η : E) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun x : E ↦ (𝐞 ⟪η, x⟫ : ℂ)) x‖ ≤ (2 * π * ‖η‖) ^ k := by
  rw [fourierChar_inner_eq_fourierAtom, ← norm_neg η]
  exact TauCeti.norm_iteratedFDeriv_fourierAtom_le (-η) x k

/-- The plane wave `x ↦ 𝐞 ⟪η, x⟫` has temperate growth. -/
theorem hasTemperateGrowth_fourierChar_inner (η : E) :
    (fun x : E ↦ (𝐞 ⟪η, x⟫ : ℂ)).HasTemperateGrowth :=
  .of_norm_iteratedFDeriv_le (contDiff_fourierChar_inner η) fun k ↦
    ⟨_, norm_iteratedFDeriv_fourierChar_inner_le η k⟩

end Real
