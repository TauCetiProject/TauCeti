/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.PositiveDefinite.FourierAtom
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Test functions cut off by a Fourier atom

Multiplying a complex test function `φ` by the Fourier atom `e_η x = 𝐞 (-⟪x, η⟫)`
(`TauCeti.fourierAtom`) gives the test function `φ e_η`, written
`bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ`. Pairing a
distribution with it is the localized Fourier transform `Distribution.localFourier`. This file
records the product rule for its directional derivatives,

`∂_v (φ e_η) = (∂_v φ) e_η - 2πi ⟪v, η⟫ φ e_η`.

## Main declarations

* `TestFunction.lineDerivOp_bilinLeftCLM_fourierAtom`: the directional derivative of `φ e_η`.
-/

public section

noncomputable section

open Complex LineDeriv Real TopologicalSpace
open scoped Distributions FourierTransform RealInnerProductSpace

namespace TestFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-- **The product rule for a test function cut off by a Fourier atom.** For
`e_η x = 𝐞 (-⟪x, η⟫)`, `∂_v (φ e_η) = (∂_v φ) e_η - 2πi ⟪v, η⟫ φ e_η`. -/
theorem lineDerivOp_bilinLeftCLM_fourierAtom (φ : 𝓓(Ω, ℂ)) (v η : E) :
    ∂_{v} (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ) =
      bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) (∂_{v} φ) -
        (2 * π * I * ⟪v, η⟫ : ℂ) •
          bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ := by
  ext x
  have hφ : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  -- `innerSL ℝ`, used as a real bilinear map, still evaluates to the inner product.
  have hL (a b : E) : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) a b = ⟪a, b⟫ := rfl
  have he := hasFDerivAt_fourierChar_neg_bilinear_left (innerSL ℝ) x η
  simp only [hL] at he
  have hfun : (fun y ↦ φ y * TauCeti.fourierAtom η y) = fun y ↦ φ y * (𝐞 (-⟪y, η⟫) : ℂ) := by
    simp [TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply]
  simp only [lineDerivOp_apply, bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
    sub_apply, smul_apply, smul_eq_mul]
  rw [hfun]
  -- `hφ.mul he` is stated for the pointwise product `⇑φ * _`, which unfolds to `φ e_η`; the
  -- coercion of `𝐞` to `ℂ` in `he` agrees with the one in `TauCeti.fourierAtom` up to unfolding.
  refine ((hφ.mul he).hasLineDerivAt v).lineDeriv.trans ?_
  rw [(hφ.hasLineDerivAt v).lineDeriv]
  simp [TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply, hL, real_inner_comm v η]
  ring

end TestFunction
