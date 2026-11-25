/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Analysis.Distribution.TestFunction.Schwartz
public import TauCeti.Analysis.PositiveDefinite.FourierAtom
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import TauCeti.Analysis.Distribution.TestFunction.FourierSeries
import TauCeti.Analysis.Distribution.TestFunction.Frechet
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Fourier.ChangeOfVariables

/-!
# Test functions cut off by a Fourier atom

Multiplying a complex test function `φ` by the Fourier atom `e_η x = 𝐞 (-⟪x, η⟫)`
(`TauCeti.fourierAtom`) gives the test function `φ e_η`, written
`bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ`. Pairing a
distribution with it is the localized Fourier transform `Distribution.localFourier`. This file
records the product rule for its directional derivatives,

`∂_v (φ e_η) = (∂_v φ) e_η - 2πi ⟪v, η⟫ φ e_η`,

and, viewing `φ e_η` as a Schwartz function, that modulation is translation in frequency:
the Fourier transform of `φ e_η` is `𝓕 φ (· + η)`.

## Main declarations

* `TestFunction.lineDerivOp_bilinLeftCLM_fourierAtom`: the directional derivative of `φ e_η`.
* `TestFunction.exists_forall_norm_iteratedFDeriv_bilinLeftCLM_fourierAtom_le`: the derivatives of
  `φ e_η` grow at most polynomially in `η`.
* `TestFunction.fourierAtomMulSchwartzMap`: `φ e_η` as a Schwartz function.
* `TestFunction.fourier_fourierAtomMulSchwartzMap`, `TestFunction.fourier_bilinLeftCLM_fourierAtom`:
  the Fourier transform of `φ e_η` is `𝓕 φ (· + η)`.
-/

public section

noncomputable section

open Complex LineDeriv Real TopologicalSpace
open scoped Distributions FourierTransform RealInnerProductSpace SchwartzMap

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

/-- The derivatives of order at most `r` of the modulated cutoffs `g e_ζ` grow at most polynomially
in the frequency `ζ`, with a constant independent of `ζ`. -/
theorem exists_forall_norm_iteratedFDeriv_bilinLeftCLM_fourierAtom_le (g : 𝓓(Ω, ℂ))
    (r : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ ζ : E, ∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i
      (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom ζ) g) y‖ ≤
        A * (1 + 2 * Real.pi * ‖ζ‖) ^ r := by
  let K : Compacts E := ⟨tsupport g, g.hasCompactSupport⟩
  let gK : 𝓓_{K}(E, ℂ) :=
    ContDiffMapSupportedIn.of_support_subset g.contDiff (subset_tsupport _)
  refine ⟨ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K r gK, apply_nonneg _ _,
    fun ζ i hi y ↦ ?_⟩
  -- `g e_ζ` is the modulation of `g` by `-ζ`.
  have hcoe : ⇑(bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom ζ) g) =
      gK.modulate (-ζ) := by
    ext x
    simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
      ContDiffMapSupportedIn.modulate_apply, gK, ContDiffMapSupportedIn.coe_of_support_subset,
      TauCeti.fourierAtom_apply, inner_neg_right, smul_eq_mul]
    -- Both sides are `g x` times the exponential of the same phase, up to sign placement.
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hsup : ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K i gK ≤
      ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K r gK :=
    Seminorm.le_def.1 (ContDiffMapSupportedIn.supSeminorm_mono hi) gK
  rw [hcoe]
  calc ‖iteratedFDeriv ℝ i (gK.modulate (-ζ)) y‖ ≤ N[ℂ]_{K, i} (gK.modulate (-ζ)) :=
        ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ
    _ ≤ ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K i gK * (1 + 2 * Real.pi * ‖-ζ‖) ^ i :=
        ContDiffMapSupportedIn.seminorm_modulate_le gK (-ζ) i
    _ ≤ ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K r gK * (1 + 2 * Real.pi * ‖ζ‖) ^ r := by
        rw [norm_neg]
        gcongr
        · exact le_add_of_nonneg_right (by positivity)

/-- The modulated cutoff `x ↦ φ x e_η x`, the product of `φ` with the Fourier atom
`e_η x = 𝐞 (-⟪x, η⟫)` (`TauCeti.fourierAtom η`), as a Schwartz function. Pairing a distribution
with it is the localized Fourier transform `Distribution.localFourier`. -/
def fourierAtomMulSchwartzMap (φ : 𝓓(Ω, ℂ)) (η : E) : 𝓢(E, ℂ) :=
  toSchwartzMapCLM ℂ (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ)

@[simp]
theorem fourierAtomMulSchwartzMap_apply (φ : 𝓓(Ω, ℂ)) (η x : E) :
    φ.fourierAtomMulSchwartzMap η x = φ x * TauCeti.fourierAtom η x := by
  simp [fourierAtomMulSchwartzMap, bilinLeftCLM_apply]

/-- **Modulation is translation in frequency.** The Fourier transform of `φ e_η` is
`ξ ↦ 𝓕 φ (ξ + η)`. -/
theorem fourier_fourierAtomMulSchwartzMap [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (φ : 𝓓(Ω, ℂ)) (η ξ : E) :
    𝓕 (φ.fourierAtomMulSchwartzMap η) ξ = 𝓕 (toSchwartzMapCLM ℂ φ) (ξ + η) := by
  have hmod : ⇑(φ.fourierAtomMulSchwartzMap η) = fun y ↦ 𝐞 ⟪y, -η⟫ • toSchwartzMapCLM ℂ φ y := by
    ext y
    rw [fourierAtomMulSchwartzMap_apply, toSchwartzMapCLM_apply, TauCeti.fourierAtom_eq_fourierChar,
      inner_neg_right, Circle.smul_def, smul_eq_mul, mul_comm]
  rw [SchwartzMap.fourier_coe, hmod, TauCeti.fourier_fourierChar_smul, sub_neg_eq_add,
    SchwartzMap.fourier_coe]

/-- **Modulation is translation in frequency**, for the function underlying `φ e_η`: its Fourier
transform is `ξ ↦ 𝓕 φ (ξ + η)`. -/
theorem fourier_bilinLeftCLM_fourierAtom [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (φ : 𝓓(Ω, ℂ)) (η ξ : E) :
    𝓕 (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ : E → ℂ) ξ =
      𝓕 (φ : E → ℂ) (ξ + η) := by
  have h := fourier_fourierAtomMulSchwartzMap φ η ξ
  have hcoe : ⇑(φ.fourierAtomMulSchwartzMap η) = ⇑(bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
      (TauCeti.contDiff_fourierAtom η) φ) := funext fun x ↦ by simp [bilinLeftCLM_apply]
  rwa [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, hcoe,
    show ⇑(toSchwartzMapCLM ℂ φ) = ⇑φ from funext (toSchwartzMapCLM_apply φ)] at h

end TestFunction
