/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Topology.Algebra.Module.Star
public import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Conjugate-linear maps applied to the values of Schwartz functions

A continuous conjugate-linear map `L : F →L⋆[ℂ] G`, for instance complex conjugation on `ℂ` or
componentwise conjugation on `ℂʳ`, acts on Schwartz functions by `f ↦ L ∘ f`
(`SchwartzMap.conjPostcompCLM`). For `L = conj` on `ℂ` this is the complex conjugation
`SchwartzMap.conjCLM` of scalar Schwartz functions (`SchwartzMap.conjCLM_eq_conjPostcompCLM`).

Since `L` is conjugate-linear, it turns the character `e^{-2πi⟪x, ξ⟫}` of the Fourier transform into
its conjugate `e^{2πi⟪x, ξ⟫}`, so it exchanges the Fourier transform and its inverse:
`𝓕 (L ∘ f) = L ∘ 𝓕⁻ f` and `𝓕⁻ (L ∘ f) = L ∘ 𝓕 f`. Consequently it conjugates and reflects the
symbol of a Fourier multiplier,

`T_g (L ∘ f) = L ∘ T_{g'} f`, `g'(ξ) = conj (g (-ξ))`

(`SchwartzMap.fourierMultiplierCLM_conjPostcompCLM`). A real even symbol, such as the Bessel
potential `⟨ξ⟩ ^ s`, is unchanged, so its multiplier commutes with `L`.

These identities are the Schwartz-space input for conjugation on tempered distributions and on the
Bessel-potential spaces `H^{s,p}`.

## Main declarations

* `SchwartzMap.conjPostcompCLM`: postcomposition with a continuous conjugate-linear map.
* `SchwartzMap.conjCLM_eq_conjPostcompCLM`: complex conjugation `SchwartzMap.conjCLM` of scalar
  Schwartz functions is postcomposition with conjugation on `ℂ`.
* `SchwartzMap.fourier_conjPostcompCLM_apply`, `SchwartzMap.fourierInv_conjPostcompCLM_apply`:
  `𝓕 (L ∘ f) = L ∘ 𝓕⁻ f` and `𝓕⁻ (L ∘ f) = L ∘ 𝓕 f`.
* `SchwartzMap.conjCLM_fourier`, `SchwartzMap.conjCLM_fourierInv`: `conj (𝓕 φ) = 𝓕⁻ (conj φ)` and
  `conj (𝓕⁻ φ) = 𝓕 (conj φ)`.
* `SchwartzMap.fourierMultiplierCLM_conjPostcompCLM`: the multiplier with symbol `g` applied to
  `L ∘ f` is `L` applied to the multiplier with symbol `conj (g (-ξ))`;
  `SchwartzMap.fourierMultiplierCLM_conjCLM` is the case of complex conjugation.
-/

public section

noncomputable section

open scoped FourierTransform SchwartzMap ComplexConjugate
open FourierTransform MeasureTheory

namespace SchwartzMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

section NormedSpace

variable [NormedSpace ℝ E]

/-- Postcomposition with a continuous conjugate-linear map `L : F →L⋆[ℂ] G`, as a continuous
conjugate-linear map `𝓢(E, F) → 𝓢(E, G)`, `f ↦ L ∘ f`. -/
def conjPostcompCLM (L : F →L⋆[ℂ] G) : 𝓢(E, F) →L⋆[ℂ] 𝓢(E, G) where
  -- As a continuous additive map between real vector spaces, `L` is real-linear, and
  -- postcomposition with a real-linear map is continuous.
  toFun := postcompCLM ((L : F →+ G).toRealLinearMap L.continuous)
  map_add' := map_add _
  map_smul' c f := by
    ext x
    simp
  cont := (postcompCLM ((L : F →+ G).toRealLinearMap L.continuous)).continuous

@[simp]
theorem conjPostcompCLM_apply (L : F →L⋆[ℂ] G) (f : 𝓢(E, F)) (x : E) :
    conjPostcompCLM L f x = L (f x) :=
  (rfl)

/-- Complex conjugation `SchwartzMap.conjCLM` is postcomposition with conjugation on `ℂ`. -/
theorem conjCLM_eq_conjPostcompCLM (φ : 𝓢(E, ℂ)) :
    conjCLM φ = conjPostcompCLM (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap φ := by
  ext x
  simp

/-- Postcomposition with two conjugate-linear maps is postcomposition with their complex-linear
composite. -/
@[simp]
theorem conjPostcompCLM_conjPostcompCLM {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L' : G →L⋆[ℂ] H) (L : F →L⋆[ℂ] G) (f : 𝓢(E, F)) :
    conjPostcompCLM L' (conjPostcompCLM L f) = postcompCLM (L'.comp L) f := by
  ext x
  simp

end NormedSpace

section Fourier

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F] [CompleteSpace G]

/-- A conjugate-linear map commutes with Bochner integrals of Schwartz functions twisted by a
character. -/
private theorem integral_circle_smul_conj (L : F →L⋆[ℂ] G) (f : 𝓢(E, F)) (c : E → Circle)
    (hc : Continuous c) :
    ∫ v, c v • L (f v) = L (∫ v, (c v)⁻¹ • f v) := by
  rw [← L.integral_comp_commSL (fun r z ↦ by simp)]
  · congr 1 with v
    rw [Circle.smul_def, Circle.smul_def, map_smulₛₗ, Circle.coe_inv_eq_conj, Complex.conj_conj]
  · refine f.integrable.norm.mono' ?_ (.of_forall fun v ↦ ?_)
    · exact ((continuous_inv.comp hc).smul f.continuous).aestronglyMeasurable
    · simp [Circle.norm_smul]

/-- A conjugate-linear map exchanges the Fourier transform and its inverse:
`𝓕 (L ∘ f) = L ∘ 𝓕⁻ f`. -/
@[simp]
theorem fourier_conjPostcompCLM_apply (L : F →L⋆[ℂ] G) (f : 𝓢(E, F)) (x : E) :
    𝓕 (conjPostcompCLM L f) x = L (𝓕⁻ f x) := by
  rw [fourier_coe, fourierInv_coe, Real.fourier_eq, Real.fourierInv_eq]
  simp only [conjPostcompCLM_apply]
  rw [integral_circle_smul_conj L f _ (by fun_prop)]
  congr 2 with v
  rw [← AddChar.map_neg_eq_inv, neg_neg]

/-- A conjugate-linear map exchanges the inverse Fourier transform and the Fourier transform:
`𝓕⁻ (L ∘ f) = L ∘ 𝓕 f`. -/
@[simp]
theorem fourierInv_conjPostcompCLM_apply (L : F →L⋆[ℂ] G) (f : 𝓢(E, F)) (x : E) :
    𝓕⁻ (conjPostcompCLM L f) x = L (𝓕 f x) := by
  -- `L ∘ f = L ∘ 𝓕⁻ (𝓕 f) = 𝓕 (L ∘ 𝓕 f)`.
  have h : conjPostcompCLM L f = 𝓕 (conjPostcompCLM L (𝓕 f)) := by
    ext y
    rw [fourier_conjPostcompCLM_apply, fourierInv_fourier_eq, conjPostcompCLM_apply]
  rw [h, fourierInv_fourier_eq, conjPostcompCLM_apply]

/-- **Conjugation of Fourier multipliers.** A conjugate-linear map `L` conjugates and reflects the
symbol of a Fourier multiplier: `T_g (L ∘ f) = L ∘ T_{g'} f` with `g'(ξ) = conj (g (-ξ))`. -/
theorem fourierMultiplierCLM_conjPostcompCLM (L : F →L⋆[ℂ] G) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM G g (conjPostcompCLM L f) =
      conjPostcompCLM L (fourierMultiplierCLM F (fun ξ ↦ conj (g (-ξ))) f) := by
  have hg' : (fun ξ ↦ conj (g ξ)).HasTemperateGrowth :=
    (Complex.conjCLE.toContinuousLinearMap.hasTemperateGrowth).comp hg
  -- `𝓕 (L ∘ f) = L ∘ 𝓕⁻ f`, and multiplying by `g` commutes with `L` up to conjugating `g`.
  have hmul : smulLeftCLM G g (𝓕 (conjPostcompCLM L f)) =
      conjPostcompCLM L (smulLeftCLM F (fun ξ ↦ conj (g ξ)) (𝓕⁻ f)) := by
    ext ξ
    rw [smulLeftCLM_apply_apply hg, conjPostcompCLM_apply, smulLeftCLM_apply_apply hg',
      fourier_conjPostcompCLM_apply, map_smulₛₗ, Complex.conj_conj]
  ext x
  rw [fourierMultiplierCLM_apply, hmul, fourierInv_conjPostcompCLM_apply,
    fourier_smulLeftCLM_fourierInv_eq hg', conjPostcompCLM_apply]

/-- Complex conjugation exchanges the Fourier transform and its inverse:
`𝓕 (conj φ) = conj (𝓕⁻ φ)`. -/
@[simp]
theorem fourier_conjCLM_apply (φ : 𝓢(E, ℂ)) (x : E) : 𝓕 (conjCLM φ) x = conj (𝓕⁻ φ x) :=
  conjCLM_eq_conjPostcompCLM φ ▸ fourier_conjPostcompCLM_apply _ φ x

/-- Complex conjugation exchanges the inverse Fourier transform and the Fourier transform:
`𝓕⁻ (conj φ) = conj (𝓕 φ)`. -/
@[simp]
theorem fourierInv_conjCLM_apply (φ : 𝓢(E, ℂ)) (x : E) : 𝓕⁻ (conjCLM φ) x = conj (𝓕 φ x) :=
  conjCLM_eq_conjPostcompCLM φ ▸ fourierInv_conjPostcompCLM_apply _ φ x

/-- The conjugate of a Fourier transform is the inverse Fourier transform of the conjugate:
`conj (𝓕 φ) = 𝓕⁻ (conj φ)`. -/
theorem conjCLM_fourier (φ : 𝓢(E, ℂ)) : conjCLM (𝓕 φ) = 𝓕⁻ (conjCLM φ) := by
  ext x
  simp

/-- The conjugate of an inverse Fourier transform is the Fourier transform of the conjugate:
`conj (𝓕⁻ φ) = 𝓕 (conj φ)`. -/
theorem conjCLM_fourierInv (φ : 𝓢(E, ℂ)) : conjCLM (𝓕⁻ φ) = 𝓕 (conjCLM φ) := by
  ext x
  simp

/-- Complex conjugation of scalar Schwartz functions conjugates and reflects the symbol of a
Fourier multiplier: `T_g (conj φ) = conj (T_{g'} φ)` with `g'(ξ) = conj (g (-ξ))`. -/
theorem fourierMultiplierCLM_conjCLM {g : E → ℂ} (hg : g.HasTemperateGrowth) (φ : 𝓢(E, ℂ)) :
    fourierMultiplierCLM ℂ g (conjCLM φ) =
      conjCLM (fourierMultiplierCLM ℂ (fun ξ ↦ conj (g (-ξ))) φ) :=
  by simpa only [conjCLM_eq_conjPostcompCLM] using fourierMultiplierCLM_conjPostcompCLM _ hg φ

end Fourier

end SchwartzMap
