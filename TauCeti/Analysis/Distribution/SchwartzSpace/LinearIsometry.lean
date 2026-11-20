/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import TauCeti.Analysis.Distribution.SchwartzSpace.ChangeOfVariables
import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Linear isometries and the reflection of Schwartz functions

Let `E` be a finite-dimensional real inner product space and `A` a linear isometry of `E`. Since
`A` preserves the inner product and Lebesgue measure, composition with `A` commutes with the
Fourier transform and its inverse, `𝓕 (f ∘ A) = 𝓕 f ∘ A`. So it commutes with every Fourier
multiplier whose symbol is invariant under `A`, such as the Bessel potentials `⟨ξ⟩ ^ s`. The
Jacobian of `A⁻¹` has absolute value `1`, so the pushforward of Schwartz densities along `A` is
composition with `A⁻¹`. These are the Schwartz-space inputs for the action of linear isometries on
tempered distributions and on the Bessel-potential spaces `H^{s,p}`.

The case `A = -1` is the **reflection** `R g = g (-·)`. Applying the Fourier transform twice is the
reflection, `𝓕 (𝓕 g) = R g`, so the bilinear Plancherel identity compares the Fourier-side
pairing `B_F(f, g) = ∫ M (𝓕 f ξ) (𝓕 g ξ) dξ` with the spatial pairing
`B₀(f, g) = ∫ M (f x) (g x) dx` of a continuous bilinear map `M`:

`B_F(f, g) = B₀(f, R g)`.

Consequently transposes for the two pairings differ by conjugation with `R`.

## Main declarations

* `SchwartzMap.fourier_compCLMOfContinuousLinearEquiv_linearIsometryEquiv` and
  `SchwartzMap.fourierInv_compCLMOfContinuousLinearEquiv_linearIsometryEquiv`: the Fourier
  transform and its inverse commute with composition with a linear isometry.
* `SchwartzMap.fourierMultiplierCLM_compCLMOfContinuousLinearEquiv_linearIsometryEquiv`: so do
  Fourier multipliers with invariant symbols.
* `SchwartzMap.pushforwardCLM_linearIsometryEquiv`: the pushforward of Schwartz densities along a
  linear isometry `A` is composition with `A⁻¹`.
* `SchwartzMap.fourier_fourier_apply`: `𝓕 (𝓕 g) x = g (-x)`.
* `SchwartzMap.integral_bilin_fourier_fourier_eq`: `B_F(f, g) = B₀(f, R g)`, and
  `SchwartzMap.integral_bilin_fourier_fourier_eq_of_transpose`: if `S` is a transpose of `T` for
  `B₀`, then `R S R` is a transpose of `T` for `B_F`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Proposition 2.2.11 (the Fourier transform
  commutes with orthogonal changes of variables and `𝓕 (𝓕 g) = g (-·)`).
-/

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace LinearIsometryEquiv

/-- A linear isometry, as a bijection, has temperate growth. -/
theorem hasTemperateGrowth_toEquiv (A : E ≃ₗᵢ[ℝ] E) :
    (A.toLinearEquiv.toEquiv : E → E).HasTemperateGrowth :=
  A.toContinuousLinearEquiv.hasTemperateGrowth

/-- The inverse of a linear isometry, as a bijection, has temperate growth. -/
theorem hasTemperateGrowth_toEquiv_symm (A : E ≃ₗᵢ[ℝ] E) :
    (A.toLinearEquiv.toEquiv.symm : E → E).HasTemperateGrowth :=
  A.symm.toContinuousLinearEquiv.hasTemperateGrowth

end LinearIsometryEquiv

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F G K : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G]
  [NormedSpace ℂ G] [NormedAddCommGroup K] [NormedSpace ℂ K]

namespace SchwartzMap

omit [MeasurableSpace E] [BorelSpace E] in
/-- The pushforward of Schwartz densities along a linear isometry `A` is composition with `A⁻¹`:
the Jacobian factor `|det A⁻¹|` is `1`. -/
theorem pushforwardCLM_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) (f : 𝓢(E, F)) :
    pushforwardCLM ℂ A.toLinearEquiv.toEquiv A.hasTemperateGrowth_toEquiv
        A.hasTemperateGrowth_toEquiv_symm f =
      compCLMOfContinuousLinearEquiv ℂ A.symm.toContinuousLinearEquiv f := by
  ext y
  have hdet : |(fderiv ℝ (A.toLinearEquiv.toEquiv.symm : E → E) y).det| = 1 := by
    have hA : (A.toLinearEquiv.toEquiv.symm : E → E) = A.symm := rfl
    rw [hA, A.symm.fderiv, ContinuousLinearMap.det, ← LinearMap.normDet_eq_abs_det]
    exact A.symm.toLinearIsometry.normDet_eq_one
  rw [pushforwardCLM_apply, hdet]
  simp

/-- The Fourier transform commutes with composition with a linear isometry `A`:
`𝓕 (f ∘ A) = 𝓕 f ∘ A`. -/
theorem fourier_compCLMOfContinuousLinearEquiv_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E)
    (f : 𝓢(E, F)) :
    𝓕 (compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f) =
      compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv (𝓕 f) := by
  ext x
  simp [fourier_coe, Real.fourier_comp_linearIsometry]

/-- The inverse Fourier transform commutes with composition with a linear isometry `A`:
`𝓕⁻ (f ∘ A) = 𝓕⁻ f ∘ A`. -/
theorem fourierInv_compCLMOfContinuousLinearEquiv_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E)
    (f : 𝓢(E, F)) :
    𝓕⁻ (compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f) =
      compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv (𝓕⁻ f) := by
  ext x
  simp [fourierInv_coe, Real.fourierInv_comp_linearIsometry]

/-- A Fourier multiplier whose symbol is invariant under a linear isometry `A` commutes with
composition with `A`. -/
theorem fourierMultiplierCLM_compCLMOfContinuousLinearEquiv_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E)
    {g : E → ℂ} (hgA : ∀ x, g (A x) = g x) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g (compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f) =
      compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv (fourierMultiplierCLM F g f) := by
  by_cases hg : g.HasTemperateGrowth
  · have hg' : g ∘ A.toContinuousLinearEquiv.symm = g :=
      funext fun x ↦ by simpa using (hgA (A.symm x)).symm
    rw [fourierMultiplierCLM_apply, fourierMultiplierCLM_apply,
      fourier_compCLMOfContinuousLinearEquiv_linearIsometryEquiv,
      smulLeftCLM_compCLMOfContinuousLinearEquiv ℂ hg, hg',
      fourierInv_compCLMOfContinuousLinearEquiv_linearIsometryEquiv]
  · simp [fourierMultiplierCLM_apply, smulLeftCLM, hg]

variable [CompleteSpace F] [CompleteSpace G]

/-- Applying the Fourier transform twice reflects a Schwartz function: `𝓕 (𝓕 g) x = g (-x)`. -/
theorem fourier_fourier_apply (g : 𝓢(E, G)) (x : E) : 𝓕 (𝓕 g) x = g (-x) := by
  have h := fourierInv_apply_eq (𝓕 g)
  rw [FourierTransform.fourierInv_fourier_eq] at h
  conv_rhs => rw [h]
  simp

/-- **The Fourier-side bilinear pairing is the spatial pairing with a reflection.** For Schwartz
functions and a continuous bilinear map `M`,
`∫ M (𝓕 f ξ) (𝓕 g ξ) dξ = ∫ M (f x) (g (-x)) dx`, by the bilinear Plancherel identity and
`𝓕 (𝓕 g) = g (-·)`. -/
theorem integral_bilin_fourier_fourier_eq (M : F →L[ℂ] G →L[ℂ] K) (f : 𝓢(E, F)) (g : 𝓢(E, G)) :
    ∫ ξ, M (𝓕 f ξ) (𝓕 g ξ) = ∫ x, M (f x) (g (-x)) := by
  rw [integral_bilin_fourier_eq f (𝓕 g) M]
  congr 1 with x
  rw [fourier_fourier_apply]

/-- **Transposes for the Fourier-side pairing.** If `S` is a transpose of `T` for the spatial
pairings, `∫ M (T f x) (g x) dx = ∫ M' (f x) (S g x) dx`, then `R ∘ S ∘ R`, with the reflection
`R g = g (-·)`, is a transpose of `T` for the Fourier-side pairings. -/
theorem integral_bilin_fourier_fourier_eq_of_transpose {F' G' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℂ F'] [CompleteSpace F'] [NormedAddCommGroup G'] [NormedSpace ℂ G']
    [CompleteSpace G'] (M : F' →L[ℂ] G →L[ℂ] K) (M' : F →L[ℂ] G' →L[ℂ] K)
    {T : 𝓢(E, F) → 𝓢(E, F')} {S : 𝓢(E, G) → 𝓢(E, G')}
    (hTS : ∀ f g, ∫ x, M (T f x) (g x) = ∫ x, M' (f x) (S g x)) (f : 𝓢(E, F)) (g : 𝓢(E, G)) :
    ∫ ξ, M (𝓕 (T f) ξ) (𝓕 g ξ) =
      ∫ ξ, M' (𝓕 f ξ) (𝓕 (compCLMOfContinuousLinearEquiv ℂ
        (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv (S (compCLMOfContinuousLinearEquiv ℂ
          (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv g))) ξ) := by
  rw [integral_bilin_fourier_fourier_eq, integral_bilin_fourier_fourier_eq]
  simpa using hTS f (compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv g)

end SchwartzMap
