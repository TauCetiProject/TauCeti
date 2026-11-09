/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.Convolution

/-!
# The inverse Fourier transform of a convolution

Mathlib's convolution theorem `Real.fourier_mul_convolution_eq` says that the Fourier transform of
the convolution of two integrable functions is the product of their Fourier transforms. Since the
inverse Fourier transform is the Fourier transform evaluated at `-x`
(`Real.fourierInv_eq_fourier_neg`), the same holds for the inverse Fourier transform:

`𝓕⁻ (f₁ ⋆ f₂) = 𝓕⁻ f₁ * 𝓕⁻ f₂`

(`Real.fourierInv_mul_convolution_eq`). Read backwards, this writes the pointwise product of two
functions with integrable Fourier transforms as the inverse Fourier transform of an integrable
function, which is how products are handled in Fourier-side Sobolev estimates.
-/

public section

open MeasureTheory ContinuousLinearMap
open scoped Convolution FourierTransform

namespace Real

variable {E R : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedRing R] [NormedSpace ℂ R] [IsScalarTower ℂ R R]
  [SMulCommClass ℂ R R] [CompleteSpace R]

/-- **The convolution theorem for the inverse Fourier transform.** The inverse Fourier transform
of the convolution of two integrable functions is the product of their inverse Fourier
transforms. -/
theorem fourierInv_mul_convolution_eq {f₁ f₂ : E → R} (hf₁ : Integrable f₁) (hf₂ : Integrable f₂)
    (x : E) : 𝓕⁻ (f₁ ⋆[mul ℂ R] f₂) x = 𝓕⁻ f₁ x * 𝓕⁻ f₂ x := by
  simp only [fourierInv_eq_fourier_neg, fourier_mul_convolution_eq hf₁ hf₂]

end Real
