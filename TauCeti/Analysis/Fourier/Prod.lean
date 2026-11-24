/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fourier transforms of tensor products

On the Euclidean product `WithLp 2 (E × D)` of finite-dimensional real inner product spaces, the
Fourier transform of a tensor product `(x, y) ↦ f x • g y` is the tensor product of the Fourier
transforms of `f` and `g` (`Real.fourier_prod_smul`, and `Real.fourier_prod_mul` for scalar
`g`), by Fubini's theorem: the character `𝐞 (-⟪(x, y), (ξ, η)⟫)` is `𝐞 (-⟪x, ξ⟫) 𝐞 (-⟪y, η⟫)`.
-/

public section

noncomputable section

open MeasureTheory WithLp
open scoped FourierTransform RealInnerProductSpace

namespace Real

variable {E D F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Fourier transform of `(x, y) ↦ f x • g y` on the Euclidean product `WithLp 2 (E × D)` is
`(ξ, η) ↦ 𝓕 f ξ • 𝓕 g η`. -/
theorem fourier_prod_smul (f : E → ℂ) (g : D → F) (ζ : WithLp 2 (E × D)) :
    𝓕 (fun p : WithLp 2 (E × D) ↦ f p.fst • g p.snd) ζ = 𝓕 f ζ.fst • 𝓕 g ζ.snd := by
  simp only [Real.fourier_eq]
  rw [← (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E D).symm.integral_comp',
    ← integral_prod_smul, ← Measure.volume_eq_prod]
  congr 1
  ext q
  simp only [MeasurableEquiv.symm_symm, MeasurableEquiv.coe_toLp, toLp_fst, toLp_snd,
    prod_inner_apply, neg_add, AddChar.map_add_eq_mul, Circle.smul_def, Circle.coe_mul,
    ofLp_fst, ofLp_snd, smul_smul]
  ring_nf

/-- The Fourier transform of `(x, y) ↦ f x * g y` on the Euclidean product `WithLp 2 (E × D)` is
the product of the Fourier transforms of `f` and `g`. -/
theorem fourier_prod_mul (f : E → ℂ) (g : D → ℂ) (ζ : WithLp 2 (E × D)) :
    𝓕 (fun p : WithLp 2 (E × D) ↦ f p.fst * g p.snd) ζ = 𝓕 f ζ.fst * 𝓕 g ζ.snd :=
  fourier_prod_smul f g ζ

end Real
