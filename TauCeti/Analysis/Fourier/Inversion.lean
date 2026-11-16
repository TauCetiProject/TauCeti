/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Consequences of Fourier inversion

On a finite-dimensional real inner product space, a continuous integrable function whose Fourier
transform vanishes is zero. The vanishing transform is trivially integrable, so Mathlib's Fourier
inversion formula `Continuous.fourierInv_fourier_eq` applies and recovers the function as the
inverse transform of zero.

Fourier inversion also computes the pairing of a function `g` composed with a linear map `A` on
the Fourier side: writing `g (A x)` as `∫ 𝓕 g η 𝐞 ⟪Aᵀ η, x⟫ dη` and exchanging the integrals gives
`∫ ψ x g (A x) dx = ∫ 𝓕 g η 𝓕 ψ (-Aᵀ η) dη`. The right side makes sense for a distribution in
place of `g` when the Fourier transform of `ψ` absorbs its growth, which is how distributions are
pulled back along linear maps.

## Main results

* `Continuous.eq_zero_of_fourier_eq_zero`: a continuous integrable function with vanishing Fourier
  transform is zero.
* `ContinuousLinearMap.integral_mul_comp_eq_integral_fourier_mul_fourier`: the pairing of `ψ` with
  `g ∘ A` in Fourier variables.
-/

public section

open MeasureTheory Function
open scoped FourierTransform

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : V → E}

/-- A continuous integrable function whose Fourier transform vanishes is zero. -/
theorem Continuous.eq_zero_of_fourier_eq_zero (h : Continuous f) (hf : Integrable f)
    (hF : 𝓕 f = 0) : f = 0 := by
  have hinv := h.fourierInv_fourier_eq hf (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  ext v
  simp [Real.fourierInv_eq]

namespace ContinuousLinearMap

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

open scoped InnerProduct RealInnerProductSpace

/-- **Pairing with a composition in Fourier variables.** Let `A : V →L[ℝ] W` be linear, `g` a
continuous integrable function on `W` with integrable Fourier transform, and `ψ` integrable on `V`.
Then `∫ ψ x g (A x) dx = ∫ 𝓕 g η 𝓕 ψ (-Aᵀ η) dη`. -/
theorem integral_mul_comp_eq_integral_fourier_mul_fourier (A : V →L[ℝ] W) {g : W → ℂ}
    (hg : Continuous g) (hgi : Integrable g) (hFg : Integrable (𝓕 g)) {ψ : V → ℂ}
    (hψ : Integrable ψ) :
    ∫ x, ψ x * g (A x) = ∫ η, 𝓕 g η * 𝓕 ψ (-(A†) η) := by
  set F : V → W → ℂ := fun x η ↦ ψ x * (𝐞 ⟪(A†) η, x⟫ * 𝓕 g η)
  have hFi : Integrable (uncurry F) (volume.prod volume) := by
    refine Integrable.mono' (hψ.norm.mul_prod hFg.norm) ?_ (.of_forall fun p ↦ ?_)
    · have he : Continuous fun p : V × W ↦ (𝐞 ⟪(A†) p.2, p.1⟫ : ℂ) :=
        continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
      exact hψ.aestronglyMeasurable.comp_fst.mul
        (he.aestronglyMeasurable.mul hFg.aestronglyMeasurable.comp_snd)
    · simp [F, uncurry]
  -- Fourier inversion for `g`.
  have hinv (y : W) : g y = ∫ η, 𝐞 ⟪η, y⟫ • 𝓕 g η := by
    rw [← Real.fourierInv_eq, hg.fourierInv_fourier_eq hgi hFg]
  calc ∫ x, ψ x * g (A x)
      = ∫ x, ∫ η, F x η := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [hinv (A x), ← integral_const_mul]
        congr 1 with η
        simp [F, Circle.smul_def, adjoint_inner_left]
    _ = ∫ η, ∫ x, F x η := integral_integral_swap hFi
    _ = ∫ η, 𝓕 g η * 𝓕 ψ (-(A†) η) := by
        refine integral_congr_ae (.of_forall fun η ↦ ?_)
        dsimp only
        rw [Real.fourier_eq ψ, ← integral_const_mul]
        congr 1 with x
        simp only [F, Circle.smul_def, inner_neg_right, neg_neg, real_inner_comm, smul_eq_mul]
        ring

end ContinuousLinearMap
