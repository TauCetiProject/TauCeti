/-
Copyright (c) 2024 David Loeffler; 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, David Loeffler, Heather Macbeth, Sébastien Gouëzel,
  The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# The Fourier transform of an iterated derivative under weak regularity

Mathlib's `VectorFourier.fourierIntegral_iteratedFDeriv` computes the Fourier integral of the
`n`-th iterated derivative of a `C^N` function `f` whose derivatives up to order `N` are
integrable. Its induction applies the first-order formula `VectorFourier.fourierIntegral_fderiv`
once per order, which only needs each derivative below order `n` to be differentiable; continuity
of the top derivative is never used. This file records the identity under that weaker hypothesis.

## Main results

* `VectorFourier.fourierIntegral_iteratedFDeriv_of_differentiable`: the Fourier integral of
  `D^n f` with respect to a bilinear pairing `L` is the Fourier integral of `f` multiplied by
  `(2πi L ⬝ w)^n`, when the derivatives below order `n` are differentiable and those up to
  order `n` are integrable.
* `Real.fourier_iteratedFDeriv_of_differentiable`: the same identity for the Fourier transform
  on a finite-dimensional real inner product space.
-/

public section

open scoped FourierTransform

namespace VectorFourier

open Real Complex MeasureTheory

variable {V W E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace V] [BorelSpace V]
  (L : V →L[ℝ] W →L[ℝ] ℝ) {f : V → E}

/-- The Fourier integral of the `n`-th derivative of a function is obtained by multiplying the
Fourier integral of the original function by `(2πI L w ⬝ )^n`. Unlike Mathlib's
`VectorFourier.fourierIntegral_iteratedFDeriv`, only the derivatives below order `n` need to be
differentiable. -/
theorem fourierIntegral_iteratedFDeriv_of_differentiable [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {n : ℕ}
    (hf : ∀ k < n, Differentiable ℝ (iteratedFDeriv ℝ k f))
    (h'f : ∀ k ≤ n, Integrable (iteratedFDeriv ℝ k f) μ) :
    fourierIntegral 𝐞 μ L.toLinearMap₁₂ (iteratedFDeriv ℝ n f)
      = (fun w ↦ fourierPowSMulRight (-L.flip) (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) w n) := by
  classical
  induction n with
  | zero =>
    ext w m
    simp only [iteratedFDeriv_zero_apply, fourierPowSMulRight_apply, pow_zero, Finset.univ_eq_empty,
      neg_apply, ContinuousLinearMap.flip_apply, Finset.prod_empty, one_smul,
      fourierIntegral_continuousMultilinearMap_apply' ((h'f 0 le_rfl))]
  | succ n ih =>
    -- Select the normed structure before transporting integrability through currying.
    let : NormedAddCommGroup (V →L[ℝ] V [×n]→L[ℝ] E) := inferInstance
    ext w m
    have J : Integrable (fderiv ℝ (iteratedFDeriv ℝ n f)) μ := by
      specialize h'f (n + 1) le_rfl
      rwa [iteratedFDeriv_succ_eq_comp_left, Function.comp_def,
          LinearIsometryEquiv.integrable_comp_iff (𝕜 := ℝ) (φ := fderiv ℝ (iteratedFDeriv ℝ n f))]
        at h'f
    suffices H : (fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fderiv ℝ (iteratedFDeriv ℝ n f)) w)
          (m 0) (Fin.tail m) =
        (-(2 * π * I)) ^ (n + 1) • (∏ x : Fin (n + 1), -L (m x) w) • ∫ v, 𝐞 (-L v w) • f v ∂μ by
      rw [fourierIntegral_continuousMultilinearMap_apply' (h'f _ le_rfl)]
      simp only [iteratedFDeriv_succ_apply_left, fourierPowSMulRight_apply, neg_apply,
        ContinuousLinearMap.flip_apply]
      rw [← fourierIntegral_continuousMultilinearMap_apply' ((J.apply_continuousLinearMap _)),
          ← fourierIntegral_continuousLinearMap_apply' J]
      exact H
    rw [fourierIntegral_fderiv _ (h'f n n.le_succ) (hf n n.lt_succ_self) J]
    simp only [ih (fun k hk ↦ hf k (hk.trans n.lt_succ_self))
        (fun k hk ↦ h'f k (hk.trans n.le_succ)), fourierSMulRight_apply, neg_apply,
      ContinuousLinearMap.flip_apply, neg_smul, smul_neg, neg_neg, smul_apply,
      fourierPowSMulRight_apply, ← coe_smul (E := E), smul_smul]
    congr 1
    simp only [ofReal_prod, ofReal_neg, pow_succ, mul_neg, Fin.prod_univ_succ, neg_mul,
      ofReal_mul, neg_neg, Fin.tail_def]
    ring

end VectorFourier

namespace Real

open MeasureTheory

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

/-- The Fourier transform of the `n`-th derivative of a function is obtained by multiplying the
Fourier transform of the original function by `(2πI ⟪⬝, w⟫)^n`. Unlike Mathlib's
`Real.fourier_iteratedFDeriv`, only the derivatives below order `n` need to be differentiable. -/
theorem fourier_iteratedFDeriv_of_differentiable {n : ℕ}
    (hf : ∀ k < n, Differentiable ℝ (iteratedFDeriv ℝ k f))
    (h'f : ∀ k ≤ n, Integrable (iteratedFDeriv ℝ k f)) :
    𝓕 (iteratedFDeriv ℝ n f)
      = (fun w ↦ VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 f) w n) := by
  rw [← flip_innerSL_real V]
  exact VectorFourier.fourierIntegral_iteratedFDeriv_of_differentiable (innerSL ℝ) hf h'f

end Real
