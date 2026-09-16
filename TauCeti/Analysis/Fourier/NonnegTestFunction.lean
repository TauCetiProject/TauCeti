/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Fourier.Convolution
import TauCeti.Analysis.Bochner.Fourier.Nonneg

/-!
# A smooth compactly supported function with nonnegative Fourier transform

On a finite-dimensional real inner-product space there is a smooth, compactly supported function
`psi` whose Fourier transform is real and nonnegative everywhere and strictly positive at the
origin. Such a test function turns a limit statement about a Fourier-weighted sum with nonnegative
summands into an upper bound on the summands near the origin of the frequency variable, which is
how Tauberian arguments extract a Chebyshev-type growth bound from smoothed asymptotics.

The function is the autocorrelation `g ⋆ g` of a real bump function `g`. The bump function is even
and real, so its Fourier transform is real
(`TauCeti.fourier_eq_re_of_map_neg_eq_conj`), and the Fourier transform of the convolution is
the square of that real number (`Real.fourier_mul_convolution_eq`). At the origin it is the square
of `∫ g`, which is positive.

## Main results

* `TauCeti.exists_contDiff_hasCompactSupport_fourier_nonneg`: a smooth compactly supported
  function whose Fourier transform is nonnegative everywhere and positive at `0`.
-/

public section

open Complex MeasureTheory
open scoped ComplexOrder ContDiff Convolution FourierTransform

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- There is a smooth compactly supported complex-valued function on `V` whose Fourier transform
is nonnegative (in `ComplexOrder`, so real and nonnegative) at every frequency and strictly
positive at the origin. -/
theorem exists_contDiff_hasCompactSupport_fourier_nonneg :
    ∃ psi : V → ℂ, ContDiff ℝ ∞ psi ∧ HasCompactSupport psi ∧
      (∀ ξ : V, 0 ≤ 𝓕 psi ξ) ∧ 0 < 𝓕 psi 0 := by
  let φ : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  let g : V → ℂ := fun v ↦ (φ v : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp φ.contDiff
  have hgc : HasCompactSupport g := φ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hre : ∀ ξ : V, 𝓕 g ξ = ((𝓕 g ξ).re : ℂ) :=
    fourier_eq_re_of_map_neg_eq_conj g (fun v ↦ by simp [g, φ.neg]) hgi
  have hsq : ∀ ξ : V, 𝓕 (g ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ξ =
      (((𝓕 g ξ).re * (𝓕 g ξ).re : ℝ) : ℂ) := fun ξ ↦ by
    rw [Real.fourier_mul_convolution_eq hgi hgi, hre, Complex.ofReal_mul, Complex.ofReal_re]
  have h0 : (𝓕 g 0).re = ∫ v, φ v := by
    have : 𝓕 g 0 = ((∫ v, φ v : ℝ) : ℂ) := by
      simp only [Real.fourier_eq, inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul, g]
      exact integral_ofReal
    rw [this, Complex.ofReal_re]
  have hconv : g ⋆[ContinuousLinearMap.mul ℂ ℂ] g = g ⋆[ContinuousLinearMap.mul ℝ ℂ] g := by
    ext v
    simp [convolution_def]
  refine ⟨g ⋆[ContinuousLinearMap.mul ℂ ℂ] g, ?_, hgc.convolution _ hgc, fun ξ ↦ ?_, ?_⟩
  · rw [hconv]
    exact hgc.contDiff_convolution_left _ hg hgi.locallyIntegrable
  · rw [hsq, Complex.zero_le_real]
    exact mul_self_nonneg _
  · rw [hsq, Complex.zero_lt_real, h0]
    exact mul_pos φ.integral_pos φ.integral_pos

end TauCeti
