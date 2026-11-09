/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# The Fourier integral of an integrable function

On a finite-dimensional real inner-product space, the Fourier transform `𝓕 f` of an integrable
`f` with values in a complex normed space is continuous, and so is the inverse transform `𝓕⁻ f`.
These are Mathlib's `VectorFourier.fourierIntegral_continuous` specialized to the inner-product
pairing and its negation, packaged so that consumers do not repeat the pairing-continuity bridge
at every call site.

This file also records the elementary algebraic and `L¹` properties of the Fourier integral of a
function: it is homogeneous for every function and additive on integrable functions, it is
bounded from `L¹` to `L^∞` with norm at most one, and `L¹` convergence of integrable functions
makes their Fourier integrals converge uniformly.

## Main declarations

* `MeasureTheory.Integrable.continuous_fourier`: `𝓕 f` is continuous for integrable `f`.
* `MeasureTheory.Integrable.continuous_fourierInv`: `𝓕⁻ f` is continuous for integrable `f`.
* `Real.fourier_const_smul`, `Real.fourier_neg`: `𝓕 (c • f) = c • 𝓕 f` and `𝓕 (-f) = -𝓕 f`.
* `MeasureTheory.Integrable.fourier_add`, `MeasureTheory.Integrable.fourier_sub`: the Fourier
  integral is additive on integrable functions.
* `TauCeti.eLpNorm_fourier_top_le`: `‖𝓕 f‖_∞ ≤ ‖f‖₁`.
* `MeasureTheory.Integrable.tendstoUniformly_fourier`: if integrable `gᵢ` tend to an integrable
  `f` in `L¹`, then `𝓕 gᵢ` tends to `𝓕 f` uniformly.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform

namespace MeasureTheory.Integrable

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

/-- The Fourier transform of an integrable function is continuous. This is Mathlib's
`VectorFourier.fourierIntegral_continuous` specialized to the inner-product pairing. -/
theorem continuous_fourier (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

/-- The inverse Fourier transform of an integrable function is continuous. This is Mathlib's
`VectorFourier.fourierIntegral_continuous` specialized to the negated inner-product pairing. -/
theorem continuous_fourierInv (hf : Integrable f) : Continuous (𝓕⁻ f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (-innerSL ℝ).continuous₂ hf

end MeasureTheory.Integrable

namespace Real

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Fourier integral of a function is homogeneous: `𝓕 (c • f) = c • 𝓕 f`. On functions, `𝓕`
is by definition `VectorFourier.fourierIntegral` for the pairing `innerₗ V`
(`Real.instFourierTransform`), so this is Mathlib's `VectorFourier.fourierIntegral_const_smul`. -/
@[simp]
theorem fourier_const_smul (c : ℂ) (f : V → E) : 𝓕 (c • f) = c • 𝓕 f :=
  VectorFourier.fourierIntegral_const_smul _ _ _ _ _

/-- The Fourier integral of `-f` is `-𝓕 f`. -/
@[simp]
theorem fourier_neg (f : V → E) : 𝓕 (-f) = -𝓕 f := by
  simpa only [neg_one_smul] using fourier_const_smul (-1) f

end Real

namespace MeasureTheory.Integrable

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : V → E}

/-- The Fourier integral is additive on integrable functions. -/
theorem fourier_add (hf : Integrable f) (hg : Integrable g) : 𝓕 (f + g) = 𝓕 f + 𝓕 g :=
  VectorFourier.fourierIntegral_add (L := innerₗ V) Real.continuous_fourierChar continuous_inner
    hf hg

/-- The Fourier integral of a difference of integrable functions is the difference of their
Fourier integrals. -/
theorem fourier_sub (hf : Integrable f) (hg : Integrable g) : 𝓕 (f - g) = 𝓕 f - 𝓕 g := by
  rw [sub_eq_add_neg, hf.fourier_add hg.neg, Real.fourier_neg, ← sub_eq_add_neg]

/-- If integrable functions `gᵢ` tend to an integrable function `f` in `L¹`, then their Fourier
integrals tend to `𝓕 f` uniformly, since `‖𝓕 gᵢ - 𝓕 f‖_∞ ≤ ‖gᵢ - f‖₁`. -/
theorem tendstoUniformly_fourier {ι : Type*} {l : Filter ι} {g : ι → V → E} (hf : Integrable f)
    (hg : ∀ i, Integrable (g i)) (h : Tendsto (fun i => eLpNorm (g i - f) 1 volume) l (𝓝 0)) :
    TendstoUniformly (fun i => 𝓕 (g i)) (𝓕 f) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).eventually
    (gt_mem_nhds (by simpa using hε))] with i hi ξ
  rw [dist_eq_norm', ← Pi.sub_apply (𝓕 (g i)), ← (hg i).fourier_sub hf]
  refine (Real.norm_fourier_le_integral_norm _ _).trans_lt ?_
  rwa [integral_norm_eq_lintegral_enorm ((hg i).1.sub hf.1),
    ← eLpNorm_one_eq_lintegral_enorm ((hg i).1.sub hf.1)]

end MeasureTheory.Integrable

namespace TauCeti

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Fourier integral is bounded from `L¹` to `L^∞` with norm at most one:
`‖𝓕 f‖_∞ ≤ ‖f‖₁`. No integrability is assumed; for a function outside `L¹` the bound is trivial. -/
theorem eLpNorm_fourier_top_le (f : V → E) : eLpNorm (𝓕 f) ∞ volume ≤ eLpNorm f 1 volume := by
  by_cases hf : Integrable f
  · rw [eLpNorm_exponent_top hf.continuous_fourier.aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_enorm_bound (ae_of_all _ fun ξ => ?_)
    rw [Real.fourier_eq]
    refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
    simp only [Circle.enorm_smul]
  · have h : eLpNorm f 1 volume = ∞ := by
      by_contra h
      exact hf (memLp_one_iff_integrable.1 (memLp_iff.2 (lt_top_iff_ne_top.2 h)))
    rw [h]
    exact le_top

end TauCeti
