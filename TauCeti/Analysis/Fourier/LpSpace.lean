/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
public import TauCeti.Analysis.Fourier.Continuous

/-!
# The Fourier integral on `L¹` and on `L¹ ∩ L²`

On a finite-dimensional real inner product space `E`, Mathlib has two Fourier transforms: the
Fourier integral `𝓕 f ξ = ∫ 𝐞(-⟪x, ξ⟫) • f x` of a function, and the Fourier transform on
`L²(E, F)` (`MeasureTheory.Lp.fourierTransformₗᵢ`), obtained by extending the Fourier transform of
Schwartz functions by continuity. This file records the two `Lᵖ` bounds for the Fourier integral
that hold with constant `1`, together with its additivity on integrable functions:

* the `L¹ → L^∞` bound `‖𝓕 f‖_∞ ≤ ‖f‖₁`, for every `f`;
* **Plancherel's theorem on `L¹ ∩ L²`**: if `f` is integrable and square integrable, then `𝓕 f`
  is square integrable with `‖𝓕 f‖₂ = ‖f‖₂`.

The second rests on the fact that the two transforms agree on `L¹ ∩ L²`: the `L²` Fourier
transform of the class of such an `f` is almost everywhere the Fourier integral of `f`. Both are
the Fourier transform of `f` as a tempered distribution
(`MeasureTheory.Lp.fourier_toTemperedDistribution_eq`,
`MeasureTheory.Lp.fourier_toTemperedDistribution_apply`), and an `L²` function is determined
almost everywhere by its pairings with Schwartz functions.

These are the two endpoint estimates which the Riesz–Thorin theorem interpolates to the
Hausdorff–Young inequality, in `TauCeti.Analysis.Fourier.HausdorffYoung`.

## Main declarations

* `TauCeti.eLpNorm_fourier_top_le`: `‖𝓕 f‖_∞ ≤ ‖f‖₁`.
* `MeasureTheory.Integrable.fourier_add`, `MeasureTheory.Integrable.fourier_sub`: the Fourier
  integral is additive on integrable functions.
* `MeasureTheory.Integrable.coeFn_fourier_toLp`: on `L¹ ∩ L²` the `L²` Fourier transform is the
  Fourier integral.
* `MeasureTheory.Integrable.eLpNorm_fourier_two_eq`: Plancherel's theorem on `L¹ ∩ L²`.
* `MeasureTheory.Integrable.memLp_fourier_two`: the Fourier integral of a function in `L¹ ∩ L²`
  lies in `L²`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 2.2.4.
* E. M. Stein, G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter I,
  Theorem 2.1.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TauCeti

variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Fourier integral is bounded from `L¹` to `L^∞` with norm at most one:
`‖𝓕 f‖_∞ ≤ ‖f‖₁`. No integrability is assumed; for a function outside `L¹` the bound is trivial. -/
theorem eLpNorm_fourier_top_le (f : E → F) : eLpNorm (𝓕 f) ∞ volume ≤ eLpNorm f 1 volume := by
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

namespace MeasureTheory.Integrable

section Additive

variable [NormedAddCommGroup F] [NormedSpace ℂ F] {f g : E → F}

/-- The Fourier integral is additive on integrable functions. -/
theorem fourier_add (hf : Integrable f) (hg : Integrable g) : 𝓕 (f + g) = 𝓕 f + 𝓕 g :=
  VectorFourier.fourierIntegral_add (L := innerₗ E) Real.continuous_fourierChar continuous_inner
    hf hg

/-- The Fourier integral of a difference of integrable functions is the difference of their
Fourier integrals. -/
theorem fourier_sub (hf : Integrable f) (hg : Integrable g) : 𝓕 (f - g) = 𝓕 f - 𝓕 g := by
  -- On functions, `𝓕` is by definition the Fourier integral `VectorFourier.fourierIntegral` for
  -- the pairing `innerₗ E` (`Real.instFourierTransform`), so its scaling lemma applies directly.
  have h : 𝓕 (-g) = -𝓕 g := by
    have h := VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ E) g (-1)
    rw [neg_one_smul, neg_one_smul] at h
    exact h
  rw [sub_eq_add_neg, hf.fourier_add hg.neg, h, ← sub_eq_add_neg]

end Additive

variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {f : E → F}

/-- On `L¹ ∩ L²` the Fourier transform on `L²` is the Fourier integral: for `f` integrable and
square integrable, the `L²` Fourier transform of the class of `f` is almost everywhere `𝓕 f`. -/
theorem coeFn_fourier_toLp (hf : Integrable f) (hf₂ : MemLp f 2) :
    ⇑(𝓕 (hf₂.toLp f) : Lp F 2 (volume : Measure E)) =ᵐ[volume] 𝓕 f := by
  refine Lp.ae_eq_of_toTemperedDistribution_apply_eq _ hf.continuous_fourier.locallyIntegrable
    fun φ => ?_
  rw [← Lp.fourier_toTemperedDistribution_eq]
  exact Lp.fourier_toTemperedDistribution_apply _ hf hf₂.coeFn_toLp φ

/-- **Plancherel's theorem on `L¹ ∩ L²`.** The Fourier integral of an integrable, square
integrable function has the same `L²` norm as the function. -/
theorem eLpNorm_fourier_two_eq (hf : Integrable f) (hf₂ : MemLp f 2) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  rw [← eLpNorm_congr_ae (hf.coeFn_fourier_toLp hf₂), ← eLpNorm_congr_ae hf₂.coeFn_toLp,
    ← ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _), ← Lp.norm_def,
    ← Lp.norm_def, Lp.norm_fourier_eq]

/-- The Fourier integral of an integrable, square integrable function is square integrable. -/
theorem memLp_fourier_two (hf : Integrable f) (hf₂ : MemLp f 2) : MemLp (𝓕 f) 2 :=
  memLp_iff.2 ((hf.eLpNorm_fourier_two_eq hf₂).trans_lt hf₂.eLpNorm_lt_top)

end MeasureTheory.Integrable
