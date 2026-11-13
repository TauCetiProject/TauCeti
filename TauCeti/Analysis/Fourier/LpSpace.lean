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
# The Fourier integral on `L¹ ∩ L²`

On a finite-dimensional real inner product space `E`, Mathlib has two Fourier transforms: the
Fourier integral `𝓕 f ξ = ∫ 𝐞(-⟪x, ξ⟫) • f x` of a function, and the Fourier transform on
`L²(E, F)` (`MeasureTheory.Lp.fourierTransformₗᵢ`), obtained by extending the Fourier transform of
Schwartz functions by continuity. This file proves **Plancherel's theorem on `L¹ ∩ L²`**: if `f`
is integrable and square integrable, then `𝓕 f` is square integrable with `‖𝓕 f‖₂ = ‖f‖₂`.

It rests on the fact that the two transforms agree on `L¹ ∩ L²`: the `L²` Fourier
transform of the class of such an `f` is almost everywhere the Fourier integral of `f`. Both are
the Fourier transform of `f` as a tempered distribution
(`MeasureTheory.Lp.fourier_toTemperedDistribution_eq`,
`MeasureTheory.Lp.fourier_toTemperedDistribution_apply`), and an `L²` function is determined
almost everywhere by its pairings with Schwartz functions.

Together with the `L¹ → L^∞` bound `‖𝓕 f‖_∞ ≤ ‖f‖₁` (`TauCeti.eLpNorm_fourier_top_le`), these are
the two endpoint estimates which the Riesz–Thorin theorem interpolates to the Hausdorff–Young
inequality, in `TauCeti.Analysis.Fourier.HausdorffYoung`.

## Main declarations

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

namespace MeasureTheory.Integrable

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
