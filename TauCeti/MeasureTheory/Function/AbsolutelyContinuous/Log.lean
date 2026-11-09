/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp

/-!
# The almost-everywhere derivative of the logarithm of an absolutely continuous curve

For an absolutely continuous complex curve `σ` that stays in the slit plane, almost everywhere the
derivative of `Complex.log ∘ σ` is `deriv σ t / σ t`. For the quotient `f / g` of two absolutely
continuous curves, this is the difference of the two logarithmic derivatives. Absolute continuity
of `Complex.log ∘ σ` itself is `AbsolutelyContinuousOnInterval.clog`.

## Main results

* `AbsolutelyContinuousOnInterval.ae_hasDerivAt_clog`: the almost-everywhere derivative of
  `Complex.log ∘ σ`.
* `AbsolutelyContinuousOnInterval.ae_hasDerivAt_log_div`: the same for a quotient `f / g`.
-/

public section

open Complex MeasureTheory Set

namespace AbsolutelyContinuousOnInterval

/-- Almost everywhere, the principal logarithm of an absolutely continuous complex curve in the
slit plane has derivative `deriv σ t / σ t`. -/
theorem ae_hasDerivAt_clog {σ : ℝ → ℂ} {a b : ℝ} (hσ : AbsolutelyContinuousOnInterval σ a b)
    (h : ∀ t ∈ uIcc a b, σ t ∈ slitPlane) :
    ∀ᵐ t, t ∈ uIoc a b → HasDerivAt (Complex.log ∘ σ) (deriv σ t / σ t) t := by
  filter_upwards [hσ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht ht'
  have ht'' := uIoc_subset_uIcc ht'
  exact (ht ht'').hasDerivAt.clog_real (h t ht'')

/-- Almost everywhere, the principal logarithm of the quotient of two absolutely continuous
complex curves, which stays in the slit plane, has the difference of the two logarithmic
derivatives as derivative. -/
theorem ae_hasDerivAt_log_div {f g : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ t ∈ uIcc a b, f t / g t ∈ slitPlane) :
    ∀ᵐ t, t ∈ uIoc a b →
      HasDerivAt (Complex.log ∘ fun t ↦ f t / g t) (deriv f t / f t - deriv g t / g t) t := by
  have hf0 : ∀ t ∈ uIcc a b, f t ≠ 0 := fun t ht h0 ↦ by
    simpa [h0] using h t ht
  have hg0 : ∀ t ∈ uIcc a b, g t ≠ 0 := fun t ht h0 ↦ by
    simpa [h0] using h t ht
  filter_upwards [(hf.fun_div hg hg0).ae_hasDerivAt_clog h,
    hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc,
    hg.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t hlog ht₀ ht₁ ht
  have ht' := uIoc_subset_uIcc ht
  have hdiv := logDeriv_fun_div t (hf0 t ht') (hg0 t ht') (ht₀ ht') (ht₁ ht')
  simp only [logDeriv_apply] at hdiv
  rw [← hdiv]
  exact hlog ht

end AbsolutelyContinuousOnInterval
