/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The almost-everywhere derivative of the logarithm of a curve of bounded variation

For a complex curve `σ` of bounded variation that stays in the slit plane, almost everywhere the
derivative of `Complex.log ∘ σ` is `deriv σ t / σ t`. For the quotient `f / g` of two such curves,
this is the difference of the two logarithmic derivatives. Absolute continuity of `Complex.log ∘ σ`
itself is `AbsolutelyContinuousOnInterval.clog`; an absolutely continuous curve is of bounded
variation, `AbsolutelyContinuousOnInterval.boundedVariationOn`.

## Main results

* `BoundedVariationOn.ae_hasDerivAt_clog`: the almost-everywhere derivative of `Complex.log ∘ σ`.
* `BoundedVariationOn.ae_hasDerivAt_clog_div`: the same for a quotient `f / g`.
-/

public section

open Complex MeasureTheory Set

namespace BoundedVariationOn

/-- Almost everywhere, the principal logarithm of a complex curve of bounded variation in the
slit plane has derivative `deriv σ t / σ t`. -/
theorem ae_hasDerivAt_clog {σ : ℝ → ℂ} {a b : ℝ} (hσ : BoundedVariationOn σ (uIcc a b))
    (h : ∀ t ∈ uIcc a b, σ t ∈ slitPlane) :
    ∀ᵐ t, t ∈ uIoc a b → HasDerivAt (fun t ↦ Complex.log (σ t)) (deriv σ t / σ t) t := by
  filter_upwards [hσ.ae_differentiableAt_of_mem_uIcc] with t ht ht'
  have ht'' := uIoc_subset_uIcc ht'
  exact (ht ht'').hasDerivAt.clog_real (h t ht'')

/-- Almost everywhere, the principal logarithm of the quotient of two complex curves of bounded
variation, which stays in the slit plane, has the difference of the two logarithmic derivatives as
derivative. -/
theorem ae_hasDerivAt_clog_div {f g : ℝ → ℂ} {a b : ℝ}
    (hf : BoundedVariationOn f (uIcc a b)) (hg : BoundedVariationOn g (uIcc a b))
    (h : ∀ t ∈ uIcc a b, f t / g t ∈ slitPlane) :
    ∀ᵐ t, t ∈ uIoc a b →
      HasDerivAt (fun t ↦ Complex.log (f t / g t)) (deriv f t / f t - deriv g t / g t) t := by
  have hf0 : ∀ t ∈ uIcc a b, f t ≠ 0 := fun t ht h0 ↦ by
    simpa [h0] using h t ht
  have hg0 : ∀ t ∈ uIcc a b, g t ≠ 0 := fun t ht h0 ↦ by
    simpa [h0] using h t ht
  filter_upwards [hf.ae_differentiableAt_of_mem_uIcc,
    hg.ae_differentiableAt_of_mem_uIcc] with t ht₀ ht₁ ht
  have ht' := uIoc_subset_uIcc ht
  have hdiv := logDeriv_fun_div t (hf0 t ht') (hg0 t ht') (ht₀ ht') (ht₁ ht')
  simp only [logDeriv_apply] at hdiv
  rw [← hdiv]
  exact ((ht₀ ht').div (ht₁ ht') (hg0 t ht')).hasDerivAt.clog_real (h t ht')

end BoundedVariationOn
