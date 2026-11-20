/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Logarithmic derivatives and integrals along complex curves

For a complex curve `σ` of bounded variation that stays in the slit plane, almost everywhere the
derivative of `Complex.log ∘ σ` is `deriv σ t / σ t`. For the quotient `f / g` of two such curves,
this is the difference of the two logarithmic derivatives. Absolute continuity of `Complex.log ∘ σ`
itself is `AbsolutelyContinuousOnInterval.clog`; an absolutely continuous curve is of bounded
variation, `AbsolutelyContinuousOnInterval.boundedVariationOn`.

## Main results

* `BoundedVariationOn.ae_hasDerivAt_clog`: the almost-everywhere derivative of `Complex.log ∘ σ`.
* `BoundedVariationOn.ae_hasDerivAt_clog_div`: the same for a quotient `f / g`.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_div`: integrability of the
  logarithmic derivative of a nonvanishing absolutely continuous curve.
* `AbsolutelyContinuousOnInterval.integral_deriv_div_sub_integral_deriv_div_eq_log_div_sub_log_div`:
  the complex logarithmic FTC for two absolutely continuous curves with slit-plane ratio.
* `AbsolutelyContinuousOnInterval.integral_deriv_div_eq_log_sub_log`: its single-curve form.
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

namespace AbsolutelyContinuousOnInterval

variable {f g : ℝ → ℂ} {a b : ℝ}

/-- The logarithmic derivative of a nonvanishing absolutely continuous complex curve is
interval integrable. -/
theorem intervalIntegrable_deriv_div (hf : AbsolutelyContinuousOnInterval f a b)
    (h0 : ∀ t ∈ uIcc a b, f t ≠ 0) :
    IntervalIntegrable (fun t ↦ deriv f t / f t) volume a b := by
  simpa only [div_eq_mul_inv, Pi.inv_apply] using
    hf.intervalIntegrable_deriv_of_finiteDimensional.mul_continuousOn (hf.continuousOn.inv₀ h0)

/-- For two absolutely continuous curves with slit-plane ratio, the difference of their
logarithmic-derivative integrals is the increment of the principal logarithm of the ratio. -/
theorem integral_deriv_div_sub_integral_deriv_div_eq_log_div_sub_log_div
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ t ∈ uIcc a b, f t / g t ∈ slitPlane) :
    (∫ t in a..b, deriv f t / f t) - ∫ t in a..b, deriv g t / g t =
      Complex.log (f b / g b) - Complex.log (f a / g a) := by
  have hne : ∀ t ∈ uIcc a b, f t ≠ 0 ∧ g t ≠ 0 := fun t ht ↦
    div_ne_zero_iff.mp (slitPlane_ne_zero (h t ht))
  have hlog := (hf.fun_div hg fun t ht ↦ (hne t ht).2).clog h
  have hint := hlog.integral_eq_sub_of_ae_hasDerivAt
    (hf.boundedVariationOn.ae_hasDerivAt_clog_div hg.boundedVariationOn h)
  rwa [intervalIntegral.integral_sub (hf.intervalIntegrable_deriv_div fun t ht ↦ (hne t ht).1)
    (hg.intervalIntegrable_deriv_div fun t ht ↦ (hne t ht).2)] at hint

/-- The logarithmic-derivative integral of an absolutely continuous curve in the slit plane
is the difference of the principal logarithms of its endpoints. -/
theorem integral_deriv_div_eq_log_sub_log (hf : AbsolutelyContinuousOnInterval f a b)
    (h : ∀ t ∈ uIcc a b, f t ∈ slitPlane) :
    ∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a) := by
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ (1 : ℂ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [div_one, deriv_const, zero_div, intervalIntegral.integral_zero, sub_zero] using
    hf.integral_deriv_div_sub_integral_deriv_div_eq_log_div_sub_log_div hconst
      (by simpa only [div_one] using h)

end AbsolutelyContinuousOnInterval
