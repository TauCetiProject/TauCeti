/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.PrekopaLeindler.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Real-valued Prékopa–Leindler

For nonnegative real functions `f` and `g` and an integrable real function `h`, the pointwise
bound

`f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)`

implies the same inequality between their integrals. The function `h` may be only a.e.
measurable, but the bound is imposed on the supplied representatives at every pair of
points. Measurable minorants and a majorant preserve this bound when applying the
extended-valued theorem, without assuming that affine combinations avoid exceptional null sets.

`MeasureTheory.Measure.HasPrekopaLeindler.integral` applies to any measure with the
Prékopa–Leindler property. `MeasureTheory.Measure.integral_rpow_mul_integral_rpow_le_integral`
specializes it to additive Haar measures on finite-dimensional real normed spaces, including
Euclidean volume. Weights at the endpoints use `0 ^ 0 = 1`; no positivity of the input
integrals is assumed. Neither `f` nor `g` needs to be integrable: a non-integrable input has
integral `0`, and the inequality then holds because `h` is nonnegative and, at an endpoint
weight, dominates the other input. Integrability of `h` prevents its infinite integral from being
totalized to zero.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., AMS, 2001, Section 4.3.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E] [Module ℝ E]

/-- **Real-valued Prékopa–Leindler.** Nonnegative inputs satisfying the pointwise
geometric-mean bound by an integrable function have the corresponding bound on their integrals.
No measurability or integrability of the inputs is needed, while the bound concerns every pair
of points of the given representatives. -/
theorem HasPrekopaLeindler.integral {μ : Measure E} {θ : ℝ}
    (hμ : μ.HasPrekopaLeindler θ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    {f g h : E → ℝ} (hh : Integrable h μ) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x)
    (hfg : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)) :
    (∫ x, f x ∂μ) ^ (1 - θ) * (∫ x, g x ∂μ) ^ θ ≤ ∫ x, h x ∂μ := by
  have hh₀ (x : E) : 0 ≤ h x := by
    have hx := hfg x x
    simp only [← add_smul, sub_add_cancel, one_smul] at hx
    exact (mul_nonneg (Real.rpow_nonneg (hf₀ x) _) (Real.rpow_nonneg (hg₀ x) _)).trans hx
  have hofReal {u : E → ℝ} (hu : ∀ x, 0 ≤ u x) :
      ENNReal.ofReal (∫ x, u x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (u x) ∂μ := by
    simpa only [Real.eNorm_of_nonneg (integral_nonneg hu), Real.eNorm_of_nonneg (hu _)] using
      eNorm_integral_le_lintegral_eNorm u
  have hbound := hμ.lintegral hθ₀ hθ₁ hh.aemeasurable.ennreal_ofReal
    (f := fun x => ENNReal.ofReal (f x)) (g := fun x => ENNReal.ofReal (g x))
    (fun x y => by
      rw [ENNReal.ofReal_rpow_mul_ofReal_rpow (hf₀ x) (hg₀ y) (sub_nonneg.mpr hθ₁) hθ₀]
      exact ENNReal.ofReal_le_ofReal (hfg x y))
  rw [← ofReal_integral_eq_lintegral_ofReal hh (.of_forall hh₀)] at hbound
  refine (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hh₀)).mp ?_
  rw [← ENNReal.ofReal_rpow_mul_ofReal_rpow (integral_nonneg hf₀) (integral_nonneg hg₀)
    (sub_nonneg.mpr hθ₁) hθ₀]
  exact (mul_le_mul' (ENNReal.rpow_le_rpow (hofReal hf₀) (sub_nonneg.mpr hθ₁))
    (ENNReal.rpow_le_rpow (hofReal hg₀) hθ₀)).trans hbound

end MeasureTheory.Measure

namespace MeasureTheory.Measure

/-- **Prékopa–Leindler for real functions on a finite-dimensional real space.**
Every additive Haar measure, in particular Euclidean volume, satisfies the weighted integral
inequality for nonnegative functions with the pointwise geometric-mean bound by an integrable
function. -/
theorem integral_rpow_mul_integral_rpow_le_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) {f g h : E → ℝ}
    (hh : Integrable h μ) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x)
    (hfg : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)) :
    (∫ x, f x ∂μ) ^ (1 - θ) * (∫ x, g x ∂μ) ^ θ ≤ ∫ x, h x ∂μ :=
  (hasPrekopaLeindler_of_isAddHaarMeasure μ hθ₀ hθ₁).integral hθ₀ hθ₁ hh hf₀ hg₀ hfg

end MeasureTheory.Measure
