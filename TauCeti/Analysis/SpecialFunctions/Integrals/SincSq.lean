/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The integral of `sinc²`

Unlike `Real.sinc` itself, whose integral over `[0, ∞)` exists only as an improper limit, its
square is Lebesgue integrable on `ℝ`, being bounded by `2 / (1 + x²)`, and

`∫ x, sinc x ^ 2 = π`.

The derivative of `x ↦ sin x * sinc x = sin² x / x` is `2 sinc (2x) - sinc² x` away from `0`, so
`∫₀ᴿ sinc² = ∫₀^{2R} sinc - sin R sinc R`. As `R → ∞` the Dirichlet integral
`TauCeti.Contour.tendsto_integral_sinc_atTop` gives `∫₀^∞ sinc² = π / 2`, and evenness doubles it.

## Main results

* `TauCeti.integrable_sinc_sq`: `sinc ^ 2` is integrable on `ℝ`.
* `TauCeti.integral_Ioi_sinc_sq`: `∫ x in Ioi 0, sinc x ^ 2 = π / 2`.
* `TauCeti.integral_sinc_sq`: `∫ x, sinc x ^ 2 = π`.
-/

public section

open MeasureTheory Filter Set Real
open scoped Topology

namespace TauCeti

/-- The square of the sinc function is Lebesgue integrable on `ℝ`. -/
theorem integrable_sinc_sq : Integrable fun x : ℝ ↦ sinc x ^ 2 := by
  refine (integrable_inv_one_add_sq.const_mul 2).mono'
    (continuous_sinc.pow 2).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sinc_sq_le_two_div_one_add_sq x).trans_eq (div_eq_mul_inv _ _)

/-- Away from `0`, `x ↦ sin x * sinc x` has derivative `2 sinc (2x) - sinc² x`. -/
private theorem hasDerivAt_sin_mul_sinc {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y ↦ sin y * sinc y) (2 * sinc (2 * x) - sinc x ^ 2) x := by
  have heq : (fun y ↦ sin y * sinc y) =ᶠ[𝓝 x] fun y ↦ sin y ^ 2 / y := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [sinc_of_ne_zero hy]
    ring
  refine ((((hasDerivAt_sin x).pow 2).div (hasDerivAt_id x) hx).congr_of_eventuallyEq
    heq).congr_deriv ?_
  rw [sinc_of_ne_zero (mul_ne_zero two_ne_zero hx), sinc_of_ne_zero hx, sin_two_mul]
  simp only [id, Pi.pow_apply]
  field_simp
  ring

/-- `∫₀ᴿ sinc² = ∫₀^{2R} sinc - sin R sinc R` for `0 ≤ R`. -/
private theorem intervalIntegral_sinc_sq_eq {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in 0..R, sinc x ^ 2 = (∫ x in 0..2 * R, sinc x) - sin R * sinc R := by
  have hint₁ : IntervalIntegrable (fun x ↦ sinc x ^ 2) volume 0 R :=
    (continuous_sinc.pow 2).intervalIntegrable _ _
  have hint₂ : IntervalIntegrable (fun x ↦ 2 * sinc (2 * x)) volume 0 R :=
    (continuous_const.mul (continuous_sinc.comp (continuous_const.mul continuous_id))
      ).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
    (continuous_sin.mul continuous_sinc).continuousOn
    (fun x hx ↦ hasDerivAt_sin_mul_sinc hx.1.ne') (hint₂.sub hint₁)
  have hdil : ∫ x in 0..R, 2 * sinc (2 * x) = ∫ x in 0..2 * R, sinc x := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun x ↦ sinc x) two_ne_zero]
    simp
  rw [intervalIntegral.integral_sub hint₂ hint₁, hdil] at hftc
  simp only [Pi.mul_apply, sin_zero, zero_mul, sub_zero] at hftc
  linarith

/-- The truncated integrals `∫₀ᴿ sinc²` tend to `π / 2`. -/
private theorem tendsto_intervalIntegral_sinc_sq_atTop :
    Tendsto (fun R ↦ ∫ x in 0..R, sinc x ^ 2) atTop (𝓝 (π / 2)) := by
  have h₁ : Tendsto (fun R ↦ ∫ x in 0..2 * R, sinc x) atTop (𝓝 (π / 2)) :=
    Contour.tendsto_integral_sinc_atTop.comp (tendsto_id.const_mul_atTop two_pos)
  have h₂ : Tendsto (fun R ↦ sin R * sinc R) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
    · filter_upwards [eventually_gt_atTop 0] with R hR
      rw [sinc_of_ne_zero hR.ne', ← mul_div_assoc]
      exact div_nonneg (mul_self_nonneg _) hR.le
    · filter_upwards [eventually_gt_atTop 0] with R hR
      rw [sinc_of_ne_zero hR.ne', ← mul_div_assoc, ← sq, div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.2 hR.le) (sin_sq_le_one R)
  simpa using (h₁.sub h₂).congr' <| by
    filter_upwards [eventually_ge_atTop 0] with R hR
    exact (intervalIntegral_sinc_sq_eq hR).symm

/-- `∫₀^∞ sinc² x dx = π / 2`. -/
theorem integral_Ioi_sinc_sq : ∫ x in Ioi 0, sinc x ^ 2 = π / 2 :=
  tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi 0 integrable_sinc_sq.integrableOn tendsto_id)
    tendsto_intervalIntegral_sinc_sq_atTop

/-- `∫_ℝ sinc² x dx = π`. -/
theorem integral_sinc_sq : ∫ x, sinc x ^ 2 = π := by
  have h := integral_comp_abs (f := fun x ↦ sinc x ^ 2)
  have hfun : (fun x : ℝ ↦ sinc |x| ^ 2) = fun x ↦ sinc x ^ 2 :=
    funext fun x ↦ by rcases abs_choice x with h | h <;> simp [h]
  simp only [hfun, integral_Ioi_sinc_sq] at h
  linarith

end TauCeti
