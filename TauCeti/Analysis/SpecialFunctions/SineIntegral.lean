/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Bounds for the sine integral

This file defines the sine integral `Si x = ∫_0^x sin t / t dt` and proves the explicit bounds
used to truncate Dirichlet-kernel integrals:

* `Si` is odd and continuous, with derivative `sinc`, and tends to `-π / 2` at `-∞`;
* `|Si x| ≤ Si π` for every real `x`, the first maximum of `Si` being its global maximum;
* `(cos x - 1) / x ≤ π / 2 - Si x ≤ (1 + cos x) / x` for `x > 0`, so `|π / 2 - Si x| ≤ 2 / x`;
* `|∫_a^b sin (T v) / v dv| ≤ 2 Si π` for all real `a`, `b` and `T`.

The two-sided tail bound comes from two monotone comparison functions on `(0, ∞)`:
`Si x + (cos x - 1) / x` has derivative `(1 - cos x) / x² ≥ 0` and `Si x + (cos x + 1) / x` has
derivative `-(1 + cos x) / x² ≤ 0`. This is the integration by parts
`∫_x^R sin t / t dt = cos x / x - cos R / R - ∫_x^R cos t / t² dt` in monotone form. Letting
`R → ∞` against the Dirichlet integral `Si R → π / 2`, which is
`TauCeti.Contour.tendsto_integral_sinc_atTop` after unfolding `sineIntegral`, gives the tail
bound. On `[0, π]` the integrand is nonnegative, and beyond `π` the second comparison function is
bounded by its value `Si π` at `π`, which gives the global maximum.

## Main declarations

* `Real.sineIntegral`: the sine integral `Si x = ∫_0^x sinc t dt`.
* `Real.integral_sin_div_eq_sub`: `∫_a^b sin t / t dt = Si b - Si a`.
* `Real.abs_sineIntegral_le`: `|Si x| ≤ Si π`.
* `Real.abs_sineIntegral_sub_le`: `|Si R - Si x| ≤ 2 / x` for `0 < x ≤ R`.
* `Real.abs_pi_div_two_sub_sineIntegral_le`: `|π / 2 - Si x| ≤ 2 / x` for `x > 0`.
* `Real.abs_integral_sin_mul_div_le`: `|∫_a^b sin (T v) / v dv| ≤ 2 Si π`.

## References

* NIST Digital Library of Mathematical Functions, §6.2 (6.2.19), §6.12 (6.12.5 to 6.12.8) and
  §6.16 (the maxima of `Si`).
-/

public section

open Filter Set Topology intervalIntegral Real

namespace Real

/-- The **sine integral** `Si x = ∫_0^x sin t / t dt`. The integrand is written as the continuous
function `Real.sinc`, which agrees with `sin t / t` away from `t = 0`; see
`integral_sin_div_eq_sub` for the `sin t / t` spelling. -/
noncomputable def sineIntegral (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, sinc t

/-- The sine integral is a primitive of `sinc`. -/
theorem hasDerivAt_sineIntegral (x : ℝ) : HasDerivAt sineIntegral (sinc x) x :=
  (continuous_sinc.integral_hasStrictDerivAt 0 x).hasDerivAt

@[simp]
theorem deriv_sineIntegral : deriv sineIntegral = sinc :=
  funext fun x ↦ (hasDerivAt_sineIntegral x).deriv

theorem differentiable_sineIntegral : Differentiable ℝ sineIntegral :=
  fun x ↦ (hasDerivAt_sineIntegral x).differentiableAt

@[continuity, fun_prop]
theorem continuous_sineIntegral : Continuous sineIntegral :=
  differentiable_sineIntegral.continuous

@[simp]
theorem sineIntegral_zero : sineIntegral 0 = 0 := by
  simp [sineIntegral]

@[simp]
theorem sineIntegral_neg (x : ℝ) : sineIntegral (-x) = -sineIntegral x := by
  have H := integral_comp_neg (f := sinc) (a := 0) (b := x)
  simp only [sinc_neg, neg_zero] at H
  rw [sineIntegral, sineIntegral, integral_symm, ← H]

theorem odd_sineIntegral : Function.Odd sineIntegral :=
  sineIntegral_neg

/-- The integral of `sinc` over any oriented interval is a difference of sine integrals. -/
theorem integral_sinc_eq_sub (a b : ℝ) :
    ∫ t in a..b, sinc t = sineIntegral b - sineIntegral a :=
  (integral_interval_sub_left (continuous_sinc.intervalIntegrable 0 b)
    (continuous_sinc.intervalIntegrable 0 a)).symm

/-- The integral of `sin t / t` over any oriented interval is a difference of sine integrals. -/
theorem integral_sin_div_eq_sub (a b : ℝ) :
    ∫ t in a..b, sin t / t = sineIntegral b - sineIntegral a := by
  rw [← integral_sinc_eq_sub]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2 (MeasureTheory.measure_singleton (0 : ℝ))]
    with t ht _
  exact (sinc_of_ne_zero (by simpa using ht)).symm

theorem sineIntegral_eq_integral_sin_div (x : ℝ) :
    sineIntegral x = ∫ t in (0 : ℝ)..x, sin t / t := by
  simp [integral_sin_div_eq_sub]

/-- `Si x → -π / 2` as `x → -∞`, by oddness from the Dirichlet integral
`TauCeti.Contour.tendsto_integral_sinc_atTop`, which states `Si x → π / 2` as `x → ∞`. -/
theorem tendsto_sineIntegral_atBot : Tendsto sineIntegral atBot (𝓝 (-(π / 2))) := by
  have h : Tendsto sineIntegral atTop (𝓝 (π / 2)) := TauCeti.Contour.tendsto_integral_sinc_atTop
  simpa [Function.comp_def] using (h.comp tendsto_neg_atBot_atTop).neg

/-! ### The comparison functions on `(0, ∞)` -/

/-- For `x ≠ 0`, the derivative of `Si x + (cos x + c) / x` is `-(cos x + c) / x²`. -/
private theorem hasDerivAt_sineIntegral_add_div (c : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y ↦ sineIntegral y + (cos y + c) / y) (-(cos x + c) / x ^ 2) x := by
  convert (hasDerivAt_sineIntegral x).add
    (((hasDerivAt_cos x).add_const c).div (hasDerivAt_id' x) hx) using 1
  rw [sinc_of_ne_zero hx]
  field_simp
  ring

private theorem continuousOn_sineIntegral_add_div (c : ℝ) :
    ContinuousOn (fun y ↦ sineIntegral y + (cos y + c) / y) (Ioi 0) := fun _ hy ↦
  (hasDerivAt_sineIntegral_add_div c (ne_of_gt hy)).continuousAt.continuousWithinAt

/-- `Si x + (cos x - 1) / x` is monotone on `(0, ∞)`. -/
private theorem monotoneOn_sineIntegral_add_cos_sub_one_div :
    MonotoneOn (fun y ↦ sineIntegral y + (cos y + -1) / y) (Ioi 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x ↦ -(cos x + -1) / x ^ 2) (convex_Ioi 0)
    (continuousOn_sineIntegral_add_div (-1)) (fun x hx ↦ ?_) fun x _ ↦ ?_
  · rw [interior_Ioi] at hx
    exact (hasDerivAt_sineIntegral_add_div (-1) (ne_of_gt hx)).hasDerivWithinAt
  · exact div_nonneg (by linarith [cos_le_one x]) (sq_nonneg x)

/-- `Si x + (cos x + 1) / x` is antitone on `(0, ∞)`. -/
private theorem antitoneOn_sineIntegral_add_cos_add_one_div :
    AntitoneOn (fun y ↦ sineIntegral y + (cos y + 1) / y) (Ioi 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x ↦ -(cos x + 1) / x ^ 2) (convex_Ioi 0)
    (continuousOn_sineIntegral_add_div 1) (fun x hx ↦ ?_) fun x _ ↦ ?_
  · rw [interior_Ioi] at hx
    exact (hasDerivAt_sineIntegral_add_div 1 (ne_of_gt hx)).hasDerivWithinAt
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith [neg_one_le_cos x]) (sq_nonneg x)

private theorem tendsto_sineIntegral_add_div (c : ℝ) :
    Tendsto (fun y ↦ sineIntegral y + (cos y + c) / y) atTop (𝓝 (π / 2)) := by
  have hzero : Tendsto (fun y ↦ (cos y + c) / y) atTop (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (b := -1 + c) (B := 1 + c)
      (.of_forall fun y ↦ by linarith [neg_one_le_cos y])
      (.of_forall fun y ↦ by linarith [cos_le_one y]) tendsto_id
  have hSi : Tendsto sineIntegral atTop (𝓝 (π / 2)) := TauCeti.Contour.tendsto_integral_sinc_atTop
  simpa using hSi.add hzero

/-! ### The tail bounds -/

/-- Between two positive points `x ≤ R` the sine integral moves by at most `2 / x`. -/
theorem abs_sineIntegral_sub_le {x R : ℝ} (hx : 0 < x) (hxR : x ≤ R) :
    |sineIntegral R - sineIntegral x| ≤ 2 / x := by
  have hR : 0 < R := hx.trans_le hxR
  have h₁ := monotoneOn_sineIntegral_add_cos_sub_one_div hx hR hxR
  have h₂ := antitoneOn_sineIntegral_add_cos_add_one_div hx hR hxR
  simp only at h₁ h₂
  have hx₁ : -2 / x ≤ (cos x + -1) / x := by
    gcongr
    linarith [neg_one_le_cos x]
  have hx₂ : (cos x + 1) / x ≤ 2 / x := by
    gcongr
    linarith [cos_le_one x]
  have hR₁ : (cos R + -1) / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by linarith [cos_le_one R]) hR.le
  have hR₂ : 0 ≤ (cos R + 1) / R := div_nonneg (by linarith [neg_one_le_cos R]) hR.le
  rw [abs_le, neg_div']
  constructor <;> linarith

/-- The lower half of the sharp tail bound: `(cos x - 1) / x ≤ π / 2 - Si x` for `x > 0`. -/
theorem cos_sub_one_div_le_pi_div_two_sub_sineIntegral {x : ℝ} (hx : 0 < x) :
    (cos x - 1) / x ≤ π / 2 - sineIntegral x := by
  have h := ge_of_tendsto (tendsto_sineIntegral_add_div (-1)) <|
    (eventually_ge_atTop x).mono fun R hR ↦
      monotoneOn_sineIntegral_add_cos_sub_one_div hx (hx.trans_le hR) hR
  simp only [← sub_eq_add_neg] at h
  linarith

/-- The upper half of the sharp tail bound: `π / 2 - Si x ≤ (1 + cos x) / x` for `x > 0`. -/
theorem pi_div_two_sub_sineIntegral_le_one_add_cos_div {x : ℝ} (hx : 0 < x) :
    π / 2 - sineIntegral x ≤ (1 + cos x) / x := by
  have h := le_of_tendsto (tendsto_sineIntegral_add_div 1) <|
    (eventually_ge_atTop x).mono fun R hR ↦
      antitoneOn_sineIntegral_add_cos_add_one_div hx (hx.trans_le hR) hR
  simp only at h
  rw [add_comm (cos x) 1] at h
  linarith

/-- **Tail bound for the sine integral**: `|π / 2 - Si x| ≤ 2 / x` for `x > 0`. -/
theorem abs_pi_div_two_sub_sineIntegral_le {x : ℝ} (hx : 0 < x) :
    |π / 2 - sineIntegral x| ≤ 2 / x := by
  have h₁ := cos_sub_one_div_le_pi_div_two_sub_sineIntegral hx
  have h₂ := pi_div_two_sub_sineIntegral_le_one_add_cos_div hx
  have hx₁ : -2 / x ≤ (cos x - 1) / x := by
    gcongr
    linarith [neg_one_le_cos x]
  have hx₂ : (1 + cos x) / x ≤ 2 / x := by
    gcongr
    linarith [cos_le_one x]
  rw [abs_le, neg_div']
  constructor <;> linarith

/-! ### The global maximum -/

theorem sineIntegral_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ sineIntegral x := by
  rcases le_or_gt x π with hxπ | hπx
  · exact integral_nonneg hx fun t ht ↦
      sinc_nonneg (abs_le.2 ⟨by linarith [pi_pos, ht.1], ht.2.trans hxπ⟩)
  have hx₀ : 0 < x := pi_pos.trans hπx
  have h := pi_div_two_sub_sineIntegral_le_one_add_cos_div hx₀
  have h₁ : (1 + cos x) / x ≤ 2 / x := by
    gcongr
    linarith [cos_le_one x]
  have h₂ : 2 / x ≤ 2 / π := by gcongr
  have h₃ : 2 / π ≤ π / 2 := by
    rw [div_le_div_iff₀ pi_pos two_pos]
    nlinarith [two_le_pi]
  linarith

theorem sineIntegral_pi_nonneg : 0 ≤ sineIntegral π :=
  sineIntegral_nonneg pi_pos.le

/-- The first maximum `Si π` of the sine integral is its global maximum. -/
theorem sineIntegral_le_sineIntegral_pi (x : ℝ) : sineIntegral x ≤ sineIntegral π := by
  rcases lt_or_ge x 0 with hx | hx
  · have := sineIntegral_nonneg (neg_nonneg.2 hx.le)
    rw [sineIntegral_neg] at this
    linarith [sineIntegral_pi_nonneg]
  rcases le_or_gt x π with hxπ | hπx
  · rw [← sub_nonneg, ← integral_sinc_eq_sub]
    exact integral_nonneg hxπ fun t ht ↦
      sinc_nonneg (abs_le.2 ⟨by linarith [pi_pos, ht.1], ht.2⟩)
  have hx₀ : 0 < x := pi_pos.trans hπx
  have h := antitoneOn_sineIntegral_add_cos_add_one_div pi_pos hx₀ hπx.le
  have hx₁ : 0 ≤ (cos x + 1) / x := div_nonneg (by linarith [neg_one_le_cos x]) hx₀.le
  simp only [cos_pi, neg_add_cancel, zero_div, add_zero] at h
  linarith

/-- **The sine integral is bounded by its first maximum**: `|Si x| ≤ Si π` for every real `x`. -/
theorem abs_sineIntegral_le (x : ℝ) : |sineIntegral x| ≤ sineIntegral π := by
  refine abs_le.2 ⟨?_, sineIntegral_le_sineIntegral_pi x⟩
  have := sineIntegral_le_sineIntegral_pi (-x)
  rw [sineIntegral_neg] at this
  linarith

/-! ### The truncated Dirichlet integral -/

/-- The truncated Dirichlet integral at frequency `T` is a difference of sine integrals. -/
theorem integral_sin_mul_div_eq_sub (T a b : ℝ) :
    ∫ v in a..b, sin (T * v) / v = sineIntegral (T * b) - sineIntegral (T * a) := by
  have h (v : ℝ) : sin (T * v) / v = T * (sin (T * v) / (T * v)) := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    rcases eq_or_ne T 0 with rfl | hT
    · simp
    field_simp
  have hsub := smul_integral_comp_mul_left (f := fun u ↦ sin u / u) (a := a) (b := b) T
  simp only [smul_eq_mul] at hsub
  simp_rw [h]
  rw [integral_const_mul, hsub, integral_sin_div_eq_sub]

/-- **Uniform bound for the truncated Dirichlet integral**: for all real `a`, `b` and `T`,
`|∫_a^b sin (T v) / v dv| ≤ 2 Si π`. -/
theorem abs_integral_sin_mul_div_le (T a b : ℝ) :
    |∫ v in a..b, sin (T * v) / v| ≤ 2 * sineIntegral π := by
  rw [integral_sin_mul_div_eq_sub]
  have h₁ := abs_le.1 (abs_sineIntegral_le (T * b))
  have h₂ := abs_le.1 (abs_sineIntegral_le (T * a))
  exact abs_le.2 ⟨by linarith [h₁.1, h₂.2], by linarith [h₁.2, h₂.1]⟩

end Real
