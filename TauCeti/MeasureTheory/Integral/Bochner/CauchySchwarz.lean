/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Cauchy–Schwarz inequality for real integrals

For square-integrable real functions `f` and `g`,

`(∫ f g)² ≤ (∫ f²) (∫ g²)`

(`TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq`). Mathlib states Hölder's inequality
for real integrals with real exponents and roots
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`); this is the squared form for `p = q = 2`,
without roots or sign conditions, as it is used in energy estimates.

A weighted variant for nonnegative `a`, `d` and positive `g` gives
`(∫ a √d)² ≤ (∫ a (d / g)) (∫ a g)` (`TauCeti.sq_integral_mul_sqrt_le_integral_mul_div_mul`).
-/

public section

namespace TauCeti

open MeasureTheory

/-- **The Cauchy–Schwarz inequality** `(∫ f g)² ≤ (∫ f²) (∫ g²)` for square-integrable real
functions. -/
theorem sq_integral_mul_le_integral_sq_mul_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x))
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (g x))
    (by simpa [Real.norm_eq_abs] using hf.norm) (by simpa [Real.norm_eq_abs] using hg.norm)
  have hF : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x ↦ sq_nonneg _
  have hG : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x ↦ sq_nonneg _
  simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at h
  calc (∫ x, f x * g x ∂μ) ^ 2 = |∫ x, f x * g x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ x, |f x| * |g x| ∂μ) ^ 2 := by
        gcongr
        calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := abs_integral_le_integral_abs
          _ = ∫ x, |f x| * |g x| ∂μ := by simp_rw [abs_mul]
    _ ≤ (√(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ)) ^ 2 :=
        pow_le_pow_left₀ (integral_nonneg fun x ↦ by positivity) h 2
    _ = (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
        rw [mul_pow, Real.sq_sqrt hF, Real.sq_sqrt hG]

/-- **Weighted Cauchy–Schwarz inequality** `(∫ a √d)² ≤ (∫ a (d / g)) (∫ a g)` for almost
everywhere nonnegative weights `a` and `d` and almost everywhere positive `g`. -/
theorem sq_integral_mul_sqrt_le_integral_mul_div_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {a d g : α → ℝ} (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (hd : ∀ᵐ x ∂μ, 0 ≤ d x)
    (hg : ∀ᵐ x ∂μ, 0 < g x) (hadg : Integrable (fun x ↦ a x * (d x / g x)) μ)
    (hag : Integrable (fun x ↦ a x * g x) μ) :
    (∫ x, a x * √(d x) ∂μ) ^ 2 ≤ (∫ x, a x * (d x / g x) ∂μ) * ∫ x, a x * g x ∂μ := by
  have hmem1 : MemLp (fun x ↦ √(a x * (d x / g x))) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hadg.aestronglyMeasurable)).2 <|
      hadg.congr <| by
        filter_upwards [ha, hd, hg] with x hxa hxd hxg
        exact (Real.sq_sqrt (mul_nonneg hxa (div_nonneg hxd hxg.le))).symm
  have hmem2 : MemLp (fun x ↦ √(a x * g x)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hag.aestronglyMeasurable)).2 <|
      hag.congr <| by
        filter_upwards [ha, hg] with x hxa hxg
        exact (Real.sq_sqrt (mul_nonneg hxa hxg.le)).symm
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq hmem1 hmem2
  have hprod : (fun x ↦ √(a x * (d x / g x)) * √(a x * g x)) =ᵐ[μ] fun x ↦ a x * √(d x) := by
    filter_upwards [ha, hd, hg] with x hxa hxd hxg
    have hmul : a x * (d x / g x) * (a x * g x) = a x ^ 2 * d x := by
      calc a x * (d x / g x) * (a x * g x) = a x ^ 2 * d x * (g x / g x) := by ring
        _ = a x ^ 2 * d x := by rw [div_self hxg.ne', mul_one]
    rw [← Real.sqrt_mul (mul_nonneg hxa (div_nonneg hxd hxg.le)), hmul,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hxa]
  have hsq1 : (fun x ↦ √(a x * (d x / g x)) ^ 2) =ᵐ[μ] fun x ↦ a x * (d x / g x) := by
    filter_upwards [ha, hd, hg] with x hxa hxd hxg
    exact Real.sq_sqrt (mul_nonneg hxa (div_nonneg hxd hxg.le))
  have hsq2 : (fun x ↦ √(a x * g x) ^ 2) =ᵐ[μ] fun x ↦ a x * g x := by
    filter_upwards [ha, hg] with x hxa hxg
    exact Real.sq_sqrt (mul_nonneg hxa hxg.le)
  rwa [integral_congr_ae hprod, integral_congr_ae hsq1, integral_congr_ae hsq2] at hcs

end TauCeti
