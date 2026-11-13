/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The first-order Perron integral

The kernel `x^s / (s(s+1))` is absolutely integrable on each vertical line avoiding the two
poles. On a line `Re s = c > 0` its normalized integral is `max (1 - 1/x) 0`, for `x > 0`.
Unlike the sharp Perron kernel `x^s/s`, the first-order weight is continuous at the cutoff
`x = 1`, where its value is zero.

This is the kernel for sums smoothed by `1 - n/x`. For `d = min |c| |c + 1| > 0`, the vertical
integrand has modulus at most `x^c / (d² + t²)`. This integrable Cauchy majorant applies on
both positive and negative lines away from the poles.

## Main results

* `TauCeti.integrable_cpow_div_mul_add_one`: absolute convergence for `c ≠ 0, -1`.
* `TauCeti.integral_cpow_div_mul_add_one`: the normalized integral on `c > 0`.

## Provenance

The migration motivating this formula is the Prime Number Theorem and more project by
Alex Kontorovich, Terence Tao and contributors, `PrimeNumberTheoremAnd/PerronFormula.lean`
(`Perron.formulaLtOne`, `Perron.formulaGtOne`). The proof here is independent of its contour
argument: it composes Mathlib's interval-power Mellin transforms and Mellin inversion.
-/

public section

open Complex Real Set MeasureTheory

namespace TauCeti

private noncomputable def weight (t : ℝ) : ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℂ)) t -
    (Ioc (0 : ℝ) 1).indicator (fun u ↦ (u : ℂ) ^ (1 : ℂ)) t

private lemma weight_eq {t : ℝ} (ht : 0 < t) : weight t = (max (1 - t) 0 : ℝ) := by
  unfold weight
  by_cases h : t ≤ 1
  · simp [ht, h]
  · have ht1 : 1 - t ≤ 0 := by linarith
    simp [h, max_eq_right ht1]

private lemma hasMellin_weight {s : ℂ} (hs : 0 < s.re) :
    HasMellin weight s ((s * (s + 1))⁻¹) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc (1 : ℂ) (by simpa using (by linarith : 0 < s.re + 1))
  have hh := hasMellin_sub h0.1 h1.1
  rw [h0.2, h1.2] at hh
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  refine ⟨hh.1, hh.2.trans ?_⟩
  field_simp [hs0, hs1]
  ring

private lemma verticalIntegrable_riesz {c : ℝ} (hc : c ≠ 0) (hc1 : c ≠ -1) :
    VerticalIntegrable (fun s : ℂ ↦ (s * (s + 1))⁻¹) c := by
  let d := min |c| |c + 1|
  have h1 : c + 1 ≠ 0 := by simpa using sub_ne_zero.mpr hc1
  have hd : 0 < d := lt_min (abs_pos.mpr hc) (abs_pos.mpr h1)
  have hmajor : Integrable (fun t : ℝ ↦ (d ^ 2 + t ^ 2)⁻¹) := by
    have h := (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hd.ne')).const_mul (d^2)⁻¹
    convert h using 1
    ext t
    field_simp
  refine hmajor.mono' (by fun_prop) (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [norm_inv, norm_mul]
  have hsq0 : ‖(c : ℂ) + t * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hsq1 : ‖(c : ℂ) + t * I + 1‖ ^ 2 = (c + 1) ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hdc : d ^ 2 ≤ c ^ 2 := by
    have h := min_le_left |c| |c + 1|
    nlinarith [sq_abs c]
  have hdc1 : d ^ 2 ≤ (c + 1) ^ 2 := by
    have h := min_le_right |c| |c + 1|
    nlinarith [sq_abs (c + 1)]
  apply inv_anti₀ (by positivity)
  by_cases hle : ‖(c : ℂ) + t * I‖ ≤ ‖(c : ℂ) + t * I + 1‖
  · calc d ^ 2 + t ^ 2 ≤ ‖(c : ℂ) + t * I‖ ^ 2 := by linarith
         _ ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖ := by
           simpa only [sq] using mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  · calc d ^ 2 + t ^ 2 ≤ ‖(c : ℂ) + t * I + 1‖ ^ 2 := by linarith
         _ ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖ := by
           simpa only [sq] using mul_le_mul_of_nonneg_right (not_le.mp hle).le (norm_nonneg _)

/-- The inverse Mellin transform of `1 / (s(s+1))` is the continuous first-order Perron weight. -/
private theorem mellinInv_inv_mul_add_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    mellinInv c (fun s : ℂ ↦ (s * (s + 1))⁻¹) x = (max (1 - x) 0 : ℝ) := by
  have hm (t : ℝ) : mellin weight ((c : ℂ) + t * I) =
      ((((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))⁻¹) :=
    (hasMellin_weight (by simpa using hc)).2
  have hv : VerticalIntegrable (mellin weight) c := by
    simpa only [VerticalIntegrable, hm] using verticalIntegrable_riesz hc.ne' (by linarith)
  have hwc : ContinuousAt weight x := by
    have hnear : weight =ᶠ[nhds x] (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ)) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx) fun u hu ↦ weight_eq hu
    exact (by fun_prop : ContinuousAt (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ)) x).congr hnear.symm
  have h := mellinInv_mellin_eq c weight hx (hasMellin_weight (by simpa using hc)).1 hv hwc
  rw [mellinInv] at h ⊢
  simpa only [hm, weight_eq hx] using h

private lemma riesz_integrand_eq {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ (-s) • (s * (s + 1))⁻¹ = (x : ℂ) ^ s / (s * (s + 1)) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx.le, Complex.cpow_neg, inv_inv]
  rfl

/-- The first-order Perron kernel is absolutely integrable on every line away from
`Re s = 0, -1`. -/
theorem integrable_cpow_div_mul_add_one {c x : ℝ} (hc : c ≠ 0) (hc1 : c ≠ -1) (hx : 0 < x) :
    Integrable (fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) := by
  simpa only [riesz_integrand_eq hx] using
    (verticalIntegrable_riesz hc hc1).integrable_cpow_smul (inv_pos.mpr hx)

/-- The first-order Perron integral has the continuous cutoff weight, including value zero
at `x = 1`. The integration variable is real, so the prefactor is `(2π)⁻¹`. -/
theorem integral_cpow_div_mul_add_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ((2 * π : ℝ) : ℂ)⁻¹ *
      (∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) =
      (max (1 - x⁻¹) 0 : ℝ) := by
  have h := mellinInv_inv_mul_add_one hc (inv_pos.mpr hx)
  simp only [mellinInv, riesz_integrand_eq hx] at h
  simpa only [Complex.real_smul, one_div, Complex.ofReal_inv] using h

end TauCeti
