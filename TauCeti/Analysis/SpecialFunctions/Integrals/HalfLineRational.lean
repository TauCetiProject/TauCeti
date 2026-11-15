/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# A rational integral on the half-line

For all real `a` and `c`,

`∫_{y > 0} y² / ((y² + a²) (y² + c²)) dy = π / (2 (|a| + |c|))`,

where for `a = c = 0` the integrand is not integrable and both sides are zero.

The integrand is the product of the two functions `y / (y² + a²)` and `y / (y² + c²)`, and
integrals of this shape arise when two Lorentzian line shapes are paired on the half-line. It
depends on `a` and `c` only through their squares, so one may take `a, c ≥ 0`. For `a ≠ c` partial
fractions then give the antiderivative `(c arctan (y / c) - a arctan (y / a)) / (c² - a²)`, and
for `a = c > 0` the antiderivative is `arctan (y / a) / (2 a) - y / (2 (y² + a²))`. The integrand
is nonnegative, so integrability comes for free from the limits of these antiderivatives at
infinity.

## Main results

* `TauCeti.hasDerivAt_mul_arctan_div`: `a arctan (y / a)` is an antiderivative of
  `a² / (y² + a²)` for every real `a`;
* `TauCeti.tendsto_mul_arctan_div`: `a arctan (y / a)` tends to `|a| π / 2` at infinity;
* `TauCeti.integrableOn_sq_div_sq_add_sq_mul_sq_add_sq_iff`: the integrand is integrable on
  `(0, ∞)` exactly when `a` and `c` are not both zero;
* `TauCeti.integral_Ioi_sq_div_sq_add_sq_mul_sq_add_sq`: the value of the integral.
-/

public section

open Filter MeasureTheory Real Set
open scoped Topology

namespace TauCeti

/-- `a arctan (y / a)` is an antiderivative of `a² / (y² + a²)`, for every real `a`; both sides
vanish when `a = 0`. -/
theorem hasDerivAt_mul_arctan_div (a y : ℝ) :
    HasDerivAt (fun y ↦ a * arctan (y / a)) (a ^ 2 / (y ^ 2 + a ^ 2)) y := by
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using hasDerivAt_const y (0 : ℝ)
  refine (((hasDerivAt_id y).div_const a).arctan.const_mul a).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- For every real `a`, `a arctan (y / a)` tends to `|a| π / 2` as `y → ∞`. -/
theorem tendsto_mul_arctan_div (a : ℝ) :
    Tendsto (fun y ↦ a * arctan (y / a)) atTop (𝓝 (|a| * (π / 2))) := by
  have key (y : ℝ) : a * arctan (y / a) = |a| * arctan (y / |a|) := by
    rcases abs_choice a with h | h <;> simp [h, div_neg, arctan_neg]
  simp_rw [key]
  rcases (abs_nonneg a).eq_or_lt with ha | ha
  · simp [← ha]
  exact ((tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp
    (tendsto_id.atTop_div_const ha)).const_mul |a|

/-- An antiderivative of `y² / ((y² + a²) (y² + c²))` on `[0, ∞)` vanishing at `0`, with limit
`π / (2 (a + c))` at infinity. -/
private theorem exists_antiderivative {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : 0 < a + c) :
    ∃ G : ℝ → ℝ, ContinuousWithinAt G (Ici 0) 0 ∧
      (∀ y ∈ Ioi (0 : ℝ), HasDerivAt G (y ^ 2 / ((y ^ 2 + a ^ 2) * (y ^ 2 + c ^ 2))) y) ∧
      Tendsto G atTop (𝓝 (π / (2 * (a + c)))) ∧ G 0 = 0 := by
  rcases ne_or_eq a c with hne | rfl
  · -- Partial fractions:
    -- `y² / ((y² + a²)(y² + c²)) = (c² / (y² + c²) - a² / (y² + a²)) / (c² - a²)`.
    have hd : c ^ 2 - a ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero (by linarith) (sub_ne_zero.mpr hne.symm)
    refine ⟨fun y ↦ (c * arctan (y / c) - a * arctan (y / a)) / (c ^ 2 - a ^ 2), ?_, fun y hy ↦ ?_,
      ?_, by simp⟩
    · exact Continuous.continuousWithinAt (by fun_prop)
    · have hy : 0 < y := hy
      refine (((hasDerivAt_mul_arctan_div c y).sub (hasDerivAt_mul_arctan_div a y)).div_const
        (c ^ 2 - a ^ 2)).congr_deriv ?_
      have h₁ : y ^ 2 + a ^ 2 ≠ 0 := by positivity
      have h₂ : y ^ 2 + c ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    · convert ((tendsto_mul_arctan_div c).sub (tendsto_mul_arctan_div a)).div_const
        (c ^ 2 - a ^ 2) using 2
      rw [abs_of_nonneg ha, abs_of_nonneg hc, eq_div_iff hd, sq_sub_sq]
      field_simp
      ring
  · -- Equal parameters: `y² / (y² + a²)² = d/dy (arctan (y / a) / (2 a) - y / (2 (y² + a²)))`.
    have ha' : 0 < a := by linarith
    refine ⟨fun y ↦ a * arctan (y / a) / (2 * a ^ 2) - y / (2 * (y ^ 2 + a ^ 2)), ?_,
      fun y _ ↦ ?_, ?_, by simp⟩
    · refine Continuous.continuousWithinAt (Continuous.sub (by fun_prop) ?_)
      exact continuous_id.div (by fun_prop) fun y ↦ by positivity
    · have h₁ : y ^ 2 + a ^ 2 ≠ 0 := by positivity
      have hq : HasDerivAt (fun y : ℝ ↦ 2 * (y ^ 2 + a ^ 2)) (2 * (2 * y)) y := by
        simpa using (((hasDerivAt_id y).pow 2).add_const (a ^ 2)).const_mul 2
      refine (((hasDerivAt_mul_arctan_div a y).div_const (2 * a ^ 2)).sub
        ((hasDerivAt_id y).div hq (by positivity))).congr_deriv ?_
      simp only [id]
      field_simp
      ring
    · have hlim : Tendsto (fun y : ℝ ↦ y / (2 * (y ^ 2 + a ^ 2))) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
          tendsto_inv_atTop_zero ?_ ?_
        · filter_upwards [eventually_ge_atTop 0] with y hy
          positivity
        · filter_upwards [eventually_gt_atTop 0] with y hy
          rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hy]
          nlinarith
      convert ((tendsto_mul_arctan_div a).div_const (2 * a ^ 2)).sub hlim using 2
      rw [abs_of_nonneg ha]
      field_simp
      ring

/-- The function `y² / ((y² + a²) (y² + c²))` is integrable on `(0, ∞)` exactly when `a` and `c`
are not both zero. -/
theorem integrableOn_sq_div_sq_add_sq_mul_sq_add_sq_iff {a c : ℝ} :
    IntegrableOn (fun y : ℝ ↦ y ^ 2 / ((y ^ 2 + a ^ 2) * (y ^ 2 + c ^ 2))) (Ioi 0) ↔
      a ≠ 0 ∨ c ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra! hac
    obtain ⟨rfl, rfl⟩ := hac
    refine not_integrableOn_Ioi_rpow (-2) (h.congr_fun (fun y hy ↦ ?_) measurableSet_Ioi)
    have hy : 0 < y := hy
    rw [rpow_neg hy.le, rpow_two]
    field_simp
    ring
  · have hac : 0 < |a| + |c| := by rcases h with h | h <;> positivity
    obtain ⟨G, hcont, hderiv, hlim, -⟩ := exists_antiderivative (abs_nonneg a) (abs_nonneg c) hac
    simp only [sq_abs] at hderiv
    exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv (fun y _ ↦ by positivity) hlim

/-- For all real `a` and `c`,
`∫_{y > 0} y² / ((y² + a²) (y² + c²)) dy = π / (2 (|a| + |c|))`. When `a = c = 0` the integrand
is not integrable and both sides are zero. -/
theorem integral_Ioi_sq_div_sq_add_sq_mul_sq_add_sq (a c : ℝ) :
    ∫ y in Ioi 0, y ^ 2 / ((y ^ 2 + a ^ 2) * (y ^ 2 + c ^ 2)) = π / (2 * (|a| + |c|)) := by
  by_cases h : a ≠ 0 ∨ c ≠ 0
  · have hac : 0 < |a| + |c| := by rcases h with h | h <;> positivity
    obtain ⟨G, hcont, hderiv, hlim, hG⟩ := exists_antiderivative (abs_nonneg a) (abs_nonneg c) hac
    simp only [sq_abs] at hderiv
    rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv (fun y _ ↦ by positivity) hlim, hG,
      sub_zero]
  · rw [integral_undef (mt integrableOn_sq_div_sq_add_sq_mul_sq_add_sq_iff.mp h)]
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ c = 0 := by simpa using h
    simp

end TauCeti
