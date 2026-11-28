/-
Copyright (c) 2026 Tau Ceti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complex cone inequalities and Laplace-method Bochner integral lower bounds

This file collects the complex cone bounds, covering-error absorption inequality, and abstract
Bochner-integral cone lower bound used in Laplace's method for periods of discrete series
coefficients:

* `TauCeti.norm_mul_sub_mul_le`: if `a, c, t ∈ [0, 1]` and `u, v ∈ ℂ` lie within `a / 10 + t` and
  `c / 10 + t` of `a` and `c`, then `u * v` lies within `0.21 * (a * c) + 4 * t` of `a * c`.
* `TauCeti.norm_le_two_mul_re_add`: a complex number within `0.21 * p + 4 * t` of a nonnegative
  real `p` lies in the cone `‖z‖ ≤ 2 * z.re + 12 * t`.
* `TauCeti.le_pow_mul_of_le`: covering-error absorption for Laplace's method
  (`V ≤ β ^ (20 * N) * I`).
* `TauCeti.setIntegral_re_le_norm_integral_add`: if an integrable `f : α → ℂ` satisfies
  `‖f x‖ ≤ C * (f x).re + g x` with `0 < C` and `g` integrable, then for any measurable `s`,
  `∫ x in s, (f x).re ∂μ ≤ ‖∫ x, f x ∂μ‖ + C⁻¹ * ∫ x in sᶜ, g x ∂μ`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/New/Appendix/DiscreteSeries/Periods.lean`,
declarations `New.DiscreteSeries.norm_mul_sub_mul_le`, `New.DiscreteSeries.norm_le_two_mul_re_add`,
`New.DiscreteSeries.le_pow_mul_of_le`, and the cone-integral step of
`New.DiscreteSeries.IsLaplaceDatum.laplace_method`.
-/

@[expose] public section

namespace TauCeti

open MeasureTheory Complex

/-- Let `a, c, t ∈ [0, 1]`. If `u` is within `a / 10 + t` of `a` and `v` is within `c / 10 + t` of
`c`, then `u * v` is within `0.21 * (a * c) + 4 * t` of `a * c`. -/
theorem norm_mul_sub_mul_le {a c t : ℝ} {u v : ℂ} (ha : a ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1)
    (ht : t ∈ Set.Icc 0 1) (hu : ‖u - a‖ ≤ a / 10 + t) (hv : ‖v - c‖ ≤ c / 10 + t) :
    ‖u * v - ↑(a * c)‖ ≤ 0.21 * (a * c) + 4 * t := by
  calc ‖u * v - ↑(a * c)‖
      = ‖a * (v - c) + (u - a) * c + (u - a) * (v - c)‖ := by rw [ofReal_mul]; ring_nf
    _ ≤ ‖a * (v - c)‖ + ‖(u - a) * c‖ + ‖(u - a) * (v - c)‖ := norm_add₃_le
    _ ≤ a * (c / 10 + t) + (a / 10 + t) * c + (a / 10 + t) * (c / 10 + t) := by
        simp only [norm_mul, Complex.norm_of_nonneg ha.left, Complex.norm_of_nonneg hc.left]
        gcongr <;> linarith [ha.left, hc.left, ht.left]
    _ ≤ 0.21 * (a * c) + 4 * t := by
        nlinarith [ha.left, hc.left, ht.left, ha.right, hc.right, ht.right]

/-- A complex number `z` within `0.21 * p + 4 * t` of a nonnegative real `p` lies in the cone
`‖z‖ ≤ 2 * z.re + 12 * t`. -/
theorem norm_le_two_mul_re_add {p t : ℝ} {z : ℂ} (hp : 0 ≤ p)
    (hz : ‖z - p‖ ≤ 0.21 * p + 4 * t) : ‖z‖ ≤ 2 * z.re + 12 * t := by
  have h_norm : ‖z‖ ≤ p + ‖z - p‖ := by
    simpa [abs_of_nonneg hp] using norm_le_insert' z p
  have h_re : -‖z - p‖ ≤ z.re - p := by simpa using neg_le_of_abs_le (abs_re_le_norm (z - p))
  linarith

/-- Covering-error absorption for Laplace's method: if `β ≥ 16`, `N ≥ 1`, `V, I ≥ 0`,
`V ≤ β ^ (16 * N) * W`, and `W / 4 ≤ 2 * I + 6 * β⁻¹ ^ (50 * N) * (16 ^ (9 * N) * V)`, then
`V ≤ β ^ (20 * N) * I`. -/
theorem le_pow_mul_of_le {β : ℝ} {N : ℕ} {V W I : ℝ} (hβ : 16 ≤ β) (hN : 1 ≤ N) (hV : 0 ≤ V)
    (hI : 0 ≤ I) (h_cover : V ≤ β ^ (16 * N) * W)
    (h_int : W / 4 ≤ 2 * I + 6 * β⁻¹ ^ (50 * N) * (16 ^ (9 * N) * V)) :
    V ≤ β ^ (20 * N) * I := by
  have hβ_one : 1 ≤ β := by linarith
  have h_main : 16 * β ^ (16 * N) ≤ β ^ (20 * N) :=
    calc 16 * β ^ (16 * N) ≤ β * β ^ (16 * N) := by gcongr
      _ ≤ β ^ (20 * N) := by
          rw [← pow_succ']
          exact pow_le_pow_right₀ hβ_one (by omega)
  have h_error : 48 * β ^ (16 * N) * 16 ^ (9 * N) ≤ β ^ (50 * N) :=
    calc 48 * β ^ (16 * N) * 16 ^ (9 * N) ≤ β ^ 2 * β ^ (16 * N) * β ^ (9 * N) := by
          gcongr; nlinarith
      _ ≤ β ^ (50 * N) := by
          rw [← pow_add, ← pow_add]
          exact pow_le_pow_right₀ hβ_one (by omega)
  have h_half : β ^ (16 * N) * (24 * β⁻¹ ^ (50 * N) * 16 ^ (9 * N)) ≤ 1 / 2 := by
    rw [inv_pow]
    field_simp
    linarith
  have h_combined : V ≤ 8 * β ^ (16 * N) * I + 1 / 2 * V :=
    calc V ≤ β ^ (16 * N) * (8 * I + 24 * β⁻¹ ^ (50 * N) * 16 ^ (9 * N) * V) := by
          refine h_cover.trans ?_; gcongr; linarith
      _ = 8 * β ^ (16 * N) * I + β ^ (16 * N) * (24 * β⁻¹ ^ (50 * N) * 16 ^ (9 * N)) * V := by ring
      _ ≤ 8 * β ^ (16 * N) * I + 1 / 2 * V := by gcongr
  linarith [mul_le_mul_of_nonneg_right h_main hI]

/-- Abstract cone lower bound for a Bochner integral: if `f : α → ℂ` and `g : α → ℝ` are integrable
and `‖f x‖ ≤ C * (f x).re + g x` everywhere (with `0 < C`), then for any measurable set `s`,
`∫ x in s, (f x).re ∂μ ≤ ‖∫ x, f x ∂μ‖ + C⁻¹ * ∫ x in sᶜ, g x ∂μ`. -/
theorem setIntegral_re_le_norm_integral_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} {g : α → ℝ} {C : ℝ} {s : Set α} (hC : 0 < C) (hs : MeasurableSet s)
    (hf : Integrable f μ) (hg : Integrable g μ) (h_cone : ∀ x, ‖f x‖ ≤ C * (f x).re + g x) :
    ∫ x in s, (f x).re ∂μ ≤ ‖∫ x, f x ∂μ‖ + C⁻¹ * ∫ x in sᶜ, g x ∂μ := by
  have hf_re : Integrable (fun x ↦ (f x).re) μ := Complex.reCLM.integrable_comp hf
  have h_total : ∫ x, (f x).re ∂μ ≤ ‖∫ x, f x ∂μ‖ := by
    have h_eq : ∫ x, (f x).re ∂μ = (∫ x, f x ∂μ).re := Complex.reCLM.integral_comp_comm hf
    rw [h_eq]
    exact Complex.re_le_norm _
  have h_split : (∫ x in s, (f x).re ∂μ) + ∫ x in sᶜ, (f x).re ∂μ = ∫ x, (f x).re ∂μ :=
    integral_add_compl hs hf_re
  have h_neg : -(C⁻¹ * ∫ x in sᶜ, g x ∂μ) ≤ ∫ x in sᶜ, (f x).re ∂μ := by
    rw [← integral_const_mul, ← integral_neg]
    refine integral_mono ((hg.integrableOn.const_mul C⁻¹).neg) hf_re.integrableOn fun x ↦ ?_
    have h0 : 0 ≤ C * (f x).re + g x := (norm_nonneg (f x)).trans (h_cone x)
    have h1 : -g x ≤ C * (f x).re := by linarith
    have h2 : C⁻¹ * (-g x) ≤ C⁻¹ * (C * (f x).re) :=
      mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hC.le)
    rw [inv_mul_cancel_left₀ hC.ne'] at h2
    linarith
  linarith

end TauCeti
