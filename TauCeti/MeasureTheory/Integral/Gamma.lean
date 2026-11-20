/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Two-sided Gamma integrals on the real line

For `0 < p`, the even function `x ↦ |x| ^ q * exp (-|x| ^ p)` is Lebesgue integrable on `ℝ`
exactly when `-1 < q`, and then its integral is `2 / p * Γ ((q + 1) / p)`.

Mathlib's `integral_rpow_mul_exp_neg_rpow` evaluates the half-line integral; folding the line onto
the positive half-line by `integral_comp_abs` doubles it. Below the threshold the integrand is
comparable to `x ^ q` near the origin, which is not integrable there.

These integrals normalize the generalized normal (exponential power) densities
`exp (-|x| ^ p)` and compute all of their absolute moments.
The scaled case `exp (-b * |x| ^ p)` is also evaluated for `b > 0`.
-/

public section

open MeasureTheory Set

namespace TauCeti

private theorem integrableOn_rpow_of_exp_lower_bound {p q b c : ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hspos : s ⊆ Ioi 0) (hc : 0 < c)
    (hbound : ∀ x ∈ s, c ≤ Real.exp (-b * x ^ p))
    (hint : Integrable (fun x : ℝ => |x| ^ q * Real.exp (-b * |x| ^ p))) :
    IntegrableOn (fun x : ℝ => x ^ q) s := by
  have hscaled : IntegrableOn (fun x : ℝ => c * x ^ q) s := by
    refine Integrable.mono' hint.integrableOn (by fun_prop) ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    have hxpos : 0 < x := hspos hx
    have hxq : 0 ≤ x ^ q := Real.rpow_nonneg hxpos.le q
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le hxq), abs_of_pos hxpos]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hbound x hx) hxq
  simpa only [IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc.ne')]
    using hscaled

/-- **Integrability of the scaled two-sided Gamma integrand.** For `0 < p`, the function
`x ↦ |x| ^ q * exp (-b * |x| ^ p)` is integrable on `ℝ` exactly when `-1 < q` and `0 < b`. -/
theorem integrable_abs_rpow_mul_exp_neg_mul_abs_rpow_iff {p q b : ℝ} (hp : 0 < p) :
    Integrable (fun x : ℝ => |x| ^ q * Real.exp (-b * |x| ^ p)) ↔ -1 < q ∧ 0 < b := by
  refine ⟨fun hint => ?_, fun ⟨hq, hb⟩ => MeasureTheory.integrable_comp_abs
    (f := fun x : ℝ => x ^ q * Real.exp (-b * x ^ p))
    (integrableOn_rpow_mul_exp_neg_mul_rpow hq hp hb)⟩
  have hnear : IntegrableOn (fun x : ℝ => x ^ q) (Ioo 0 1) := by
    refine integrableOn_rpow_of_exp_lower_bound (c := Real.exp (-|b|)) measurableSet_Ioo
      (fun _ hx => hx.1) (Real.exp_pos _) ?_ hint
    intro x hx
    have hxp : x ^ p ≤ 1 := Real.rpow_le_one hx.1.le hx.2.le hp.le
    apply Real.exp_le_exp.mpr
    by_cases hb : 0 ≤ b
    · rw [abs_of_nonneg hb]
      simpa only [mul_one] using mul_le_mul_of_nonpos_left hxp (neg_nonpos.mpr hb)
    · have hb' : b < 0 := lt_of_not_ge hb
      rw [abs_of_neg hb']
      have hnonneg : 0 ≤ -b * x ^ p :=
        mul_nonneg (by linarith) (Real.rpow_nonneg hx.1.le _)
      linarith
  have hq : -1 < q := (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mp hnear
  have hb : 0 < b := by
    by_contra hnot
    have hb' : b ≤ 0 := le_of_not_gt hnot
    have htail : IntegrableOn (fun x : ℝ => x ^ q) (Ioi 1) := by
      refine integrableOn_rpow_of_exp_lower_bound (c := 1) measurableSet_Ioi
        (fun _ hx => lt_trans zero_lt_one hx) zero_lt_one ?_ hint
      intro x hx
      apply Real.one_le_exp_iff.mpr
      exact mul_nonneg (neg_nonneg.mpr hb')
        (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hx)) _)
    have hq' := (integrableOn_Ioi_rpow_iff one_pos).mp htail
    linarith
  exact ⟨hq, hb⟩

/-- The two-sided Gamma integrand with a scaled exponential is integrable for
`0 < p`, `-1 < q`, and `0 < b`. -/
theorem integrable_abs_rpow_mul_exp_neg_mul_abs_rpow {p q b : ℝ}
    (hp : 0 < p) (hq : -1 < q) (hb : 0 < b) :
    Integrable (fun x : ℝ => |x| ^ q * Real.exp (-b * |x| ^ p)) :=
  (integrable_abs_rpow_mul_exp_neg_mul_abs_rpow_iff hp).mpr ⟨hq, hb⟩

/-- The scaled two-sided Gamma integral for `0 < p`, `-1 < q`, and `0 < b`. -/
theorem integral_abs_rpow_mul_exp_neg_mul_abs_rpow {p q b : ℝ}
    (hp : 0 < p) (hq : -1 < q) (hb : 0 < b) :
    ∫ x : ℝ, |x| ^ q * Real.exp (-b * |x| ^ p) =
      2 / p * b ^ (-(q + 1) / p) * Real.Gamma ((q + 1) / p) := by
  rw [integral_comp_abs (f := fun x : ℝ => x ^ q * Real.exp (-b * x ^ p)),
    integral_rpow_mul_exp_neg_mul_rpow hp hq hb]
  ring

/-- **Integrability of the unscaled two-sided Gamma integrand.** For `0 < p`, the function
`x ↦ |x| ^ q * exp (-|x| ^ p)` is integrable on `ℝ` exactly when `-1 < q`. -/
theorem integrable_abs_rpow_mul_exp_neg_abs_rpow_iff {p q : ℝ} (hp : 0 < p) :
    Integrable (fun x : ℝ => |x| ^ q * Real.exp (-|x| ^ p)) ↔ -1 < q := by
  simpa using
    (integrable_abs_rpow_mul_exp_neg_mul_abs_rpow_iff (p := p) (q := q) (b := 1) hp)

/-- The unscaled two-sided Gamma integral for `0 < p` and `-1 < q`. -/
theorem integral_abs_rpow_mul_exp_neg_abs_rpow {p q : ℝ} (hp : 0 < p) (hq : -1 < q) :
    ∫ x : ℝ, |x| ^ q * Real.exp (-|x| ^ p) = 2 / p * Real.Gamma ((q + 1) / p) := by
  simpa using
    (integral_abs_rpow_mul_exp_neg_mul_abs_rpow (p := p) (q := q) (b := 1)
      hp hq one_pos)

/-- The scaled Gaussian Gamma integrand is integrable exactly when `-1 < q` and `0 < b`. -/
theorem integrable_abs_rpow_mul_exp_neg_mul_sq_iff {q b : ℝ} :
    Integrable (fun x : ℝ => |x| ^ q * Real.exp (-b * x ^ 2)) ↔ -1 < q ∧ 0 < b := by
  simpa only [Real.rpow_two, sq_abs] using
    (integrable_abs_rpow_mul_exp_neg_mul_abs_rpow_iff (p := 2) (q := q) (b := b) two_pos)

/-- The two-sided Gamma integrand with a scaled Gaussian exponential is integrable when
`-1 < q` and `0 < b`. -/
theorem integrable_abs_rpow_mul_exp_neg_mul_sq {q b : ℝ} (hq : -1 < q) (hb : 0 < b) :
    Integrable (fun x : ℝ => |x| ^ q * Real.exp (-b * x ^ 2)) :=
  integrable_abs_rpow_mul_exp_neg_mul_sq_iff.mpr ⟨hq, hb⟩

/-- The two-sided Gamma integral with a scaled Gaussian exponential, when `-1 < q` and `0 < b`. -/
theorem integral_abs_rpow_mul_exp_neg_mul_sq {q b : ℝ} (hq : -1 < q) (hb : 0 < b) :
    ∫ x : ℝ, |x| ^ q * Real.exp (-b * x ^ 2) =
      b ^ (-(q + 1) / 2) * Real.Gamma ((q + 1) / 2) := by
  have h := integral_abs_rpow_mul_exp_neg_mul_abs_rpow (p := 2) two_pos hq hb
  simpa only [Real.rpow_two, sq_abs, div_self (by norm_num : (2 : ℝ) ≠ 0),
    one_mul] using h

end TauCeti
