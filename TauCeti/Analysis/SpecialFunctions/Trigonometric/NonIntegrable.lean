/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Group.Integral

/-!
# Non-integrability of `cos t / t` at infinity

The function `t ↦ cos t / t` has a convergent improper integral on `(a, ∞)` for `a > 0`, but it is
not Lebesgue integrable there. Translating by `π / 2` exchanges `|cos|` and `|sin|` up to a bounded
factor, and `1 ≤ |cos t| + |sin t|`, so integrability would contradict that of `t⁻¹`
(`not_integrableOn_Ioi_inv`). Oscillatory amplitudes such as `sin t / t` therefore have derivatives
that are not integrable at infinity.

## Main results

* `TauCeti.not_integrableOn_Ioi_cos_div`: `cos t / t` is not integrable on `(a, ∞)`.
-/

public section

open Filter MeasureTheory Set
open scoped Real

namespace TauCeti

/-- `cos t / t` is not absolutely integrable on `(a, ∞)` for `a > 0`. -/
theorem not_integrableOn_Ioi_cos_div {a : ℝ} (ha : 0 < a) :
    ¬ IntegrableOn (fun t : ℝ => Real.cos t / t) (Ioi a) := by
  intro hcos
  have hpi := Real.pi_pos
  have hshift : IntegrableOn (fun t : ℝ => Real.cos (t + π / 2) / (t + π / 2)) (Ioi a) := by
    have hind := ((integrable_indicator_iff measurableSet_Ioi).2 hcos).comp_add_right (π / 2)
    refine hind.integrableOn.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht1 : a < t := ht
    have hmem : t + π / 2 ∈ Ioi a := by
      simp only [Set.mem_Ioi]
      linarith
    simp [Set.indicator_of_mem hmem]
  have hsin : IntegrableOn (fun t : ℝ => |Real.sin t| / t) (Ioi a) := by
    refine Integrable.mono' (hshift.norm.const_mul (1 + π / (2 * a))) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      exact ((Real.continuous_sin.abs.continuousAt).div continuousAt_id
        (ha.trans ht).ne').continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht1 : a < t := ht
      have ht0 : 0 < t := ha.trans ht1
      have htp : 0 < t + π / 2 := by positivity
      have hC : t + π / 2 ≤ (1 + π / (2 * a)) * t := by
        have : π / 2 ≤ π / (2 * a) * t := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ two_pos (by positivity)]
          nlinarith
        linarith
      rw [Real.cos_add_pi_div_two, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div, abs_neg,
        abs_abs, abs_of_pos ht0, abs_of_pos htp, ← mul_div_assoc, mul_comm (1 + π / (2 * a)),
        mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [inv_eq_one_div, div_le_div_iff₀ ht0 htp]
      linarith
  refine not_integrableOn_Ioi_inv (a := a) ?_
  refine Integrable.mono' (hcos.norm.add hsin) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact (continuousAt_inv₀ (ha.trans ht).ne').continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ha.trans ht
    have hone : 1 ≤ |Real.cos t| + |Real.sin t| := by
      have hc : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
      have hs : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
      nlinarith [Real.sin_sq_add_cos_sq t, abs_nonneg (Real.cos t), abs_nonneg (Real.sin t),
        sq_abs (Real.cos t), sq_abs (Real.sin t)]
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_div, abs_of_pos ht0, abs_inv]
    rw [← add_div, inv_eq_one_div]
    exact div_le_div_of_nonneg_right hone ht0.le

end TauCeti
