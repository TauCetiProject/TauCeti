/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Group.Integral
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Non-integrability of `cos t / t` at infinity

The function `t ↦ cos t / t` has a convergent improper integral on `(a, ∞)` for `a > 0`, but it is
not Lebesgue integrable there. Translating by `π / 2` exchanges `|cos|` and `|sin|` up to a bounded
factor, and `1 ≤ |cos t| + |sin t|`, so integrability would contradict that of `t⁻¹`
(`not_integrableOn_Ioi_inv`). Oscillatory amplitudes such as `sin t / t` therefore have derivatives
that are not integrable at infinity: the derivative `cos t / t - sin t / t²` of `sinc` differs from
`cos t / t` by an integrable function.

## Main results

* `TauCeti.not_integrableOn_Ioi_cos_div`: `cos t / t` is not integrable on `(a, ∞)`.
* `TauCeti.not_integrableOn_Ioi_deriv_sinc`: the derivative of `sinc` is not integrable on
  `(a, ∞)`.
-/

public section

open Filter MeasureTheory Set
open scoped Real Topology

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
      simp only [Real.cos_add_pi_div_two, norm_div, norm_neg, Real.norm_eq_abs, abs_abs,
        abs_of_pos ht0, abs_of_pos htp]
      rw [mul_div_assoc', div_le_div_iff₀ ht0 htp]
      nlinarith [abs_nonneg (Real.sin t)]
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

/-- For `0 < a`, the derivative `cos t / t - sin t / t²` of `sinc` is not integrable on `(a, ∞)`,
although `sinc` tends to zero there. -/
theorem not_integrableOn_Ioi_deriv_sinc {a : ℝ} (ha : 0 < a) :
    ¬ IntegrableOn (deriv Real.sinc) (Ioi a) := by
  intro h
  have hd : IntegrableOn (fun t : ℝ => Real.cos t / t - Real.sin t / t ^ 2) (Ioi a) :=
    h.congr_fun (fun t ht => (Real.hasDerivAt_sinc_of_ne_zero (ha.trans ht).ne').deriv)
      measurableSet_Ioi
  have hsq : IntegrableOn (fun t : ℝ => Real.sin t / t ^ 2) (Ioi a) := by
    refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) ha) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      have ht0 : t ≠ 0 := (ha.trans ht).ne'
      exact (Real.continuous_sin.continuousAt.div (continuousAt_id.pow 2)
        (pow_ne_zero 2 ht0)).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := ha.trans ht
      simpa [abs_div, Real.rpow_neg ht0.le, div_eq_mul_inv] using
        mul_le_of_le_one_left (by positivity : (0 : ℝ) ≤ (t ^ 2)⁻¹) (Real.abs_sin_le_one t)
  refine not_integrableOn_Ioi_cos_div ha ((hd.add hsq).congr_fun (fun t _ => ?_)
    measurableSet_Ioi)
  simp

end TauCeti
