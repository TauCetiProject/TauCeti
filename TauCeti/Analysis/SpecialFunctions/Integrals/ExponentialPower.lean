/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Power-weighted exponential differences

For `0 < q < α`, this file proves integrability and evaluates
`∫ x in (0, ∞), x ^ (-(q + 1)) * (1 - exp (-x ^ α))` as `Γ(1 - q / α) / q`.
The cancellation at zero is essential: neither term obtained by expanding the difference
is integrable there. This integral computes fractional absolute moments from characteristic
functions of the form `exp (-|t| ^ α)`.

The evaluation uses integration by parts and Mathlib's Gamma integral
`integral_rpow_mul_exp_neg_rpow`.
-/

public section

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

namespace TauCeti

/-- If `0 < q < α`, the power-weighted exponential difference is integrable on the
positive half-line. The difference cancels the singularity at zero. -/
theorem integrableOn_rpow_neg_mul_one_sub_exp_neg_rpow {α q : ℝ}
    (hq : 0 < q) (hqα : q < α) :
    IntegrableOn (fun x : ℝ ↦ x ^ (-(q + 1)) * (1 - exp (-x ^ α))) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  apply IntegrableOn.union
  · have hp : IntegrableOn (fun x : ℝ ↦ x ^ (α - q - 1)) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by linarith)
    refine hp.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have h0 : 0 ≤ 1 - exp (-x ^ α) :=
      sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr (rpow_nonneg hx.1.le _)))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (rpow_nonneg hx.1.le _) h0)]
    calc
      x ^ (-(q + 1)) * (1 - exp (-x ^ α))
          ≤ x ^ (-(q + 1)) * x ^ α :=
        mul_le_mul_of_nonneg_left (by linarith [one_sub_le_exp_neg (x ^ α)])
          (rpow_nonneg hx.1.le _)
      _ = x ^ (α - q - 1) := by rw [← rpow_add hx.1]; congr 1; ring
  · have hp : IntegrableOn (fun x : ℝ ↦ x ^ (-(q + 1))) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine hp.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have h0 : 0 ≤ 1 - exp (-x ^ α) :=
      sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr (rpow_nonneg hx0.le _)))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (rpow_nonneg hx0.le _) h0)]
    exact mul_le_of_le_one_right (rpow_nonneg hx0.le _) (by linarith [exp_pos (-x ^ α)])

private lemma tendsto_rpow_mul_exponential_difference_zero {α q : ℝ} (hqα : q < α) :
    Tendsto (fun x : ℝ ↦ x ^ (-q) * (1 - exp (-x ^ α))) (𝓝[>] 0) (𝓝 0) := by
  have hp : 0 < α - q := sub_pos.mpr hqα
  have ht : Tendsto (fun x : ℝ ↦ x ^ (α - q)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id.rpow_const_nhds_zero hp)
  refine squeeze_zero' ?_ ?_ ht
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_nonneg (rpow_nonneg (le_of_lt hx) _)
      (sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr (rpow_nonneg (le_of_lt hx) _))))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    calc
      x ^ (-q) * (1 - exp (-x ^ α)) ≤ x ^ (-q) * x ^ α :=
        mul_le_mul_of_nonneg_left
          (by linarith [one_sub_le_exp_neg (x ^ α)])
          (rpow_nonneg (le_of_lt hx) _)
      _ = x ^ (α - q) := by rw [← rpow_add hx]; congr 1; ring

private lemma tendsto_rpow_mul_exponential_difference_atTop {α q : ℝ} (hq : 0 < q) :
    Tendsto (fun x : ℝ ↦ x ^ (-q) * (1 - exp (-x ^ α))) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_rpow_neg_atTop hq)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (rpow_nonneg hx.le _)
      (sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr (rpow_nonneg hx.le _))))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_le_of_le_one_right (rpow_nonneg hx.le _)
      (by linarith [exp_pos (-x ^ α)])

/-- For `0 < q < α`, the power-weighted exponential difference has integral
`Γ(1 - q / α) / q` on the positive half-line. -/
theorem integral_Ioi_rpow_neg_mul_one_sub_exp_neg_rpow {α q : ℝ}
    (hq : 0 < q) (hqα : q < α) :
    ∫ x in Ioi (0 : ℝ), x ^ (-(q + 1)) * (1 - exp (-x ^ α)) =
      Gamma (1 - q / α) / q := by
  have hα : 0 < α := hq.trans hqα
  have hkernel := integrableOn_rpow_neg_mul_one_sub_exp_neg_rpow hq hqα
  have hgamma := integrableOn_rpow_mul_exp_neg_rpow (by linarith : -1 < α - q - 1) hα
  have hprod (x : ℝ) (hx : 0 < x) :
      x ^ (-q) * (exp (-x ^ α) * (α * x ^ (α - 1))) =
        α * (x ^ (α - q - 1) * exp (-x ^ α)) := by
    rw [show α - q - 1 = -q + (α - 1) by ring, rpow_add hx]
    ring
  have hip := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ ↦ x ^ (-q))
    (u' := fun x : ℝ ↦ -q * x ^ (-(q + 1)))
    (v := fun x : ℝ ↦ 1 - exp (-x ^ α))
    (v' := fun x : ℝ ↦ exp (-x ^ α) * (α * x ^ (α - 1)))
    (a := 0) (a' := 0) (b' := 0) ?_ ?_ ?_ ?_
    (tendsto_rpow_mul_exponential_difference_zero hqα)
    (tendsto_rpow_mul_exponential_difference_atTop hq)
  · have hleft : (∫ x in Ioi (0 : ℝ),
        x ^ (-q) * (exp (-x ^ α) * (α * x ^ (α - 1)))) =
        Gamma (1 - q / α) := by
      calc
        _ = ∫ x in Ioi (0 : ℝ), α * (x ^ (α - q - 1) * exp (-x ^ α)) :=
          setIntegral_congr_fun measurableSet_Ioi hprod
        _ = Gamma (1 - q / α) := by
          rw [integral_const_mul,
            integral_rpow_mul_exp_neg_rpow hα (by linarith : -1 < α - q - 1)]
          have heq : (α - q - 1 + 1) / α = 1 - q / α := by field_simp; ring
          rw [heq]
          field_simp
    rw [hleft] at hip
    simp only [zero_sub, sub_zero] at hip
    simp_rw [mul_assoc] at hip
    rw [integral_const_mul] at hip
    apply (eq_div_iff hq.ne').2
    nlinarith [hip]
  · intro x hx
    simpa only [show -q - 1 = -(q + 1) by ring] using
      hasDerivAt_rpow_const (p := -q) (Or.inl hx.ne')
  · intro x hx
    convert (((hasDerivAt_rpow_const (p := α) (Or.inl hx.ne')).neg).exp).const_sub 1
      using 1
    simp only [Pi.neg_apply]
    ring
  · exact IntegrableOn.congr_fun (hgamma.const_mul α)
      (fun x hx ↦ (hprod x hx).symm) measurableSet_Ioi
  · simpa only [IntegrableOn, Pi.mul_def, mul_assoc] using hkernel.const_mul (-q)

end TauCeti
