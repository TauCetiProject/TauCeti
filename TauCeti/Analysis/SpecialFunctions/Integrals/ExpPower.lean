/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A compensated exponential power integral

This file evaluates the Mellin-type integral obtained by subtracting a stretched exponential
from one. The subtraction makes the negative power integrable at zero, while the negative
power itself gives convergence at infinity. This integral occurs when fractional absolute
moments are recovered from stretched-exponential characteristic functions.

## Main declarations

* `TauCeti.integrableOn_rpow_neg_mul_one_sub_exp_neg_rpow`: integrability when the power in the
  exponential is larger than the singular exponent.
* `TauCeti.integral_Ioi_rpow_neg_mul_one_sub_exp_neg_rpow`: the integral equals a Gamma value.
-/

public section

namespace TauCeti

open Filter MeasureTheory Real Set
open scoped Topology

/-- If `0 < q < p`, then `x ^ (-q - 1) * (1 - exp (-x ^ p))` is integrable on the positive
half-line. -/
theorem integrableOn_rpow_neg_mul_one_sub_exp_neg_rpow {p q : ℝ} (hq : 0 < q) (hqp : q < p) :
    IntegrableOn (fun x : ℝ ↦ x ^ (-(q + 1)) * (1 - exp (-x ^ p))) (Ioi 0) := by
  have hp : 0 < p := hq.trans hqp
  have hzero_major : IntegrableOn (fun x : ℝ ↦ x ^ (p - q - 1)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by linarith)
  have hzero : IntegrableOn
      (fun x : ℝ ↦ x ^ (-(q + 1)) * (1 - exp (-x ^ p))) (Ioo 0 1) := by
    refine hzero_major.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : 0 < x := hx.1
    have hpow0 : 0 ≤ x ^ p := by positivity
    have hexp0 : 0 ≤ 1 - exp (-x ^ p) :=
      sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr hpow0))
    have hexp_le : 1 - exp (-x ^ p) ≤ x ^ p := by
      linarith [Real.add_one_le_exp (-x ^ p)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hexp0)]
    calc
      x ^ (-(q + 1)) * (1 - exp (-x ^ p)) ≤ x ^ (-(q + 1)) * x ^ p := by
        gcongr
      _ = x ^ (p - q - 1) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
  have htop_major : IntegrableOn (fun x : ℝ ↦ x ^ (-(q + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have htop_Ioi : IntegrableOn
      (fun x : ℝ ↦ x ^ (-(q + 1)) * (1 - exp (-x ^ p))) (Ioi 1) := by
    refine htop_major.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hpow0 : 0 ≤ x ^ p := by positivity
    have hexp0 : 0 ≤ 1 - exp (-x ^ p) :=
      sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr hpow0))
    have hexp_le : 1 - exp (-x ^ p) ≤ 1 := by linarith [exp_pos (-x ^ p)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hexp0)]
    exact mul_le_of_le_one_right (by positivity) hexp_le
  have htop : IntegrableOn
      (fun x : ℝ ↦ x ^ (-(q + 1)) * (1 - exp (-x ^ p))) (Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := fun x : ℝ ↦ x ^ (-(q + 1)) * (1 - exp (-x ^ p)))).2 htop_Ioi
  rw [← Ioo_union_Ici_eq_Ioi zero_lt_one]
  exact hzero.union htop

private theorem integral_Ioi_rpow_neg_mul_one_sub_exp_neg {r : ℝ} (hr : r ∈ Ioo 0 1) :
    ∫ x in Ioi (0 : ℝ), x ^ (-(r + 1)) * (1 - exp (-x)) = Real.Gamma (1 - r) / r := by
  have hint : IntegrableOn (fun x : ℝ ↦ x ^ (-(r + 1)) * (1 - exp (-x))) (Ioi 0) := by
    simpa using integrableOn_rpow_neg_mul_one_sub_exp_neg_rpow (p := 1) hr.1 hr.2
  have hgamma : IntegrableOn (fun x : ℝ ↦ x ^ (-r) * exp (-x)) (Ioi 0) :=
    by simpa [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := -r) (neg_lt_neg hr.2) zero_lt_one
  have hu (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun y : ℝ ↦ y ^ (-r)) (-r * x ^ (-r - 1)) x := by
    convert hasDerivAt_rpow_const (p := -r) (Or.inl hx.ne') using 1
  have hv (x : ℝ) (_hx : x ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun y : ℝ ↦ 1 - exp (-y)) (exp (-x)) x := by
    have h := ((hasDerivAt_id x).neg.exp).const_sub 1
    convert h using 1
    · ext y
      simp only [Pi.neg_apply, id_eq]
    · simp only [Pi.neg_apply, id_eq]
      ring
  have hzero : Tendsto (fun x : ℝ ↦ x ^ (-r) * (1 - exp (-x))) (𝓝[>] 0) (𝓝 0) := by
    have hpow : Tendsto (fun x : ℝ ↦ x ^ (1 - r)) (𝓝[>] 0) (𝓝 0) := by
      have hcont : ContinuousWithinAt (fun x : ℝ ↦ x ^ (1 - r)) (Ioi 0) 0 :=
        (Real.continuousAt_rpow_const 0 (1 - r)
          (Or.inr (by linarith [hr.2]))).continuousWithinAt
      simpa only [Real.zero_rpow (by linarith [hr.2] : 1 - r ≠ 0)] using
        hcont.tendsto
    have hquot : Tendsto (fun x : ℝ ↦ (1 - exp (-x)) / x) (𝓝[>] 0) (𝓝 1) := by
      have hderiv : HasDerivAt (fun y : ℝ ↦ 1 - exp (-y)) 1 0 := by
        simpa only [Pi.neg_apply, id_eq, neg_zero, exp_zero, neg_neg, one_mul] using
          ((hasDerivAt_id (0 : ℝ)).neg.exp).const_sub 1
      simpa [div_eq_inv_mul] using hderiv.tendsto_slope_zero_right
    have hmul := hpow.mul hquot
    simp only [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 < x := hx
    rw [div_eq_mul_inv]
    calc
      x ^ (1 - r) * ((1 - exp (-x)) * x⁻¹) =
          (x ^ (1 - r) * x⁻¹) * (1 - exp (-x)) := by ring
      _ = x ^ (-r) * (1 - exp (-x)) := by
        rw [← Real.rpow_neg_one x, ← Real.rpow_add hx0]
        congr 1
        ring_nf
  have hinfty : Tendsto (fun x : ℝ ↦ x ^ (-r) * (1 - exp (-x))) atTop (𝓝 0) := by
    have hpow : Tendsto (fun x : ℝ ↦ x ^ (-r)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hr.1
    have hexp : Tendsto (fun x : ℝ ↦ 1 - exp (-x)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using hpow.mul hexp
  have hexponent : -r - 1 = -(r + 1) := by ring
  have hderivInt : IntegrableOn
      (fun x : ℝ ↦ (-r * x ^ (-r - 1)) * (1 - exp (-x))) (Ioi 0) := by
    refine (hint.const_mul (-r)).congr ?_
    filter_upwards with x
    rw [hexponent]
    ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := 0) (u := fun x : ℝ ↦ x ^ (-r)) (u' := fun x ↦ -r * x ^ (-r - 1))
    (v := fun x ↦ 1 - exp (-x)) (v' := fun x ↦ exp (-x)) hu hv hgamma
    hderivInt hzero hinfty
  have hGamma : ∫ x in Ioi (0 : ℝ), x ^ (-r) * exp (-x) = Real.Gamma (1 - r) := by
    convert integral_rpow_mul_exp_neg_rpow (p := 1) (q := -r) zero_lt_one
      (neg_lt_neg hr.2) using 1 <;> simp [Real.rpow_one]
    congr 1
    ring
  have hderiv_eq :
      ∫ x in Ioi (0 : ℝ), (-r * x ^ (-r - 1)) * (1 - exp (-x)) =
        -r * ∫ x in Ioi (0 : ℝ), x ^ (-(r + 1)) * (1 - exp (-x)) := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), -r * (x ^ (-(r + 1)) * (1 - exp (-x))) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x _hx ↦ ?_
        rw [hexponent]
        ring
      _ = _ := by rw [integral_const_mul]
  rw [hGamma, hderiv_eq] at hibp
  simp only [zero_sub, neg_zero] at hibp
  apply (eq_div_iff hr.1.ne').2
  linarith

/-- For `0 < q < p`, the compensated exponential-power integral is
`Gamma (1 - q / p) / q`. -/
theorem integral_Ioi_rpow_neg_mul_one_sub_exp_neg_rpow {p q : ℝ} (hq : 0 < q) (hqp : q < p) :
    ∫ x in Ioi (0 : ℝ), x ^ (-(q + 1)) * (1 - exp (-x ^ p)) =
      Real.Gamma (1 - q / p) / q := by
  have hp : 0 < p := hq.trans hqp
  have hr : q / p ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hq hp, (div_lt_one hp).2 hqp⟩
  have hsub := integral_comp_rpow_Ioi
    (fun y : ℝ ↦ y ^ (-(q / p + 1)) * (1 - exp (-y))) hp.ne'
  rw [abs_of_pos hp] at hsub
  simp only [smul_eq_mul] at hsub
  have hpoint (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      (p * x ^ (p - 1)) *
          ((x ^ p) ^ (-(q / p + 1)) * (1 - exp (-(x ^ p)))) =
        p * (x ^ (-(q + 1)) * (1 - exp (-x ^ p))) := by
    have hx0 : 0 < x := hx
    rw [← Real.rpow_mul hx0.le]
    calc
      p * x ^ (p - 1) *
            (x ^ (p * -(q / p + 1)) * (1 - exp (-x ^ p))) =
          p * ((x ^ (p - 1) * x ^ (p * -(q / p + 1))) *
            (1 - exp (-x ^ p))) := by ring
      _ = p * (x ^ (-(q + 1)) * (1 - exp (-x ^ p))) := by
        rw [← Real.rpow_add hx0]
        congr 2
        field_simp
        ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul,
    integral_Ioi_rpow_neg_mul_one_sub_exp_neg hr] at hsub
  calc
    _ = (Real.Gamma (1 - q / p) / (q / p)) / p := by
      apply (eq_div_iff hp.ne').2
      simpa [mul_comm] using hsub
    _ = Real.Gamma (1 - q / p) / q := by
      field_simp [hp.ne', hq.ne']

end TauCeti
