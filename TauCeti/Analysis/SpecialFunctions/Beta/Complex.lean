/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes

/-!
# Euler's second beta integral with complex parameters

For parameters `a`, `b` with positive real parts and a positive real shift `x`, the
kernel `t ^ (a - 1) * (x + t) ^ (-(a + b))` is absolutely integrable on the positive
half-line. Its integral is `Gamma a * Gamma b / Gamma (a + b) * x ^ (-b)`.
All complex powers use the principal branch; their bases here are positive real numbers.

The unit-shift case is already supplied by `Complex.hasMellin_one_add_cpow_neg`.
Scaling gives the arbitrary positive shift. These formulas supply the model integrals
for expansions of Stieltjes transforms.

On `(0, 1) × ℝ`, a Beta kernel `t ^ (u y - 1) * (1 - t) ^ (v y - 1)` whose exponent functions
`u, v : ℝ → ℂ` are continuous with constant positive real parts `u₀, v₀` combines with any
continuous integrable function `g : ℝ → ℂ` into a product-integrable kernel
`Complex.integrable_beta_mul_profile`, justifying Fubini swaps in Beta-weighted vertical
integrals.

## Main results

* `Complex.integrableOn_cpow_mul_add_cpow`: absolute integrability on `(0, ∞)` of the shifted
  complex beta kernel `t ^ (a - 1) * (x + t) ^ (-(a + b))`.
* `Complex.integral_cpow_mul_add_cpow`: evaluation of the shifted complex beta integral (DLMF
  2.6.4).
* `Complex.integrable_beta_mul_profile`: product integrability on `(0, 1) × ℝ` of
  `t ^ (u y - 1) * (1 - t) ^ (v y - 1) * g y` when `Re (u y) = u₀ > 0`, `Re (v y) = v₀ > 0`,
  and `g` is continuous and integrable on `ℝ`.

## References

* NIST Digital Library of Mathematical Functions, §2.6(i), equation (2.6.4),
  <https://dlmf.nist.gov/2.6.E4>.
-/

public section

open Complex MeasureTheory Set

namespace Complex

private lemma betaKernel_scale (a b : ℂ) {x t : ℝ} (hx : 0 < x) :
    ((x * t : ℝ) : ℂ) ^ (a - 1) * ((x + x * t : ℝ) : ℂ) ^ (-(a + b)) =
      (x : ℂ) ^ (-b - 1) * ((t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (-(a + b))) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hfactor : x + x * t = x * (1 + t) := by ring
  have harg (z : ℂ) : (x : ℂ).arg + z.arg ∈ Ioc (-Real.pi) Real.pi := by
    simpa only [arg_ofReal_of_nonneg hx.le, zero_add] using
      (mem_Ioc.mpr ⟨neg_pi_lt_arg z, arg_le_pi z⟩)
  rw [hfactor, ofReal_mul, ofReal_mul, mul_cpow (harg _) _, mul_cpow (harg _) _,
    ofReal_add, ofReal_one]
  calc
    _ = ((x : ℂ) ^ (a - 1) * (x : ℂ) ^ (-(a + b))) *
        ((t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (-(a + b))) := by ring
    _ = _ := by
      rw [← cpow_add _ _ hx0]
      congr 2
      ring

/-- The shifted complex beta kernel is absolutely integrable on the positive half-line.
Both endpoint conditions are encoded by the positive real parts of the parameters. -/
theorem integrableOn_cpow_mul_add_cpow {a b : ℂ} {x : ℝ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * ((x + t : ℝ) : ℂ) ^ (-(a + b)))
      (Ioi 0) := by
  have hm := hasMellin_one_add_cpow_neg (s := a) (a := a + b) ha (by simp; linarith)
  have hi : IntegrableOn (fun t : ℝ =>
      (x : ℂ) ^ (-b - 1) * ((t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (-(a + b))))
      (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_left_comm] using
      hm.1.const_smul ((x : ℂ) ^ (-b - 1))
  have hs := IntegrableOn.congr_fun hi
    (fun t _ => (betaKernel_scale a b hx).symm) measurableSet_Ioi
  simpa only [mul_zero] using
    (integrableOn_Ioi_comp_mul_left_iff _ 0 hx).mp hs

/-- The Beta-type model integral with positive real shift and complex exponents
(DLMF 2.6.4), using principal complex powers. -/
theorem integral_cpow_mul_add_cpow {a b : ℂ} {x : ℝ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * ((x + t : ℝ) : ℂ) ^ (-(a + b))) =
      Gamma a * Gamma b / Gamma (a + b) * (x : ℂ) ^ (-b) := by
  have hscale := integral_comp_mul_left_Ioi'
    (fun t : ℝ => (t : ℂ) ^ (a - 1) * ((x + t : ℝ) : ℂ) ^ (-(a + b))) 0 hx
  rw [mul_zero] at hscale
  rw [← hscale, setIntegral_congr_fun measurableSet_Ioi
    (fun (t : ℝ) _ => betaKernel_scale a b hx (t := t)),
    integral_const_mul, real_smul]
  have hm := (hasMellin_one_add_cpow_neg (s := a) (a := a + b) ha (by simp; linarith)).2
  simp only [mellin, smul_eq_mul, add_sub_cancel_left] at hm
  rw [hm]
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  calc
    _ = (Gamma a * Gamma b / Gamma (a + b)) *
        ((x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-b - 1)) := by rw [cpow_one]; ring
    _ = _ := by rw [← cpow_add _ _ hx0]; congr 2; ring

/-- Product integrability on `(0, 1) × ℝ` of a Beta-weighted kernel
`(t, y) ↦ t ^ (u y - 1) * (1 - t) ^ (v y - 1) * g y`, where `u, v : ℝ → ℂ` are continuous with
constant positive real parts `u₀, v₀` and `g : ℝ → ℂ` is continuous and integrable on `ℝ`. -/
theorem integrable_beta_mul_profile {u₀ v₀ : ℝ} {u v : ℝ → ℂ} {g : ℝ → ℂ}
    (hu_cont : Continuous u) (hv_cont : Continuous v)
    (hu_re : ∀ y, (u y).re = u₀) (hv_re : ∀ y, (v y).re = v₀)
    (hu₀ : 0 < u₀) (hv₀ : 0 < v₀) (hg_cont : Continuous g) (hg_int : Integrable g) :
    Integrable
      (fun p : ℝ × ℝ ↦ (p.1 : ℂ) ^ (u p.2 - 1) * (1 - (p.1 : ℂ)) ^ (v p.2 - 1) * g p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  have hmeas_oo : (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume : Measure ℝ) =
      volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    simpa [Measure.volume_eq_prod] using
      Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (Ioo 0 1) univ
  have hφ : Integrable
      (fun t : ℝ ↦ ‖(t : ℂ) ^ ((u₀ : ℂ) - 1) * (1 - (t : ℂ)) ^ ((v₀ : ℂ) - 1)‖)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have hb_conv := betaIntegral_convergent (u := u₀) (v := v₀) (by simpa using hu₀)
      (by simpa using hv₀)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hb_conv
    exact (hb_conv.mono_set Ioo_subset_Ioc_self).norm
  have hF_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ (p.1 : ℂ) ^ (u p.2 - 1) * (1 - (p.1 : ℂ)) ^ (v p.2 - 1) * g p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
    rw [hmeas_oo]
    refine ContinuousOn.aestronglyMeasurable (fun ⟨t, y⟩ ⟨⟨ht0, ht1⟩, _⟩ ↦ ?_)
      (measurableSet_Ioo.prod MeasurableSet.univ)
    have h1t_slit : 1 - (t : ℂ) ∈ slitPlane := by
      rw [← ofReal_one, ← ofReal_sub]
      exact ofReal_mem_slitPlane.2 (sub_pos.2 ht1)
    exact (((ContinuousAt.cpow (by fun_prop) ((hu_cont.sub continuous_const).continuousAt.comp
        continuousAt_snd) (ofReal_mem_slitPlane.2 ht0)).mul
      (ContinuousAt.cpow (by fun_prop) ((hv_cont.sub continuous_const).continuousAt.comp
        continuousAt_snd) h1t_slit)).mul
      (hg_cont.continuousAt.comp continuousAt_snd)).continuousWithinAt
  refine (hφ.mul_prod hg_int.norm).mono' hF_meas ?_
  rw [hmeas_oo]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with
    ⟨t, y⟩ ⟨⟨ht0, ht1⟩, _⟩
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  rw [← ofReal_one, ← ofReal_sub]
  simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos h1t,
    sub_re, ofReal_re, hu_re, hv_re]
  exact le_rfl

-- The elementary and half-integer cases check the normalization and the shift factor.
example {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), ((x + t : ℝ) : ℂ) ^ (-2 : ℂ)) = (x : ℂ)⁻¹ := by
  convert integral_cpow_mul_add_cpow (a := 1) (b := 1) (by norm_num) (by norm_num) hx using 1 <;>
    norm_num [cpow_neg_one, Gamma_nat_eq_factorial]

example :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-(1 / 2) : ℂ) * (1 + (t : ℂ))⁻¹) = (Real.pi : ℂ) := by
  have h := integral_cpow_mul_add_cpow (a := 1 / 2) (b := 1 / 2) (x := 1)
    (by norm_num) (by norm_num) zero_lt_one
  norm_num [cpow_neg_one, Gamma_one_half_eq, ← sq] at h
  convert h using 1
  rw [← cpow_nat_mul]
  norm_num

end Complex
