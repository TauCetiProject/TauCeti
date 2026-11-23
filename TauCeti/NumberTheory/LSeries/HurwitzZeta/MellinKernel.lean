/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.HurwitzZeta.Series
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference
import TauCeti.Analysis.SpecialFunctions.Exp.LatticeSum
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.Analysis.SpecialFunctions.Pow.Summable

/-!
# Mellin–Laplace kernel for the complex Hurwitz zeta function

For `1 < Re s` and `0 < Re c`, the shifted exponential-kernel integrand
`t ↦ t ^ (s - 1) * (exp (-c * t) / (1 - exp (-t)))` is integrable on `(0, ∞)` via the direct
Gamma majorant `(1 - exp (-t))⁻¹ ≤ 1 + t⁻¹`, and termwise integration of
`exp ((1 - c) * t) / (exp t - 1) = ∑_{k ≥ 0} exp (-(k + c) * t)` identifies its Mellin–Laplace
integral on `(0, ∞)` with `Gamma s * complexHurwitzSeries s c`.

This shared kernel module sits below both
`TauCeti.Analysis.SpecialFunctions.IncompleteGamma.IncompleteZeta` (which specializes `c = 1` to
the Riemann zeta integral and DLMF 8.22.2–8.22.3) and
`TauCeti.NumberTheory.LSeries.HurwitzZeta.Continuation`.

## Main results

* `TauCeti.integrableOn_hurwitzMellinIntegrand`: integrability of
  `t ↦ (t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t)))` on `Ioi 0` for `1 < s.re` and
  `0 < c.re`.
* `TauCeti.hasSum_setIntegral_cpow_mul_exp_neg_mul`: termwise integration of
  `t^{s−1} e^{(1−c)t}/(e^t − 1) = ∑_{k ≥ 0} t^{s−1} e^{−(k+c)t}` over any subset of `(0, ∞)` for
  `1 < s.re` and `0 < c.re`.
* `TauCeti.integral_hurwitzMellinIntegrand_eq_Gamma_mul_complexHurwitzSeries`:
  `∫₀^∞ t^{s−1} e^{−ct} / (1 − e^{−t}) dt = Γ(s) * complexHurwitzSeries s c` for `1 < s.re` and
  `0 < c.re`.
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- For `1 < s.re` and `0 < c.re`, the Mellin–Laplace integrand
`t ↦ (t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t)))` is integrable on `Ioi 0`. -/
theorem integrableOn_hurwitzMellinIntegrand {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t)))) (Ioi 0) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : 0 < (s - 1).re := by simpa using hs
  have hdom : IntegrableOn
      (fun t : ℝ =>
        ‖(t : ℂ) ^ (s - 1) * cexp (-(c * t))‖ +
          ‖(t : ℂ) ^ ((s - 1) - 1) * cexp (-(c * t))‖) (Ioi 0) :=
    (integrableOn_cpow_mul_exp_neg_mul_Ioi hs0 hc).norm.add
      (integrableOn_cpow_mul_exp_neg_mul_Ioi hs1 hc).norm
  refine hdom.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have h1e : 0 < 1 - Real.exp (-t) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have key : (1 + t) * Real.exp (-t) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos t)]
    linarith [Real.add_one_le_exp t]
  have hden : ‖1 - cexp (-(t : ℂ))‖ = 1 - Real.exp (-t) := by
    rw [← ofReal_neg, ← ofReal_exp, ← ofReal_one, ← ofReal_sub, norm_real,
      Real.norm_of_nonneg h1e.le]
  have hrew : ‖(t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t)))‖ =
      (t ^ (s.re - 1) * Real.exp (-c.re * t)) / (1 - Real.exp (-t)) := by
    rw [norm_mul, norm_div, hden, ← mul_div_assoc, ← norm_mul, neg_mul,
      norm_cpow_mul_exp_neg_mul s c ht0]
  have hpow : t ^ ((s - 1).re - 1) * t = t ^ (s.re - 1) := by
    rw [sub_re, one_re, ← Real.rpow_add_one ht0.ne']
    ring_nf
  have hrhs : ‖(t : ℂ) ^ (s - 1) * cexp (-(c * t))‖ +
      ‖(t : ℂ) ^ ((s - 1) - 1) * cexp (-(c * t))‖ =
      t ^ (s.re - 1) * Real.exp (-c.re * t) +
        t ^ ((s - 1).re - 1) * Real.exp (-c.re * t) := by
    rw [norm_cpow_mul_exp_neg_mul s c ht0, norm_cpow_mul_exp_neg_mul (s - 1) c ht0]
  rw [hrew, hrhs, div_le_iff₀ h1e]
  have h1 : t ≤ (t + 1) * (1 - Real.exp (-t)) := by linarith
  rw [← hpow]
  calc
    t ^ ((s - 1).re - 1) * t * Real.exp (-c.re * t)
        = (t ^ ((s - 1).re - 1) * Real.exp (-c.re * t)) * t := by ring
    _ ≤ (t ^ ((s - 1).re - 1) * Real.exp (-c.re * t)) * ((t + 1) * (1 - Real.exp (-t))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (t ^ ((s - 1).re - 1) * t * Real.exp (-c.re * t) +
          t ^ ((s - 1).re - 1) * Real.exp (-c.re * t)) * (1 - Real.exp (-t)) := by ring

/-- Expansion of `exp ((1 - c) * t) / (exp t - 1)` under the integral: for `1 < Re s`,
`0 < Re c`, and every set `A ⊆ (0, ∞)`,
`∫_A t^{s−1} e^{(1−c)t}/(e^t − 1) dt = ∑_{k ≥ 0} ∫_A t^{s−1} e^{−(k+c)t} dt`. -/
theorem hasSum_setIntegral_cpow_mul_exp_neg_mul {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re)
    {A : Set ℝ} (hA0 : A ⊆ Ioi 0) :
    HasSum (fun k : ℕ => ∫ t in A, (t : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + c) * t)))
      (∫ t in A, (t : ℂ) ^ (s - 1) * (cexp ((1 - c) * t) / (cexp t - 1))) := by
  have hs0 : 0 < s.re := by linarith
  have hk (k : ℕ) : 0 < ((k : ℂ) + c).re := by
    rw [add_re, natCast_re]
    positivity
  have hF (k : ℕ) : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + c) * t)))
      (Ioi 0) := integrableOn_cpow_mul_exp_neg_mul_Ioi hs0 (hk k)
  have hsum :
      Summable fun k : ℕ => ∫ t in A, ‖(t : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + c) * t))‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
      (fun k => setIntegral_mono_set (hF k).norm (ae_of_all _ fun t => norm_nonneg _)
        (ae_of_all _ hA0)) ?_
    have h := (summable_norm_natCast_add_cpow_neg hs (c.re : ℂ)).mul_left (Real.Gamma s.re)
    refine h.congr fun k => ?_
    have hre_pos : 0 < (k : ℝ) + c.re := by positivity
    rw [integral_norm_cpow_mul_exp_neg_mul_Ioi hs0 (hk k)]
    have hcpow : ‖((k : ℂ) + (c.re : ℂ)) ^ (-s)‖ = (((k : ℂ) + c).re⁻¹) ^ s.re := by
      have hsum_eq : (k : ℂ) + (c.re : ℂ) = (((k : ℝ) + c.re : ℝ) : ℂ) := by push_cast; ring
      rw [hsum_eq, norm_cpow_eq_rpow_re_of_pos hre_pos, neg_re, Real.rpow_neg hre_pos.le,
        ← Real.inv_rpow hre_pos.le, add_re, natCast_re]
    simp only [hcpow, ← one_div, mul_comm (Real.Gamma s.re)]
  convert hasSum_integral_of_summable_integral_norm (fun k => (hF k).mono_set hA0) hsum using 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hA0 (ae_restrict_mem measurableSet_Ioi)]
    with t ht0
  have htsum := ((hasSum_exp_neg_natCast_add_one_mul (z := t) (by simpa using ht0)).mul_left
    ((t : ℂ) ^ (s - 1) * cexp ((1 - c) * t))).tsum_eq
  rw [mul_one_div, ← mul_div_assoc'] at htsum
  rw [← htsum]
  refine tsum_congr fun k => ?_
  rw [mul_assoc, ← exp_add]
  congr 2
  ring

/-- For `1 < s.re` and `0 < c.re`, the Mellin–Laplace integral of the Hurwitz kernel equals
`Gamma s * complexHurwitzSeries s c`. -/
theorem integral_hurwitzMellinIntegrand_eq_Gamma_mul_complexHurwitzSeries {s c : ℂ}
    (hs : 1 < s.re) (hc : 0 < c.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t))) =
      Gamma s * complexHurwitzSeries s c := by
  have hs0 : 0 < s.re := by linarith
  have hkernel : EqOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t))))
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (cexp ((1 - c) * t) / (cexp t - 1))) (Ioi 0) :=
    fun t _ => by simp only [Complex.exp_neg_mul_div_one_sub_exp_neg]
  rw [setIntegral_congr_fun measurableSet_Ioi hkernel]
  have hsum := hasSum_setIntegral_cpow_mul_exp_neg_mul hs hc subset_rfl
  have hterm : (fun k : ℕ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + c) * t))) =
      fun k : ℕ => Gamma s * ((k : ℂ) + c) ^ (-s) := funext fun k => by
    have hk : 0 < ((k : ℂ) + c).re := by
      simp only [add_re, natCast_re]
      positivity
    exact integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs0 hk
  rw [hterm] at hsum
  exact hsum.unique ((hasSum_complexHurwitzSeries_of_re_pos hs hc).mul_left (Gamma s))

end TauCeti

end
