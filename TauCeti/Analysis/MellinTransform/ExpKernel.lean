/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.InvSubOne
import TauCeti.Analysis.SpecialFunctions.Exp.LatticeSum
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.Analysis.SpecialFunctions.Pow.Summable

/-!
# Mellin–Laplace exponential kernels

For `1 < Re s` and `0 < Re c`, the shifted exponential-kernel integrand
`t ↦ (t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t)))` is integrable on `(0, ∞)` via the
shared scalar bound `(1 - exp (-t))⁻¹ ≤ 1 + t⁻¹` (`TauCeti.inv_one_sub_exp_neg_le`), and any
compact subset of `{p : ℂ × ℂ | 1 < p.1.re ∧ 0 < p.2.re}` admits a common integrable majorant
(`TauCeti.exists_integrableOn_norm_cpow_mul_exp_neg_mul_div_one_sub_exp_neg_le`).

For `1 < Re s` and `0 < Re c`, termwise integration of the `t > 0` geometric expansion
`exp ((1 - c) * t) / (exp t - 1) = ∑_{k ≥ 0} exp (-(k + c) * t)` over any subset of `(0, ∞)`
gives the infinite series representation `TauCeti.hasSum_setIntegral_cpow_mul_exp_neg_mul`, and
specializing to `c = 1` (for `1 < Re s`) yields `TauCeti.integrableOn_cpow_div_exp_sub_one`.

## Main results

* `TauCeti.integrableOn_cpow_mul_exp_neg_mul_div_one_sub_exp_neg`: integrability of
  `t ↦ (t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t)))` on `Ioi 0` for `1 < s.re` and
  `0 < c.re`.
* `TauCeti.exists_integrableOn_norm_cpow_mul_exp_neg_mul_div_one_sub_exp_neg_le`:
  parameter-uniform integrable majorant on compact subsets of
  `{p : ℂ × ℂ | 1 < p.1.re ∧ 0 < p.2.re}`.
* `TauCeti.hasSum_setIntegral_cpow_mul_exp_neg_mul`: for `1 < s.re` and `0 < c.re`, termwise
  integration of the `t > 0` expansion
  `t^{s−1} e^{(1−c)t}/(e^t − 1) = ∑_{k ≥ 0} t^{s−1} e^{−(k+c)t}` over any subset of `(0, ∞)`.
* `TauCeti.integrableOn_cpow_div_exp_sub_one`: integrability of `t ↦ t^{s−1}/(e^t − 1)` on
  `(0, ∞)` for `1 < Re s`.
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- For `1 < s.re` and `0 < c.re`, the Mellin–Laplace integrand
`t ↦ (t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t)))` is integrable on `Ioi 0`. -/
theorem integrableOn_cpow_mul_exp_neg_mul_div_one_sub_exp_neg {s c : ℂ} (hs : 1 < s.re)
    (hc : 0 < c.re) :
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
  calc
    ‖(t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t)))‖
        = t ^ (s.re - 1) * (Real.exp (-c.re * t) / (1 - Real.exp (-t))) := by
          rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re,
            norm_exp_neg_mul_div_one_sub_exp_neg ht0 c]
    _ = t ^ (s.re - 1) * ((1 - Real.exp (-t))⁻¹ * Real.exp (-c.re * t)) := by
        rw [div_eq_mul_inv, mul_comm (Real.exp (-c.re * t))]
    _ ≤ t ^ (s.re - 1) * ((1 + t⁻¹) * Real.exp (-c.re * t)) := by
        gcongr
        exact inv_one_sub_exp_neg_le ht0
    _ = t ^ (s.re - 1) * Real.exp (-c.re * t) +
          t ^ ((s - 1).re - 1) * Real.exp (-c.re * t) := by
        have hpow : t ^ (s.re - 1) * t⁻¹ = t ^ ((s - 1).re - 1) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add ht0, sub_re, one_re]
          congr 1
        calc
          t ^ (s.re - 1) * ((1 + t⁻¹) * Real.exp (-c.re * t))
              = t ^ (s.re - 1) * Real.exp (-c.re * t) +
                  (t ^ (s.re - 1) * t⁻¹) * Real.exp (-c.re * t) := by ring
          _ = _ := by rw [hpow]
    _ = ‖(t : ℂ) ^ (s - 1) * cexp (-(c * t))‖ +
          ‖(t : ℂ) ^ ((s - 1) - 1) * cexp (-(c * t))‖ := by
        rw [norm_cpow_mul_exp_neg_mul s c ht0, norm_cpow_mul_exp_neg_mul (s - 1) c ht0]

/-- On any compact subset `K ⊆ {p : ℂ × ℂ | 1 < p.1.re ∧ 0 < p.2.re}`, the Mellin–Laplace
integrand is dominated on `(0, ∞)` by a single parameter-independent integrable function. -/
theorem exists_integrableOn_norm_cpow_mul_exp_neg_mul_div_one_sub_exp_neg_le {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) (hK_sub : K ⊆ {p : ℂ × ℂ | 1 < p.1.re ∧ 0 < p.2.re}) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ p ∈ K, ∀ t ∈ Ioi (0 : ℝ),
        ‖(t : ℂ) ^ (p.1 - 1) * (cexp (-p.2 * t) / (1 - cexp (-t)))‖ ≤ g t := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, integrableOn_zero, fun _ hp => False.elim hp⟩
  obtain ⟨pa, hpa_mem, hpa⟩ :=
    hK.exists_isMinOn hKne (continuous_re.comp continuous_fst).continuousOn
  obtain ⟨pb, hpb_mem, hpb⟩ :=
    hK.exists_isMaxOn hKne (continuous_re.comp continuous_fst).continuousOn
  obtain ⟨pη, hpη_mem, hpη⟩ :=
    hK.exists_isMinOn hKne (continuous_re.comp continuous_snd).continuousOn
  set a : ℝ := pa.1.re
  set b : ℝ := pb.1.re
  set η : ℝ := pη.2.re
  have ha : 1 < (a : ℂ).re := by simpa [a] using (hK_sub hpa_mem).1
  have hb : 1 < (b : ℂ).re := by simpa [b] using (hK_sub hpb_mem).1
  have hη : 0 < (η : ℂ).re := by simpa [η] using (hK_sub hpη_mem).2
  refine ⟨fun t : ℝ =>
      ‖(t : ℂ) ^ ((a : ℂ) - 1) * (cexp (-(η : ℂ) * t) / (1 - cexp (-t)))‖ +
        ‖(t : ℂ) ^ ((b : ℂ) - 1) * (cexp (-(η : ℂ) * t) / (1 - cexp (-t)))‖,
    (integrableOn_cpow_mul_exp_neg_mul_div_one_sub_exp_neg ha hη).norm.add
      (integrableOn_cpow_mul_exp_neg_mul_div_one_sub_exp_neg hb hη).norm,
    fun p hp t ht => ?_⟩
  have ht0 : (0 : ℝ) < t := ht
  have h1e : 0 < 1 - Real.exp (-t) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hnorm (s c : ℂ) :
      ‖(t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t)))‖ =
        t ^ (s.re - 1) * (Real.exp (-c.re * t) / (1 - Real.exp (-t))) := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re,
      norm_exp_neg_mul_div_one_sub_exp_neg ht0 c]
  have hexp : Real.exp (-p.2.re * t) / (1 - Real.exp (-t)) ≤
      Real.exp (-η * t) / (1 - Real.exp (-t)) := by
    gcongr
    exact hpη hp
  have hpa' : a ≤ p.1.re := hpa hp
  have hpb' : p.1.re ≤ b := hpb hp
  rcases le_or_gt t 1 with ht1 | ht1
  · refine le_trans ?_ (le_add_of_nonneg_right (norm_nonneg _))
    rw [hnorm p.1 p.2, hnorm a η]
    simp only [ofReal_re]
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith))
      hexp (by positivity) (Real.rpow_nonneg ht0.le _)
  · refine le_trans ?_ (le_add_of_nonneg_left (norm_nonneg _))
    rw [hnorm p.1 p.2, hnorm b η]
    simp only [ofReal_re]
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith))
      hexp (by positivity) (Real.rpow_nonneg ht0.le _)

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

/-- For `1 < Re s`, `t ↦ t^{s−1}/(e^t − 1)` is integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_div_exp_sub_one {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) / (cexp t - 1)) (Ioi 0) := by
  refine (integrableOn_cpow_mul_exp_neg_mul_div_one_sub_exp_neg (c := 1) hs one_pos).congr_fun
    (fun t _ => ?_) measurableSet_Ioi
  simp only [neg_one_mul, Complex.exp_neg_div_one_sub_exp_neg, ← div_eq_mul_inv]

end TauCeti

end
