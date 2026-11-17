/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Improper integrals of `t ^ a * log t` on a positive half-line

Companion results to Mathlib's `integrableOn_Ioi_rpow_of_lt`, `integrableOn_Ioi_rpow_iff`, and
`integral_Ioi_rpow_of_lt` for the logarithm-weighted power `t ↦ t ^ a * Real.log t` on `(c, ∞)`
with `c > 0`.

For `c > 0`, `t ^ a * log t` is integrable on `(c, ∞)` if and only if `a < -1`, and in that range
its improper integral evaluates via the antiderivative
`t ^ (a + 1) * log t / (a + 1) - t ^ (a + 1) / (a + 1) ^ 2` to
`c ^ (a + 1) * (1 / (a + 1) ^ 2 - log c / (a + 1))`. No hypothesis `1 ≤ c` is required: when
`0 < c < 1` the integrand changes sign at `1`, so integrability is established by splitting into
the compact interval `(c, max c 1]` and the ray `(max c 1, ∞)`.

## Main results

* `TauCeti.integrableOn_Ioi_rpow_mul_log_of_lt`: `t ↦ t ^ a * Real.log t` is integrable on
  `Set.Ioi c` whenever `a < -1` and `0 < c`.
* `TauCeti.integrableOn_Ioi_rpow_mul_log_iff`: for `0 < c`, `t ↦ t ^ a * Real.log t` is integrable
  on `Set.Ioi c` if and only if `a < -1`.
* `TauCeti.integral_Ioi_rpow_mul_log_of_lt`: for `a < -1` and `0 < c`,
  `∫ t in Set.Ioi c, t ^ a * Real.log t = c ^ (a + 1) * (1 / (a + 1) ^ 2 - Real.log c / (a + 1))`.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- Antiderivative of `t ↦ t ^ a * Real.log t` for `a ≠ -1` on `t ≠ 0`. -/
private noncomputable def rpowLogAntideriv (a t : ℝ) : ℝ :=
  t ^ (a + 1) * Real.log t / (a + 1) - t ^ (a + 1) / (a + 1) ^ 2

private theorem hasDerivAt_rpowLogAntideriv {a t : ℝ} (ha : a ≠ -1) (ht : t ≠ 0) :
    HasDerivAt (rpowLogAntideriv a) (t ^ a * Real.log t) t := by
  have ha1 : a + 1 ≠ 0 := by intro h; exact ha (by linarith)
  have h1 := (hasDerivAt_rpow_mul_log (a + 1) ht).div_const (a + 1)
  have h2 := (Real.hasDerivAt_rpow_const (x := t) (p := a + 1) (Or.inl ht)).div_const ((a + 1) ^ 2)
  refine (h1.sub h2).congr_deriv ?_
  rw [add_sub_cancel_right]
  field_simp [ha1]
  ring

private theorem tendsto_rpowLogAntideriv_atTop {a : ℝ} (ha : a < -1) :
    Tendsto (rpowLogAntideriv a) atTop (𝓝 0) := by
  have hσ : 0 < -(a + 1) := by linarith
  have hpow : Tendsto (fun t : ℝ ↦ t ^ (a + 1)) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop hσ
  have hlog : Tendsto (fun t : ℝ ↦ t ^ (a + 1) * Real.log t) atTop (𝓝 0) := by
    refine (isLittleO_log_rpow_atTop hσ).tendsto_div_nhds_zero.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.rpow_neg ht.le, div_inv_eq_mul, mul_comm]
  have hsub : Tendsto (fun t : ℝ ↦
      t ^ (a + 1) * Real.log t / (a + 1) - t ^ (a + 1) / (a + 1) ^ 2) atTop (𝓝 0) := by
    simpa using (hlog.div_const (a + 1)).sub (hpow.div_const ((a + 1) ^ 2))
  exact hsub

/-- If `a < -1` and `0 < c`, then `t ↦ t ^ a * Real.log t` is integrable on `(c, ∞)`. -/
theorem integrableOn_Ioi_rpow_mul_log_of_lt {a c : ℝ} (ha : a < -1) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ t ^ a * Real.log t) (Ioi c) := by
  set m : ℝ := max c 1
  have hcm : c ≤ m := le_max_left c 1
  have hm1 : 1 ≤ m := le_max_right c 1
  have hlow : IntegrableOn (fun t : ℝ ↦ t ^ a * Real.log t) (Ioc c m) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    refine ContinuousOn.mul (fun t ht ↦ ?_)
      (Real.continuousOn_log.mono fun t ht ↦ (hc.trans_le ht.1).ne')
    exact (Real.continuousAt_rpow_const t a (Or.inl (hc.trans_le ht.1).ne')).continuousWithinAt
  have hhigh : IntegrableOn (fun t : ℝ ↦ t ^ a * Real.log t) (Ioi m) := by
    have hd : ∀ t ∈ Ici m, HasDerivAt (rpowLogAntideriv a) (t ^ a * Real.log t) t := fun t ht ↦
      hasDerivAt_rpowLogAntideriv (by linarith) (zero_lt_one.trans_le (hm1.trans ht)).ne'
    have hnonneg : ∀ t ∈ Ioi m, 0 ≤ t ^ a * Real.log t := fun t ht ↦
      mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hm1.trans ht.le)) a)
        (Real.log_nonneg (hm1.trans ht.le))
    exact integrableOn_Ioi_deriv_of_nonneg' hd hnonneg (tendsto_rpowLogAntideriv_atTop ha)
  rw [← Ioc_union_Ioi_eq_Ioi hcm]
  exact hlow.union hhigh

/-- For `0 < c`, `t ↦ t ^ a * Real.log t` is integrable on `(c, ∞)` if and only if `a < -1`. -/
theorem integrableOn_Ioi_rpow_mul_log_iff {a c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ t ^ a * Real.log t) (Ioi c) ↔ a < -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrableOn_Ioi_rpow_mul_log_of_lt h hc⟩
  by_contra! ha
  set m : ℝ := max c (Real.exp 1)
  have hm_ge : c ≤ m := le_max_left c (Real.exp 1)
  have hm_exp : Real.exp 1 ≤ m := le_max_right c (Real.exp 1)
  have hm_pos : 0 < m := (Real.exp_pos 1).trans_le hm_exp
  have hrpow : IntegrableOn (fun t : ℝ ↦ t ^ a) (Ioi m) := by
    refine (h.mono_set (Ioi_subset_Ioi hm_ge)).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi
      exact (Real.continuousAt_rpow_const t a (Or.inl (hm_pos.trans ht).ne')).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := hm_pos.trans ht
      have hlog_ge : 1 ≤ Real.log t := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (hm_exp.trans ht.le)
      have hpow_nonneg : 0 ≤ t ^ a := Real.rpow_nonneg ht_pos.le a
      rw [Real.norm_of_nonneg hpow_nonneg]
      exact le_mul_of_one_le_right hpow_nonneg hlog_ge
  exact not_integrableOn_Ioi_rpow_of_neg_one_le ha hrpow

/-- Closed form for the improper integral of `t ^ a * Real.log t` over `(c, ∞)` when `a < -1` and
`0 < c`. -/
theorem integral_Ioi_rpow_mul_log_of_lt {a c : ℝ} (ha : a < -1) (hc : 0 < c) :
    ∫ t in Ioi c, t ^ a * Real.log t =
      c ^ (a + 1) * (1 / (a + 1) ^ 2 - Real.log c / (a + 1)) := by
  have hd : ∀ t ∈ Ici c, HasDerivAt (rpowLogAntideriv a) (t ^ a * Real.log t) t := fun t ht ↦
    hasDerivAt_rpowLogAntideriv (by linarith) (hc.trans_le ht).ne'
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_Ioi_rpow_mul_log_of_lt ha hc)
    (tendsto_rpowLogAntideriv_atTop ha)]
  simp only [rpowLogAntideriv, zero_sub]
  ring

end TauCeti
