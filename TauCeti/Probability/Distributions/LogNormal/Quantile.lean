/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LogNormal.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Probability.Distributions.Gaussian.Quantile
import TauCeti.Probability.Quantile.Map

/-!
# Quantiles of log-normal laws

At every level `0 < u < 1`, the quantile of the log-normal law with log-mean `m` and
nonnegative log-variance `v` is
`exp (m + sqrt (2 * v) * erfInv (2 * u - 1))`. This includes zero log-variance, where the law
is the Dirac mass at `exp m`.

The one-sided endpoint limits are stated in `EReal`: a positive-log-variance law has limits `0`
and `⊤`, while both limits of the zero-log-variance law are `exp m`. These are limits through
interior levels and do not depend on the totalized quantile values at `0` and `1`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapter 14.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

/-- The quantile of a log-normal law, including its zero-log-variance Dirac boundary. -/
theorem quantile_logNormalMeasure (m : ℝ) (v : ℝ≥0) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (logNormalMeasure m v).quantile u =
      Real.exp (m + √(2 * (v : ℝ)) * Real.erfInv (2 * u - 1)) := by
  rw [logNormalMeasure_map_exp, Measure.quantile_map_exp hu.1 hu.2,
    quantile_gaussianReal m v hu]

/-- The lower endpoint limit of a log-normal quantile is zero at positive log-variance and the
atom `exp m` at zero log-variance. -/
theorem tendsto_quantile_logNormalMeasure_nhdsGT_zero (m : ℝ) (v : ℝ≥0) :
    Tendsto (fun u ↦ ((logNormalMeasure m v).quantile u : EReal)) (nhdsWithin 0 (Ioi 0))
      (nhds (if v = 0 then (Real.exp m : EReal) else 0)) := by
  by_cases hv : v = 0
  · subst hv
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    simp [Measure.quantile_dirac (Real.exp m) hu.1 hu.2.le]
  · rw [ite_eq_right hv]
    have hlevel : Tendsto (fun u : ℝ ↦ 2 * u - 1) (nhdsWithin 0 (Ioi 0))
        (nhdsWithin (-1) (Ioi (-1))) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : ContinuousAt (fun u : ℝ ↦ 2 * u - 1) 0 := by fun_prop
        simpa using hc.tendsto.mono_left
          (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) ≤ nhds (0 : ℝ))
      · filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [mem_Ioi] at hu ⊢
        linarith
    have herf : Tendsto (fun u : ℝ ↦ Real.erfInv (2 * u - 1))
        (nhdsWithin 0 (Ioi 0)) atBot :=
      Real.tendsto_erfInv_nhdsGT_neg_one.comp hlevel
    have hsqrt : 0 < √(2 * (v : ℝ)) := Real.sqrt_pos.2 (by positivity)
    have harg : Tendsto
        (fun u : ℝ ↦ m + √(2 * (v : ℝ)) * Real.erfInv (2 * u - 1))
        (nhdsWithin 0 (Ioi 0)) atBot :=
      tendsto_atBot_add_const_left _ m ((tendsto_const_mul_atBot_of_pos hsqrt).2 herf)
    have hlim : Tendsto
        (fun u : ℝ ↦ Real.exp (m + √(2 * (v : ℝ)) * Real.erfInv (2 * u - 1)))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := Real.tendsto_exp_atBot.comp harg
    apply (EReal.tendsto_coe.mpr hlim).congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_logNormalMeasure m v hu).symm

/-- The upper endpoint limit of a log-normal quantile is plus infinity at positive log-variance
and the atom `exp m` at zero log-variance. -/
theorem tendsto_quantile_logNormalMeasure_nhdsLT_one (m : ℝ) (v : ℝ≥0) :
    Tendsto (fun u ↦ ((logNormalMeasure m v).quantile u : EReal)) (nhdsWithin 1 (Iio 1))
      (nhds (if v = 0 then (Real.exp m : EReal) else ⊤)) := by
  by_cases hv : v = 0
  · subst hv
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    simp [Measure.quantile_dirac (Real.exp m) hu.1 hu.2.le]
  · rw [ite_eq_right hv]
    have hlevel : Tendsto (fun u : ℝ ↦ 2 * u - 1) (nhdsWithin 1 (Iio 1))
        (nhdsWithin 1 (Iio 1)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : ContinuousAt (fun u : ℝ ↦ 2 * u - 1) 1 := by fun_prop
        convert hc.tendsto.mono_left
          (nhdsWithin_le_nhds : nhdsWithin (1 : ℝ) (Iio (1 : ℝ)) ≤ nhds (1 : ℝ)) using 1
        all_goals norm_num
      · filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [mem_Iio] at hu ⊢
        linarith
    have herf : Tendsto (fun u : ℝ ↦ Real.erfInv (2 * u - 1))
        (nhdsWithin 1 (Iio 1)) atTop :=
      Real.tendsto_erfInv_nhdsLT_one.comp hlevel
    have hsqrt : 0 < √(2 * (v : ℝ)) := Real.sqrt_pos.2 (by positivity)
    have harg : Tendsto
        (fun u : ℝ ↦ m + √(2 * (v : ℝ)) * Real.erfInv (2 * u - 1))
        (nhdsWithin 1 (Iio 1)) atTop :=
      tendsto_atTop_add_const_left _ m ((tendsto_const_mul_atTop_of_pos hsqrt).2 herf)
    have hlim : Tendsto
        (fun u : ℝ ↦ Real.exp (m + √(2 * (v : ℝ)) * Real.erfInv (2 * u - 1)))
        (nhdsWithin 1 (Iio 1)) atTop := Real.tendsto_exp_atTop.comp harg
    apply EReal.tendsto_coe_nhds_top_iff.mpr
    apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    exact (quantile_logNormalMeasure m v hu).symm

end TauCeti.Probability
