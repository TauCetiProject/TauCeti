/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirac
public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The quantile function of a real Gaussian law

This file computes `MeasureTheory.Measure.quantile (gaussianReal m v)` in closed form through the
inverse error function `Real.erfInv`. For a level `0 < u < 1` the quantile is
`m + √(2 * v) * erfInv (2 * u - 1)`, which inverts the cdf `(1 + erf ((x - m) / √(2 * v))) / 2`.
At the singular boundary `v = 0` the law is the Dirac mass at `m` and the same formula gives the
constant quantile `m`.

In particular the standard Gaussian quantile is `z(u) = √2 * erfInv (2 * u - 1)`, and the general
formula reads `m + √v * z(u)`.

The one-sided endpoint limits are stated in `EReal`: a positive-variance Gaussian quantile tends
to `⊥` at level zero and to `⊤` at level one, while the zero-variance law has constant quantile
`m` at both endpoints.

## Main declarations

* `TauCeti.Probability.quantile_gaussianReal` — the quantile of `gaussianReal m v`;
* `TauCeti.Probability.quantile_gaussianReal_zero_one` — the standard Gaussian quantile.
* `TauCeti.Probability.tendsto_quantile_gaussianReal_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_gaussianReal_nhdsLT_one` — the one-sided endpoint limits.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {u : ℝ}

/-- The quantile function of a real Gaussian law, including the Dirac boundary `v = 0`: at every
level `0 < u < 1` it is `m + √(2 * v) * erfInv (2 * u - 1)`. -/
theorem quantile_gaussianReal (m : ℝ) (v : ℝ≥0) (hu : u ∈ Ioo 0 1) :
    (gaussianReal m v).quantile u = m + √(2 * (v : ℝ)) * Real.erfInv (2 * u - 1) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, Measure.quantile_dirac m hu.1 hu.2.le]
    simp
  have hc : 0 < √(2 * (v : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hy : 2 * u - 1 ∈ Ioo (-1) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  refine eq_of_forall_ge_iff fun x => ?_
  rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_gaussianReal_eq m hv, ← le_sub_iff_add_le',
    ← le_div_iff₀' hc, Real.erfInv_le_iff hy]
  constructor <;> intro h <;> linarith

/-- The quantile function of the standard Gaussian law: at every level `0 < u < 1` it is
`√2 * erfInv (2 * u - 1)`. -/
theorem quantile_gaussianReal_zero_one (hu : u ∈ Ioo 0 1) :
    (gaussianReal 0 1).quantile u = √2 * Real.erfInv (2 * u - 1) := by
  simpa using quantile_gaussianReal 0 1 hu

/-- The lower endpoint limit of a Gaussian quantile is minus infinity at positive variance and
the mean at zero variance. -/
theorem tendsto_quantile_gaussianReal_nhdsGT_zero (m : ℝ) (v : ℝ≥0) :
    Tendsto (fun u ↦ ((gaussianReal m v).quantile u : EReal)) (𝓝[>] 0)
      (𝓝 (if v = 0 then (m : EReal) else ⊥)) := by
  by_cases hv : v = 0
  · subst hv
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    simp [gaussianReal_zero_var, Measure.quantile_dirac m hu.1 hu.2.le]
  · rw [ite_eq_right hv]
    apply EReal.tendsto_coe_nhds_bot_iff.2
    refine tendsto_atBot.2 fun b ↦ ?_
    have hb : 0 < cdf (gaussianReal m v) b := by
      rw [cdf_gaussianReal_eq m hv]
      linarith [TauCeti.Real.neg_one_lt_erf ((b - m) / √(2 * (v : ℝ)))]
    filter_upwards [Ioo_mem_nhdsGT hb] with u hu
    exact (Measure.quantile_le_iff _ hu.1
      (hu.2.trans_le (cdf_le_one (gaussianReal m v) b))).2 hu.2.le

/-- The upper endpoint limit of a Gaussian quantile is plus infinity at positive variance and
the mean at zero variance. -/
theorem tendsto_quantile_gaussianReal_nhdsLT_one (m : ℝ) (v : ℝ≥0) :
    Tendsto (fun u ↦ ((gaussianReal m v).quantile u : EReal)) (𝓝[<] 1)
      (𝓝 (if v = 0 then (m : EReal) else ⊤)) := by
  by_cases hv : v = 0
  · subst hv
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    simp [gaussianReal_zero_var, Measure.quantile_dirac m hu.1 hu.2.le]
  · rw [ite_eq_right hv]
    apply EReal.tendsto_coe_nhds_top_iff.2
    refine tendsto_atTop.2 fun b ↦ ?_
    have hb : cdf (gaussianReal m v) b < 1 := by
      rw [cdf_gaussianReal_eq m hv]
      linarith [TauCeti.Real.erf_lt_one ((b - m) / √(2 * (v : ℝ)))]
    filter_upwards [Ioo_mem_nhdsLT hb] with u hu
    exact ((Measure.lt_quantile_iff _
      ((cdf_nonneg (gaussianReal m v) b).trans_lt hu.1) hu.2).2 hu.1).le

end TauCeti.Probability
