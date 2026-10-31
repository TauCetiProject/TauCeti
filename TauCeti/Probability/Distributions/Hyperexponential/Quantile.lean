/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hyperexponential.Cdf
public import TauCeti.Probability.Quantile
import TauCeti.Probability.Distributions.Exponential.Quantile

/-!
# Quantiles of hyperexponential laws

At an interior probability level `u`, the hyperexponential quantile is the unique positive
solution of `∑ i, p.weights i * exp (-(r i * x)) = 1 - u`. It is continuous and strictly
increasing in `u`, with one-sided limits zero and positive infinity. Equal active rates
recover the exponential quantile, even when inactive rates differ.

## References

* S. Asmussen, *Applied Probability and Queues*, 2nd ed., Springer (2003), Chapter III, §4.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {p : Convexity.StdSimplex ℝ≥0 ι} {r : ι → ℝ} {u x : ℝ}

/-- Every interior hyperexponential quantile is strictly positive. -/
theorem quantile_hyperexponentialMeasure_pos
    (hr : ∀ i, 0 < p.weights i → 0 < r i) (hu : u ∈ Ioo 0 1) :
    0 < (hyperexponentialMeasure p r).quantile u := by
  let _ := isProbabilityMeasure_hyperexponentialMeasure hr
  exact ordConnected_Ioi.quantile_mem (ae_pos_hyperexponentialMeasure p r) hu.1 hu.2

/-- The finite survival sum at an interior quantile is exactly one minus its level. -/
@[simp]
theorem sum_exp_quantile_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i) (hu : u ∈ Ioo 0 1) :
    ∑ i, (p.weights i : ℝ) * exp (-(r i * (hyperexponentialMeasure p r).quantile u)) =
      1 - u := by
  let _ := isProbabilityMeasure_hyperexponentialMeasure hr
  have hroot := Measure.cdf_quantile (hyperexponentialMeasure p r)
    (Measure.continuous_cdf_of_noAtoms _) hu.1 hu.2
  rw [cdf_hyperexponentialMeasure_eq hr,
    ite_eq_right (quantile_hyperexponentialMeasure_pos hr hu).not_ge] at hroot
  linarith

/-- The quantile is the unique positive root of the explicit finite survival sum. -/
theorem quantile_hyperexponentialMeasure_eq_iff
    (hr : ∀ i, 0 < p.weights i → 0 < r i) (hu : u ∈ Ioo 0 1) :
    (hyperexponentialMeasure p r).quantile u = x ↔
      0 < x ∧ ∑ i, (p.weights i : ℝ) * exp (-(r i * x)) = 1 - u := by
  constructor
  · rintro rfl
    exact ⟨quantile_hyperexponentialMeasure_pos hr hu,
      sum_exp_quantile_hyperexponentialMeasure hr hu⟩
  · rintro ⟨hx, hsum⟩
    apply (strictMonoOn_cdf_hyperexponentialMeasure hr).injOn
      (quantile_hyperexponentialMeasure_pos hr hu).le hx.le
    rw [cdf_hyperexponentialMeasure_eq hr, cdf_hyperexponentialMeasure_eq hr,
      ite_eq_right (quantile_hyperexponentialMeasure_pos hr hu).not_ge, ite_eq_right hx.not_ge,
      sum_exp_quantile_hyperexponentialMeasure hr hu, hsum]

/-- Interior hyperexponential quantiles increase strictly with the probability level. -/
theorem strictMonoOn_quantile_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    StrictMonoOn (hyperexponentialMeasure p r).quantile (Ioo 0 1) := by
  let _ := isProbabilityMeasure_hyperexponentialMeasure hr
  exact Measure.strictMonoOn_quantile _ (Measure.continuous_cdf_of_noAtoms _)

/-- The hyperexponential quantile is continuous at every interior probability level. -/
theorem continuousOn_quantile_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    ContinuousOn (hyperexponentialMeasure p r).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_Ioi
    ((strictMonoOn_cdf_hyperexponentialMeasure hr).mono Ioi_subset_Ici_self)
    (fun _ hu ↦ quantile_hyperexponentialMeasure_pos hr hu)

/-- As the level decreases to zero, the quantile tends to the lower support endpoint zero. -/
theorem tendsto_quantile_hyperexponentialMeasure_nhdsGT_zero
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    Tendsto (fun u ↦ ((hyperexponentialMeasure p r).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  let _ := isProbabilityMeasure_hyperexponentialMeasure hr
  exact Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos _
    ((ae_pos_hyperexponentialMeasure p r).mono fun _ hx ↦ hx.le)
    (fun _ hx ↦ (cdf_hyperexponentialMeasure_pos_iff hr).2 hx)

/-- As the level increases to one, the quantile tends to positive infinity. -/
theorem tendsto_quantile_hyperexponentialMeasure_nhdsLT_one
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    Tendsto (fun u ↦ ((hyperexponentialMeasure p r).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  rw [EReal.tendsto_coe_nhds_top_iff]
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards [Ioo_mem_nhdsLT (cdf_hyperexponentialMeasure_lt_one hr b)] with u hu
  exact ((Measure.lt_quantile_iff _ ((cdf_nonneg _ b).trans_lt hu.1) hu.2).2 hu.1).le

/-- A common positive active rate gives the exponential quantile; inactive rates are arbitrary. -/
theorem quantile_hyperexponentialMeasure_of_const {a : ℝ} (ha : 0 < a)
    (hr : ∀ i, 0 < p.weights i → r i = a) (hu : u ∈ Ioo 0 1) :
    (hyperexponentialMeasure p r).quantile u = -log (1 - u) / a := by
  rw [hyperexponentialMeasure_congr hr, hyperexponentialMeasure_const, quantile_expMeasure ha hu]

end TauCeti.Probability
