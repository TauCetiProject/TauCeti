/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypoexponential.Cdf
public import TauCeti.Probability.Distributions.Gamma.Quantile
import TauCeti.Probability.Distributions.Dirac

/-!
# Quantiles of hypoexponential laws

For a nonempty family of positive rates and an interior level `u`, the hypoexponential
quantile is the unique root of `cdf (hypoexponentialMeasure r) x = u`, and every such root is
positive. The quantile is continuous and strictly increasing in `u`, with one-sided limits
zero and positive infinity. The empty family is the Dirac law at zero, whose interior
quantiles are zero, and equal rates recover the Erlang quantile.

The characterization uses only the qualitative cdf, so it covers repeated rates without a
partial-fraction expansion.

## References

* S. M. Ross, *Introduction to Probability Models*, 12th ed., Academic Press (2019), Chapter 5.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {r : ι → ℝ} {u x : ℝ}

section Nonempty

variable [Nonempty ι]

/-- Every interior quantile of a nonempty hypoexponential law is positive. -/
theorem quantile_hypoexponentialMeasure_pos (hr : ∀ i, 0 < r i) (hu : u ∈ Ioo 0 1) :
    0 < (hypoexponentialMeasure r).quantile u := by
  let _ := isProbabilityMeasure_hypoexponentialMeasure hr
  exact ordConnected_Ioi.quantile_mem (ae_pos_hypoexponentialMeasure r) hu.1 hu.2

/-- The cdf at an interior hypoexponential quantile is exactly its level. -/
@[simp]
theorem cdf_quantile_hypoexponentialMeasure (hr : ∀ i, 0 < r i) (hu : u ∈ Ioo 0 1) :
    cdf (hypoexponentialMeasure r) ((hypoexponentialMeasure r).quantile u) = u :=
  Measure.cdf_quantile _ (continuous_cdf_hypoexponentialMeasure hr) hu.1 hu.2

/-- An interior hypoexponential quantile is the unique root of the cdf at that level. -/
theorem quantile_hypoexponentialMeasure_eq_iff (hr : ∀ i, 0 < r i) (hu : u ∈ Ioo 0 1) :
    (hypoexponentialMeasure r).quantile u = x ↔ cdf (hypoexponentialMeasure r) x = u := by
  refine ⟨fun h ↦ h ▸ cdf_quantile_hypoexponentialMeasure hr hu, fun hx ↦ ?_⟩
  have hx0 : 0 < x := (cdf_hypoexponentialMeasure_pos_iff hr).1 (hx ▸ hu.1)
  exact (strictMonoOn_cdf_hypoexponentialMeasure hr).injOn
    (quantile_hypoexponentialMeasure_pos hr hu).le hx0.le
    ((cdf_quantile_hypoexponentialMeasure hr hu).trans hx.symm)

/-- At a positive point, the hypoexponential quantile inverts the cdf. -/
@[simp]
theorem quantile_cdf_hypoexponentialMeasure (hr : ∀ i, 0 < r i) (hx : 0 < x) :
    (hypoexponentialMeasure r).quantile (cdf (hypoexponentialMeasure r) x) = x :=
  (quantile_hypoexponentialMeasure_eq_iff hr ⟨(cdf_hypoexponentialMeasure_pos_iff hr).2 hx,
    cdf_hypoexponentialMeasure_lt_one hr x⟩).2 rfl

/-- Interior hypoexponential quantiles increase strictly with the level. -/
theorem strictMonoOn_quantile_hypoexponentialMeasure (hr : ∀ i, 0 < r i) :
    StrictMonoOn (hypoexponentialMeasure r).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_hypoexponentialMeasure hr)

/-- The hypoexponential quantile is continuous at every interior level. -/
theorem continuousOn_quantile_hypoexponentialMeasure (hr : ∀ i, 0 < r i) :
    ContinuousOn (hypoexponentialMeasure r).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_Ici
    (strictMonoOn_cdf_hypoexponentialMeasure hr)
    (fun _ hu ↦ (quantile_hypoexponentialMeasure_pos hr hu).le)

/-- As the level decreases to zero, the hypoexponential quantile tends to zero. -/
theorem tendsto_quantile_hypoexponentialMeasure_nhdsGT_zero (hr : ∀ i, 0 < r i) :
    Tendsto (hypoexponentialMeasure r).quantile (𝓝[>] 0) (𝓝 0) := by
  let _ := isProbabilityMeasure_hypoexponentialMeasure hr
  apply EReal.tendsto_coe.1
  exact Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos _
    ((ae_pos_hypoexponentialMeasure r).mono fun _ hx ↦ hx.le)
    (fun _ hx ↦ (cdf_hypoexponentialMeasure_pos_iff hr).2 hx)

/-- As the level increases to one, the hypoexponential quantile tends to infinity. -/
theorem tendsto_quantile_hypoexponentialMeasure_nhdsLT_one (hr : ∀ i, 0 < r i) :
    Tendsto (hypoexponentialMeasure r).quantile (𝓝[<] 1) atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards [Ioo_mem_nhdsLT (cdf_hypoexponentialMeasure_lt_one hr b)] with u hu
  exact ((Measure.lt_quantile_iff _ ((cdf_nonneg _ b).trans_lt hu.1) hu.2).2 hu.1).le

/-- At a common positive rate, the hypoexponential quantile is the Erlang quantile. -/
theorem quantile_hypoexponentialMeasure_const {a : ℝ} (ha : 0 < a) (hu : u ∈ Ioo 0 1) :
    (hypoexponentialMeasure fun _ : ι ↦ a).quantile u =
      inverseRegularizedGamma (Fintype.card ι) u / a := by
  rw [hypoexponentialMeasure_const ha,
    quantile_gammaMeasure (Nat.cast_pos.2 Fintype.card_pos) ha hu]

end Nonempty

/-- The empty hypoexponential law is the Dirac law at zero, with interior quantiles zero. -/
theorem quantile_hypoexponentialMeasure_of_isEmpty [IsEmpty ι] (r : ι → ℝ)
    (hu : u ∈ Ioo 0 1) : (hypoexponentialMeasure r).quantile u = 0 := by
  rw [hypoexponentialMeasure_of_isEmpty, Measure.quantile_dirac _ hu.1 hu.2.le]

end TauCeti.Probability
