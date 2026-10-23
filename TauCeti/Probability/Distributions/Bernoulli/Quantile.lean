/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Bernoulli.Cdf
public import TauCeti.Probability.Quantile
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of Bernoulli laws

At an interior probability level `u`, the lower quantile of the real Bernoulli law is zero
when `u ≤ 1 - p`, and one otherwise. In particular the level at the cumulative jump belongs
to the lower branch. The formula includes the Dirac boundaries `p = 0` and `p = 1`.

The one-sided endpoint limits in `EReal` are the endpoints of the actual support: the lower
endpoint is one at `p = 1` and zero otherwise, while the upper endpoint is zero at `p = 0`
and one otherwise. The proofs use the cdf formula and the measure-level quantile adjunction.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ProbabilityTheory

namespace TauCeti.Probability

variable {p : unitInterval} {u : ℝ}

/-- The lower quantile of a Bernoulli law is zero through cumulative mass `1 - p` and one
above it, including the probability-zero and probability-one boundaries. -/
@[simp]
theorem quantile_bernoulliMeasure (hu : u ∈ Ioo 0 1) :
    Ber((1 : ℝ), 0, p).quantile u = if u ≤ 1 - (p : ℝ) then 0 else 1 := by
  refine eq_of_forall_lt_iff fun x ↦ ?_
  rw [Measure.lt_quantile_iff _ hu.1 hu.2, cdf_bernoulliMeasure]
  split_ifs <;> grind

/-- As the level tends to zero from above, the Bernoulli quantile tends to the lower endpoint
of its support, including the singleton support at success probability one. -/
theorem tendsto_quantile_bernoulliMeasure_nhdsGT_zero (p : unitInterval) :
    Tendsto (fun u ↦ (Ber((1 : ℝ), 0, p).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (if p = 1 then 1 else 0)) := by
  refine tendsto_const_nhds.congr' ?_
  by_cases hp : p = 1
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    rw [quantile_bernoulliMeasure hu]
    simp [hp, not_le.mpr hu.1]
  · have hp' : (p : ℝ) < 1 := unitInterval.coe_lt_one.mpr
      (unitInterval.lt_one_iff_ne_one.mpr hp)
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hp')] with u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 :=
      ⟨hu.1, hu.2.trans_le (unitInterval.one_sub_le_one p)⟩
    rw [quantile_bernoulliMeasure hu', ite_eq_left hu.2.le, ite_eq_right hp]
    rfl

/-- As the level tends to one from below, the Bernoulli quantile tends to the upper endpoint
of its support, including the singleton support at success probability zero. -/
theorem tendsto_quantile_bernoulliMeasure_nhdsLT_one (p : unitInterval) :
    Tendsto (fun u ↦ (Ber((1 : ℝ), 0, p).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if p = 0 then 0 else 1)) := by
  refine tendsto_const_nhds.congr' ?_
  by_cases hp : p = 0
  · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rw [quantile_bernoulliMeasure hu]
    simp [hp, hu.2.le]
  · have hp' : 0 < (p : ℝ) := unitInterval.coe_pos.mpr
      (unitInterval.pos_iff_ne_zero.mpr hp)
    filter_upwards [Ioo_mem_nhdsLT (sub_lt_self 1 hp')] with u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 :=
      ⟨(unitInterval.one_sub_nonneg p).trans_lt hu.1, hu.2⟩
    rw [quantile_bernoulliMeasure hu', ite_eq_right (not_le.mpr hu.1), ite_eq_right hp]
    rfl

end TauCeti.Probability
