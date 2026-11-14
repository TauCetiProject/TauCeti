/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Bernoulli.Cdf
public import TauCeti.Probability.Distributions.Bernoulli.Support
public import TauCeti.Probability.Quantile

/-!
# Quantiles of Bernoulli laws

A real Bernoulli law `Ber(a, b, p)` puts mass `p` on `a` and mass `1 - p` on `b`. At an interior
probability level `u`, its lower quantile is the lower atom through the cumulative mass of that
atom, and the upper atom above it; the level at the cumulative jump belongs to the lower branch.
The formula is stated separately for the two orders of the atoms and includes coincident atoms
and the Dirac boundaries `p = 0` and `p = 1`. For the standard law `Ber(1, 0, p)` the quantile is
zero when `u ≤ 1 - p` and one otherwise.

The one-sided endpoint limits in `EReal` are the endpoints of the actual support: at the Dirac
boundaries both are the single atom carrying all the mass, and otherwise they are the minimum
and the maximum of the two atoms. These need no order between the atoms, and they specialise
`MeasureTheory.Measure.tendsto_quantile_nhdsGT_zero` and
`MeasureTheory.Measure.tendsto_quantile_nhdsLT_one`, which identify the one-sided limits of the
lower quantile at `0` and `1` with the infimum and supremum of the support of any probability
measure on the real line.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ProbabilityTheory

namespace TauCeti.Probability

variable {a b : ℝ} {p : unitInterval} {u : ℝ}

/-- The lower quantile of a Bernoulli law whose failure atom `b` lies below its success atom `a`
is `b` through cumulative mass `1 - p` and `a` above it, including coincident atoms and the
probability-zero and probability-one boundaries. -/
@[simp]
theorem quantile_bernoulliMeasure_of_ge (hba : b ≤ a) (hu : u ∈ Ioo 0 1) :
    Ber(a, b, p).quantile u = if u ≤ 1 - (p : ℝ) then b else a := by
  refine eq_of_forall_lt_iff fun x ↦ ?_
  rw [Measure.lt_quantile_iff _ hu.1 hu.2, cdf_bernoulliMeasure]
  split_ifs <;> grind

/-- The lower quantile of a Bernoulli law whose success atom `a` lies below its failure atom `b`
is `a` through cumulative mass `p` and `b` above it, including coincident atoms and the
probability-zero and probability-one boundaries. -/
@[simp]
theorem quantile_bernoulliMeasure_of_le (hab : a ≤ b) (hu : u ∈ Ioo 0 1) :
    Ber(a, b, p).quantile u = if u ≤ (p : ℝ) then a else b := by
  refine eq_of_forall_lt_iff fun x ↦ ?_
  rw [Measure.lt_quantile_iff _ hu.1 hu.2, cdf_bernoulliMeasure]
  split_ifs <;> grind

/-- As the level tends to zero from above, the Bernoulli quantile tends to the lower endpoint
of its support: the single atom at success probability zero or one, and the smaller atom
otherwise. -/
theorem tendsto_quantile_bernoulliMeasure_nhdsGT_zero (a b : ℝ) (p : unitInterval) :
    Tendsto (fun u ↦ (Ber(a, b, p).quantile u : EReal)) (𝓝[>] 0)
      (𝓝 ↑(if p = 0 then b else if p = 1 then a else min a b)) := by
  convert Measure.tendsto_quantile_nhdsGT_zero Ber(a, b, p) using 2
  -- Compute the support endpoint from the explicit support of the Bernoulli law.
  rw [iInf_subtype'', support_bernoulliMeasure]
  split_ifs
  · simp
  · simp
  · rw [iInf_pair, EReal.coe_strictMono.monotone.map_min]

/-- As the level tends to one from below, the Bernoulli quantile tends to the upper endpoint
of its support: the single atom at success probability zero or one, and the larger atom
otherwise. -/
theorem tendsto_quantile_bernoulliMeasure_nhdsLT_one (a b : ℝ) (p : unitInterval) :
    Tendsto (fun u ↦ (Ber(a, b, p).quantile u : EReal)) (𝓝[<] 1)
      (𝓝 ↑(if p = 0 then b else if p = 1 then a else max a b)) := by
  convert Measure.tendsto_quantile_nhdsLT_one Ber(a, b, p) using 2
  -- Compute the support endpoint from the explicit support of the Bernoulli law.
  rw [iSup_subtype'', support_bernoulliMeasure]
  split_ifs
  · simp
  · simp
  · rw [iSup_pair, EReal.coe_strictMono.monotone.map_max]

end TauCeti.Probability
