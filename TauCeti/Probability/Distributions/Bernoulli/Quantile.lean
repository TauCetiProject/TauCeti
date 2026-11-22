/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Bernoulli.Cdf
public import TauCeti.Probability.Distributions.Bernoulli.Support
public import TauCeti.Probability.Quantile
public import TauCeti.Probability.Quantile.Map

/-!
# Lower and upper quantiles of Bernoulli laws

A real Bernoulli law `Ber(a, b, p)` puts mass `p` on `a` and mass `1 - p` on `b`. At an interior
probability level `u`, its lower quantile assigns the cumulative jump to the lower branch, while
its upper quantile assigns it to the upper branch. The formulas are stated separately for the two
orders of the atoms and include coincident atoms and the Dirac boundaries `p = 0` and `p = 1`.
For a nondegenerate two-point law, the quantiles therefore differ at the jump, and reflection
sends the lower quantile there to the negative of the original upper atom.

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

/-- The upper quantile of a Bernoulli law whose failure atom `b` lies below its success atom `a`
is `b` strictly below cumulative mass `1 - p` and `a` from that level onwards. This includes
coincident atoms and the probability-zero and probability-one boundaries. -/
@[simp]
theorem upperQuantile_bernoulliMeasure_of_ge (hba : b ≤ a) (hu : u ∈ Ioo 0 1) :
    Ber(a, b, p).upperQuantile u = if u < 1 - (p : ℝ) then b else a := by
  refine eq_of_forall_le_iff fun x ↦ ?_
  rw [Measure.le_upperQuantile_iff _ hu.1 hu.2,
    bernoulliMeasure_real_apply p measurableSet_Iio]
  simp only [mem_Iio, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
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

/-- The upper quantile of a Bernoulli law whose success atom `a` lies below its failure atom `b`
is `a` strictly below cumulative mass `p` and `b` from that level onwards. This includes
coincident atoms and the probability-zero and probability-one boundaries. -/
@[simp]
theorem upperQuantile_bernoulliMeasure_of_le (hab : a ≤ b) (hu : u ∈ Ioo 0 1) :
    Ber(a, b, p).upperQuantile u = if u < (p : ℝ) then a else b := by
  refine eq_of_forall_le_iff fun x ↦ ?_
  rw [Measure.le_upperQuantile_iff _ hu.1 hu.2,
    bernoulliMeasure_real_apply p measurableSet_Iio]
  simp only [mem_Iio, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  split_ifs <;> grind

/-- At the cdf jump of a nondegenerate two-point Bernoulli law, the lower and upper quantiles
are the two distinct atoms. -/
theorem quantile_ne_upperQuantile_bernoulliMeasure_at_jump (hba : b < a)
    (hp : (p : ℝ) ∈ Ioo 0 1) :
    Ber(a, b, p).quantile (1 - p) ≠ Ber(a, b, p).upperQuantile (1 - p) := by
  have hp' := Set.Ioo.one_sub_mem hp
  rw [quantile_bernoulliMeasure_of_ge hba.le, upperQuantile_bernoulliMeasure_of_ge hba.le]
  · simp [hba.ne]
  · exact hp'
  · exact hp'

/-- At an interior jump level of a two-point Bernoulli law whose failure atom is no greater than
its success atom, reflection sends the lower quantile to the negative of the original upper
atom. -/
theorem quantile_neg_bernoulliMeasure_at_jump (hba : b ≤ a)
    (hp : (p : ℝ) ∈ Ioo 0 1) : Ber(a, b, p).neg.quantile p = -a := by
  rw [Measure.quantile_neg hp.1 hp.2,
    upperQuantile_bernoulliMeasure_of_ge hba]
  · simp
  · exact Set.Ioo.one_sub_mem hp

/-- Reflection of a nondegenerate two-point Bernoulli law demonstrates that a decreasing affine
quantile formula must use the upper quantile at the complementary level: negating the lower
quantile gives a different answer at the cdf jump. -/
theorem quantile_neg_bernoulliMeasure_ne_neg_quantile (hba : b < a)
    (hp : (p : ℝ) ∈ Ioo 0 1) :
    Ber(a, b, p).neg.quantile p ≠ -Ber(a, b, p).quantile (1 - p) := by
  rw [quantile_neg_bernoulliMeasure_at_jump hba.le hp,
    quantile_bernoulliMeasure_of_ge hba.le]
  · simp [hba.ne']
  · exact Set.Ioo.one_sub_mem hp

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
