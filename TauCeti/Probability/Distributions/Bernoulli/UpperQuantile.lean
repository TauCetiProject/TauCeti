/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Bernoulli.Quantile
public import TauCeti.Probability.Quantile.Map

/-!
# Upper quantiles of Bernoulli laws

For a real Bernoulli law, the upper quantile chooses the upper endpoint of a cdf plateau.
Consequently its branch at an atom uses a strict comparison, in contrast to the weak comparison
in the lower-quantile formula.

This distinction is essential under order-reversing maps. At the cumulative mass of the lower
atom of a nondegenerate two-point law, reflection sends the lower quantile to the negative of the
upper atom, not to the negative of the original lower quantile.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

namespace TauCeti.Probability

variable {a b : ℝ} {p : unitInterval} {u : ℝ}

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
  rw [quantile_bernoulliMeasure_of_ge hba.le, upperQuantile_bernoulliMeasure_of_ge hba.le]
  · simp [hba.ne]
  · constructor <;> linarith [hp.1, hp.2]
  · constructor <;> linarith [hp.1, hp.2]

/-- At the jump level of a nondegenerate two-point Bernoulli law, reflection sends the lower
quantile to the negative of the original upper atom. -/
theorem quantile_neg_bernoulliMeasure_at_jump (hba : b < a)
    (hp : (p : ℝ) ∈ Ioo 0 1) : Ber(a, b, p).neg.quantile p = -a := by
  rw [Measure.quantile_neg hp.1 hp.2,
    upperQuantile_bernoulliMeasure_of_ge hba.le]
  · simp
  · constructor <;> linarith [hp.1, hp.2]

/-- Reflection of a nondegenerate two-point Bernoulli law demonstrates that a decreasing affine
quantile formula must use the upper quantile at the complementary level: negating the lower
quantile gives a different answer at the cdf jump. -/
theorem quantile_neg_bernoulliMeasure_ne_neg_quantile (hba : b < a)
    (hp : (p : ℝ) ∈ Ioo 0 1) :
    Ber(a, b, p).neg.quantile p ≠ -Ber(a, b, p).quantile (1 - p) := by
  rw [quantile_neg_bernoulliMeasure_at_jump hba hp,
    quantile_bernoulliMeasure_of_ge hba.le]
  · simp only [le_refl, ↓reduceIte]
    intro h
    have h' := congrArg Neg.neg h
    simp only [neg_neg] at h'
    exact hba.ne' h'
  · constructor <;> linarith [hp.1, hp.2]

end TauCeti.Probability
