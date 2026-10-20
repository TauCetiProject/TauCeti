/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedGamma.Relations
public import TauCeti.Probability.Distributions.GeneralizedGamma.Transforms
public import TauCeti.Probability.Distributions.Gumbel.Transforms
import TauCeti.Probability.Distributions.Affine

/-!
# Exponential integrability of generalized extreme-value laws

The maximum-convention generalized extreme-value law has five different exponential-moment
domains. Positive shape admits exactly the nonpositive rates; zero shape has the Gumbel
cutoff. Negative shape has all exponential moments between shapes `-1` and `0`, an open
lower cutoff at shape `-1`, and exactly the nonnegative rates below shape `-1`.

At nonzero shape the law is an affine image of a shape-one generalized gamma law.
This identity transfers the sharp generalized gamma domains, with the negative affine
slope reversing the allowed rates when the extreme-value shape is negative.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 3, for the maximum-convention extreme-value parameterization.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {m s ξ : ℝ}

/-- Positive shape admits exactly the nonpositive exponential rates. In particular, the
endpoint zero is included even when some positive polynomial moments diverge. -/
@[simp]
theorem integrableExpSet_id_generalizedExtremeValueMeasure_of_shape_pos
    (hs : 0 < s) (hξ : 0 < ξ) (m : ℝ) :
    integrableExpSet id (generalizedExtremeValueMeasure m s ξ) = Iic 0 := by
  rw [generalizedExtremeValueMeasure_eq_map_generalizedGammaMeasure hs hξ.ne',
    integrableExpSet_id_map_affine,
    integrableExpSet_id_generalizedGammaMeasure_of_lt_one zero_lt_one
      (inv_ne_zero (neg_ne_zero.mpr hξ.ne'))
      (lt_trans (inv_lt_zero.mpr (neg_lt_zero.mpr hξ)) zero_lt_one) zero_lt_one]
  ext t
  simp [div_pos hs hξ]

/-- Shapes strictly between `-1` and `0` have exponential moments at every real rate. -/
@[simp]
theorem integrableExpSet_id_generalizedExtremeValueMeasure_of_neg_one_lt
    (hs : 0 < s) (hξ : -1 < ξ) (hξ0 : ξ < 0) (m : ℝ) :
    integrableExpSet id (generalizedExtremeValueMeasure m s ξ) = univ := by
  have hc : 1 < (-ξ)⁻¹ := (one_lt_inv₀ (neg_pos.mpr hξ0)).2 (by linarith)
  rw [generalizedExtremeValueMeasure_eq_map_generalizedGammaMeasure hs hξ0.ne,
    integrableExpSet_id_map_affine,
    integrableExpSet_id_generalizedGammaMeasure_of_one_lt hc]
  exact preimage_univ

/-- Shape `-1` has the strict lower cutoff `-1 / s`. The endpoint itself is not integrable. -/
theorem integrableExpSet_id_generalizedExtremeValueMeasure_neg_one
    (hs : 0 < s) (m : ℝ) :
    integrableExpSet id (generalizedExtremeValueMeasure m s (-1)) = Ioi (-1 / s) := by
  rw [generalizedExtremeValueMeasure_eq_map_generalizedGammaMeasure hs (by norm_num),
    integrableExpSet_id_map_affine]
  norm_num only [neg_neg, inv_one, div_neg, div_one]
  rw [integrableExpSet_id_generalizedGammaMeasure_one zero_lt_one zero_lt_one]
  ext t
  simp only [mem_preimage, mem_Iio, inv_one, mem_Ioi]
  rw [div_lt_iff₀ hs]
  constructor <;> intro h <;> nlinarith

/-- Shapes below `-1` admit exactly the nonnegative exponential rates. -/
@[simp]
theorem integrableExpSet_id_generalizedExtremeValueMeasure_of_lt_neg_one
    (hs : 0 < s) (hξ : ξ < -1) (m : ℝ) :
    integrableExpSet id (generalizedExtremeValueMeasure m s ξ) = Ici 0 := by
  have hξ0 : ξ < 0 := by linarith
  have hc : (-ξ)⁻¹ < 1 := (inv_lt_one₀ (neg_pos.mpr hξ0)).2 (by linarith)
  rw [generalizedExtremeValueMeasure_eq_map_generalizedGammaMeasure hs hξ0.ne,
    integrableExpSet_id_map_affine,
    integrableExpSet_id_generalizedGammaMeasure_of_lt_one zero_lt_one
      (inv_ne_zero (neg_ne_zero.mpr hξ0.ne)) hc zero_lt_one]
  ext t
  simp [div_neg_of_pos_of_neg hs hξ0]

/-- The exact exponential-integrability domain in all five shape regimes at positive scale.
Both finite cutoffs are excluded, while the heavy-tail boundaries include rate zero. -/
@[simp]
theorem integrableExpSet_id_generalizedExtremeValueMeasure (hs : 0 < s) (m ξ : ℝ) :
    integrableExpSet id (generalizedExtremeValueMeasure m s ξ) =
      if 0 < ξ then Iic 0 else if ξ = 0 then Iio (1 / s)
      else if -1 < ξ then univ else if ξ = -1 then Ioi (-1 / s) else Ici 0 := by
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · rcases lt_trichotomy ξ (-1) with hξ1 | rfl | hξ1
    · simp [integrableExpSet_id_generalizedExtremeValueMeasure_of_lt_neg_one hs hξ1,
        hξ.ne, not_lt.mpr hξ.le, hξ1.ne, not_lt.mpr hξ1.le]
    · simp [integrableExpSet_id_generalizedExtremeValueMeasure_neg_one hs]
    · simp [integrableExpSet_id_generalizedExtremeValueMeasure_of_neg_one_lt hs hξ1 hξ,
        hξ.ne, not_lt.mpr hξ.le, hξ1]
  · simp [integrableExpSet_id_gumbelMeasure hs]
  · simp [integrableExpSet_id_generalizedExtremeValueMeasure_of_shape_pos hs hξ, hξ]

end TauCeti.Probability
