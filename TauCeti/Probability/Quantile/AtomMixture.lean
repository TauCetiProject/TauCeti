/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.AtomMixture
public import TauCeti.Probability.Distributions.Dirac

/-!
# Quantiles of mixtures with an atom at zero

This file computes the quantile of `Measure.atomMixture μ 0 w` when the base probability law
`μ` is carried by the nonnegative half-line. The quantile stays at zero through the combined
mass of the added atom and any atom already present at zero. Above that mass, it is the quantile
of `μ` at the probability level obtained by removing and rescaling the added weight.

These formulas provide the quantile step needed for zero-inflated and hurdle distributions.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal unitInterval

namespace MeasureTheory.Measure

open TauCeti.Probability

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {w : unitInterval} {u : ℝ}

/-- Up to the combined atom at zero, the quantile of a nonnegative atom mixture is zero. -/
theorem quantile_atomMixture_zero_eq_zero (hμ : μ (Iio 0) = 0)
    (hu : u ∈ Ioo 0 1)
    (hle : u ≤ (w : ℝ) + (1 - (w : ℝ)) * μ.real {0}) :
    (μ.atomMixture 0 w).quantile u = 0 := by
  calc
    (μ.atomMixture 0 w).quantile u = (dirac 0).quantile u :=
      quantile_eq_of_le_cdf_iff _ _ fun x => by
        by_cases hx : 0 ≤ x
        · rw [TauCeti.Probability.cdf_dirac, ite_eq_left hx]
          constructor
          · exact fun _ => hu.2.le
          · exact fun _ => hle.trans <| by
              rw [← cdf_atomMixture_zero μ hμ w]
              exact monotone_cdf _ hx
        · have hx' : x < 0 := lt_of_not_ge hx
          rw [TauCeti.Probability.cdf_dirac, ite_eq_right hx,
            TauCeti.Probability.cdf_atomMixture, ite_eq_right hx,
            cdf_eq_zero_of_lt_of_measure_Iio_eq_zero μ hμ hx']
          simp only [mul_zero, add_zero]
    _ = 0 := quantile_dirac 0 hu.1 hu.2.le

/-- Above the combined atom at zero, remove the added weight and rescale the probability level to
obtain the quantile of the nonnegative base law. -/
theorem quantile_atomMixture_zero_of_lt (hμ : μ (Iio 0) = 0) (hu : u ∈ Ioo 0 1)
    (hlt : (w : ℝ) + (1 - (w : ℝ)) * μ.real {0} < u) :
    (μ.atomMixture 0 w).quantile u =
      μ.quantile ((u - (w : ℝ)) / (1 - (w : ℝ))) := by
  have hw : w ≠ 1 := by
    intro hw
    subst w
    norm_num at hlt
    exact (lt_asymm hlt hu.2).elim
  have hwlt : (w : ℝ) < 1 := unitInterval.lt_one_iff_ne_one.mpr hw
  have hden : 0 < 1 - (w : ℝ) := sub_pos.mpr hwlt
  have hw_le_u : (w : ℝ) < u := by
    have hnonneg : 0 ≤ (1 - (w : ℝ)) * μ.real {0} :=
      mul_nonneg (sub_nonneg.mpr (unitInterval.le_one w)) measureReal_nonneg
    linarith
  have hv0 : 0 < (u - (w : ℝ)) / (1 - (w : ℝ)) := div_pos (sub_pos.mpr hw_le_u) hden
  apply quantile_eq_of_le_cdf_iff
  intro x
  by_cases hx : 0 ≤ x
  · rw [TauCeti.Probability.cdf_atomMixture, ite_eq_left hx, mul_one,
      div_le_iff₀ hden]
    constructor <;> intro h <;> nlinarith
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [TauCeti.Probability.cdf_atomMixture, ite_eq_right hx,
      cdf_eq_zero_of_lt_of_measure_Iio_eq_zero μ hμ hx']
    simp only [mul_zero, add_zero]
    exact iff_of_false (not_le_of_gt hu.1) (not_le_of_gt hv0)

/-- The quantile of a nonnegative atom mixture: it is zero through the combined atom at zero and
otherwise is the rescaled quantile of the base law. This includes the pure-atom endpoint `w = 1`.
-/
theorem quantile_atomMixture_zero (hμ : μ (Iio 0) = 0) (w : unitInterval)
    (hu : u ∈ Ioo 0 1) :
    (μ.atomMixture 0 w).quantile u =
      if u ≤ (w : ℝ) + (1 - (w : ℝ)) * μ.real {0} then 0
      else μ.quantile ((u - (w : ℝ)) / (1 - (w : ℝ))) := by
  split_ifs with h
  · exact quantile_atomMixture_zero_eq_zero hμ hu h
  · exact quantile_atomMixture_zero_of_lt hμ hu (lt_of_not_ge h)

end MeasureTheory.Measure
