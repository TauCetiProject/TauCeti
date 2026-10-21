/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.AtomMixture
public import TauCeti.Probability.Distributions.Dirac

/-!
# Quantiles of mixtures with an atom at a support boundary

This file computes the quantile of `Measure.atomMixture μ c w` when the base probability law
`μ` has no mass below `c`. The quantile stays at `c` through the combined mass of the added atom
and any atom already present at `c`. Above that mass, it is the quantile of `μ` at the probability
level obtained by removing and rescaling the added weight.

These formulas provide the quantile step needed for zero-inflated and hurdle distributions.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal unitInterval

namespace MeasureTheory.Measure

open TauCeti.Probability

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℝ} {w : unitInterval} {u : ℝ}

/-- Up to the combined atom at a lower support boundary, the quantile of an atom mixture is that
boundary point. -/
theorem quantile_atomMixture_eq_atom (hμ : μ (Iio c) = 0)
    (hu : 0 < u)
    (hle : u ≤ (w : ℝ) + (1 - (w : ℝ)) * μ.real {c}) :
    (μ.atomMixture c w).quantile u = c := by
  have hu_one : u ≤ 1 := hle.trans <| by
    calc
      (w : ℝ) + (1 - (w : ℝ)) * μ.real {c} ≤
          (w : ℝ) + (1 - (w : ℝ)) * 1 :=
        by
          simpa only [add_comm] using
            add_le_add_left
              (mul_le_mul_of_nonneg_left measureReal_le_one
                (sub_nonneg.mpr (unitInterval.le_one w))) (w : ℝ)
      _ = 1 := by ring
  calc
    (μ.atomMixture c w).quantile u = (dirac c).quantile u :=
      quantile_eq_of_le_cdf_iff _ _ fun x => by
        by_cases hx : c ≤ x
        · rw [TauCeti.Probability.cdf_dirac, ite_eq_left hx]
          constructor
          · exact fun _ => hu_one
          · exact fun _ => hle.trans <| by
              rw [← cdf_atomMixture_atom μ c hμ w]
              exact monotone_cdf _ hx
        · have hx' : x < c := lt_of_not_ge hx
          rw [TauCeti.Probability.cdf_dirac, ite_eq_right hx,
            μ.cdf_atomMixture, ite_eq_right hx,
            cdf_eq_zero_of_lt_of_measure_Iio_eq_zero μ hμ hx']
          simp only [mul_zero, add_zero]
    _ = c := quantile_dirac c hu hu_one

/-- Above the combined atom at a lower support boundary, remove the added weight and rescale the
probability level to obtain the quantile of the base law. -/
theorem quantile_atomMixture_of_lt (hμ : μ (Iio c) = 0) (hu : u ≤ 1)
    (hlt : (w : ℝ) + (1 - (w : ℝ)) * μ.real {c} < u) :
    (μ.atomMixture c w).quantile u =
      μ.quantile ((u - (w : ℝ)) / (1 - (w : ℝ))) := by
  have hw : w ≠ 1 := by
    intro hw
    subst w
    norm_num at hlt
    exact (not_lt_of_ge hu) hlt
  have hwlt : (w : ℝ) < 1 := unitInterval.lt_one_iff_ne_one.mpr hw
  have hden : 0 < 1 - (w : ℝ) := sub_pos.mpr hwlt
  have hw_le_u : (w : ℝ) < u := by
    have hnonneg : 0 ≤ (1 - (w : ℝ)) * μ.real {c} :=
      mul_nonneg (sub_nonneg.mpr (unitInterval.le_one w)) measureReal_nonneg
    linarith
  have hu0 : 0 < u := (unitInterval.nonneg w).trans_lt hw_le_u
  have hv0 : 0 < (u - (w : ℝ)) / (1 - (w : ℝ)) := div_pos (sub_pos.mpr hw_le_u) hden
  apply quantile_eq_of_le_cdf_iff
  intro x
  by_cases hx : c ≤ x
  · rw [μ.cdf_atomMixture, ite_eq_left hx, mul_one,
      div_le_iff₀ hden]
    constructor <;> intro h <;> nlinarith
  · have hx' : x < c := lt_of_not_ge hx
    rw [μ.cdf_atomMixture, ite_eq_right hx,
      cdf_eq_zero_of_lt_of_measure_Iio_eq_zero μ hμ hx']
    simp only [mul_zero, add_zero]
    exact iff_of_false (not_le_of_gt hu0) (not_le_of_gt hv0)

/-- The quantile of an atom mixture at a lower support boundary: it is the boundary point through
the combined atom there and otherwise is the rescaled quantile of the base law. This includes the
pure-atom endpoint `w = 1`. -/
theorem quantile_atomMixture (hμ : μ (Iio c) = 0) (w : unitInterval)
    (hu : u ∈ Ioc 0 1) :
    (μ.atomMixture c w).quantile u =
      if u ≤ (w : ℝ) + (1 - (w : ℝ)) * μ.real {c} then c
      else μ.quantile ((u - (w : ℝ)) / (1 - (w : ℝ))) := by
  split_ifs with h
  · exact quantile_atomMixture_eq_atom hμ hu.1 h
  · exact quantile_atomMixture_of_lt hμ hu.2 (lt_of_not_ge h)

end MeasureTheory.Measure
