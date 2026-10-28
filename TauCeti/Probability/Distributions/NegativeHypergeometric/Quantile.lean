/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NegativeHypergeometric.Cdf
public import TauCeti.Probability.Quantile.Discrete

/-!
# Quantiles of negative hypergeometric laws

Interior quantiles of the failure count before the `r`th success are the least natural
crossings of its explicit cumulative sum. Their lower endpoint is zero; the upper endpoint
is `N - K` when a positive number of successes is awaited, and zero when no draw is needed.
Both endpoint limits include degenerate populations.

The least-crossing and endpoint arguments use the natural-cast quantile interface from
`TauCeti.Probability.Quantile.Discrete`, following the hypergeometric quantile API.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Section 6.2.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {N K r : ℕ} {u : ℝ}

/-- A natural number is the negative hypergeometric quantile exactly when it is the least
index whose explicit finite cumulative sum reaches the requested level. -/
theorem quantile_map_cast_negativeHypergeometricMeasure_eq_iff
    (hr : r ≤ K) (hK : K ≤ N) (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {i : ℕ | u ≤ ∑ j ∈ Finset.range (i + 1),
        if j ≤ N - K then
          ((j + r - 1).choose j : ℝ) * ((N - r - j).choose (K - r) : ℝ) /
            (N.choose K : ℝ)
        else 0} k := by
  let _ := isProbabilityMeasure_negativeHypergeometricMeasure hr hK
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  simp only [negativeHypergeometricMeasure_real_Iic_eq_sum hr hK]

/-- The quantile is zero precisely through the probability of drawing `r` consecutive
successes before the first failure. This also covers the Dirac boundary `r = 0`. -/
@[simp]
theorem quantile_map_cast_negativeHypergeometricMeasure_eq_zero_iff
    (hr : r ≤ K) (hK : K ≤ N) (hu : u ∈ Ioo 0 1) :
    ((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)).quantile u = 0 ↔
      u ≤ ((N - r).choose (K - r) : ℝ) / (N.choose K : ℝ) := by
  let _ := isProbabilityMeasure_negativeHypergeometricMeasure hr hK
  have hzero : (negativeHypergeometricMeasure N K r).real (Iic 0) =
      ((N - r).choose (K - r) : ℝ) / (N.choose K : ℝ) := by
    rw [negativeHypergeometricMeasure_real_Iic_eq_sum hr hK]
    simp
  simpa [IsLeast, lowerBounds, hzero] using
    (Measure.quantile_map_natCast_eq_iff (negativeHypergeometricMeasure N K r) hu 0)

/-- Above one minus the mass at the largest possible failure count, the quantile is `N - K`.
For `r = 0 < N - K`, the level hypothesis cannot hold. -/
theorem quantile_map_cast_negativeHypergeometricMeasure_eq_upper
    (hr : r ≤ K) (hK : K ≤ N) (hu : u ∈ Ioo 0 1)
    (hlevel : 1 - (negativeHypergeometricMeasure N K r).real {N - K} < u) :
    ((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)).quantile u =
      (N - K : ℕ) := by
  let _ := isProbabilityMeasure_negativeHypergeometricMeasure hr hK
  exact Measure.quantile_map_natCast_eq_of_measureReal_Iic_eq_one _ hu
    (negativeHypergeometricMeasure_real_Iic_eq_one hr hK le_rfl) hlevel

/-- As the level tends to zero from above, the quantile tends to zero failures. -/
theorem tendsto_quantile_map_cast_negativeHypergeometricMeasure_nhdsGT_zero
    (hr : r ≤ K) (hK : K ≤ N) :
    Tendsto
      (fun u ↦
        (((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hmass : 0 < ((N - r).choose (K - r) : ℝ) / (N.choose K : ℝ) := by
    apply div_pos <;> exact_mod_cast Nat.choose_pos (by omega)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min hmass zero_lt_one)] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le (min_le_right _ _)⟩
  rw [(quantile_map_cast_negativeHypergeometricMeasure_eq_zero_iff hr hK hu').2
    (hu.2.le.trans (min_le_left _ _))]
  rfl

/-- As the level tends to one from below, the quantile tends to the maximum failure count.
Waiting for zero successes instead gives the constant zero quantile. -/
theorem tendsto_quantile_map_cast_negativeHypergeometricMeasure_nhdsLT_one
    (hr : r ≤ K) (hK : K ≤ N) :
    Tendsto
      (fun u ↦
        (((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (nhdsWithin 1 (Iio 1)) (nhds (if r = 0 then 0 else (N - K : ℕ))) := by
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · simp only [ite_true]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rw [(quantile_map_cast_negativeHypergeometricMeasure_eq_zero_iff hr hK hu).2 (by
      simpa [div_self (by exact_mod_cast Nat.choose_ne_zero hK : (N.choose K : ℝ) ≠ 0)]
        using hu.2.le)]
    rfl
  · let _ := isProbabilityMeasure_negativeHypergeometricMeasure hr hK
    have hmass : 0 < (negativeHypergeometricMeasure N K r).real {N - K} := by
      rw [measureReal_def, negativeHypergeometricMeasure_singleton hr hK]
      exact ENNReal.toReal_pos
        ((negativeHypergeometricWeight_ne_zero_iff hK _).2 ⟨le_rfl, Or.inr hrpos⟩)
        (negativeHypergeometricWeight_ne_top hK r _)
    have hmass_le : (negativeHypergeometricMeasure N K r).real {N - K} ≤ 1 :=
      (measureReal_mono (subset_univ _)).trans_eq probReal_univ
    simp only [Nat.ne_of_gt hrpos, ite_false]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (sub_lt_self 1 hmass)] with u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨(sub_nonneg.mpr hmass_le).trans_lt hu.1, hu.2⟩
    rw [quantile_map_cast_negativeHypergeometricMeasure_eq_upper hr hK hu' hu.1]
    norm_cast

end TauCeti.Probability
