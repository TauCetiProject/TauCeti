/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.BetaNegativeBinomial.Cdf
public import TauCeti.Probability.Quantile.Discrete

/-!
# Quantiles of beta-negative-binomial laws

Interior lower quantiles are the least natural counts whose explicit Gamma–Beta cumulative
sums reach the level. Equality at a cumulative jump selects the smaller count. The initial
constant segment includes the entire mass at zero. The endpoint limits are zero and positive
infinity at positive shape; at shape zero the quantile is constantly zero.

The proofs specialize the natural-cast quantile API and follow the endpoint argument for
Yule–Simon laws.

## Reference

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {r a b u : ℝ}

/-- A natural count is the lower quantile exactly when it is the least crossing of the
explicit Gamma–Beta cumulative sum, including the shape-zero boundary. -/
theorem quantile_map_cast_betaNegativeBinomialMeasure_eq_iff (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {i : ℕ | u ≤ ∑ j ∈ Finset.Iic i,
        betaNegativeBinomialWeightReal r a b j} k := by
  have := isProbabilityMeasure_betaNegativeBinomialMeasure hr ha hb
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  simp only [betaNegativeBinomialMeasure_real_Iic hr ha hb]

/-- The lower quantile is zero exactly through the mass at zero. -/
@[simp]
theorem quantile_map_cast_betaNegativeBinomialMeasure_eq_zero_iff (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) (hu : u ∈ Ioo 0 1) :
    ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)).quantile u = 0 ↔
      u ≤ betaNegativeBinomialWeightReal r a b 0 := by
  simpa [IsLeast, lowerBounds, ← Nat.range_succ_eq_Iic] using
    (quantile_map_cast_betaNegativeBinomialMeasure_eq_iff hr ha hb hu 0)

/-- At shape zero every interior quantile is zero. -/
@[simp]
theorem quantile_map_cast_betaNegativeBinomialMeasure_zero (ha : 0 < a) (hb : 0 < b)
    (hu : u ∈ Ioo 0 1) :
    ((betaNegativeBinomialMeasure 0 a b).map (Nat.cast : ℕ → ℝ)).quantile u = 0 := by
  rw [quantile_map_cast_betaNegativeBinomialMeasure_eq_zero_iff le_rfl ha hb hu]
  simpa using hu.2.le

/-- Quantiles tend to zero as the level tends to zero from above, for every valid shape. -/
theorem tendsto_quantile_map_cast_betaNegativeBinomialMeasure_nhdsGT_zero
    (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun u ↦
      (((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  have := isProbabilityMeasure_betaNegativeBinomialMeasure hr ha hb
  have hmass : 0 < betaNegativeBinomialWeightReal r a b 0 :=
    (betaNegativeBinomialWeightReal_pos_iff hr ha hb 0).2 (Or.inl rfl)
  have hmass_le : betaNegativeBinomialWeightReal r a b 0 ≤ 1 := by
    rw [← betaNegativeBinomialMeasure_real_singleton hr ha hb]
    exact (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hmass] with u hu
  rw [(quantile_map_cast_betaNegativeBinomialMeasure_eq_zero_iff hr ha hb
    ⟨hu.1, hu.2.trans_le hmass_le⟩).2 hu.2.le]
  rfl

/-- Quantiles tend to positive infinity at level one for positive shape, and to zero for
the shape-zero Dirac law. -/
theorem tendsto_quantile_map_cast_betaNegativeBinomialMeasure_nhdsLT_one
    (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun u ↦
      (((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if r = 0 then 0 else ⊤)) := by
  by_cases hr0 : r = 0
  · subst r
    simp only [ite_true]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with u hu
    rw [quantile_map_cast_betaNegativeBinomialMeasure_zero ha hb hu]
    rfl
  rw [ite_eq_right hr0, EReal.tendsto_coe_nhds_top_iff]
  have := isProbabilityMeasure_betaNegativeBinomialMeasure hr ha hb
  refine tendsto_atTop.2 fun x ↦ ?_
  have hx : cdf ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) x < 1 := by
    by_cases hx0 : 0 ≤ x
    · rw [Measure.cdf_map_natCast _ hx0]
      exact betaNegativeBinomialMeasure_real_Iic_lt_one (lt_of_le_of_ne hr (Ne.symm hr0))
        ha hb _
    · rw [cdf_map_cast_betaNegativeBinomialMeasure_of_neg hr ha hb (lt_of_not_ge hx0)]
      exact zero_lt_one
  filter_upwards [Ioo_mem_nhdsLT hx] with u hu
  exact ((Measure.lt_quantile_iff _ ((cdf_nonneg _ _).trans_lt hu.1) hu.2).2 hu.1).le

end TauCeti.Probability
