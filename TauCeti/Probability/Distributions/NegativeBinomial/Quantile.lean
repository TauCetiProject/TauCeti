/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NegativeBinomial.Cdf
public import TauCeti.Probability.Quantile.Discrete
public import Mathlib.Topology.Instances.EReal.Lemmas

import TauCeti.Probability.Distributions.Dirac

/-!
# Quantiles of negative-binomial laws

For positive shape and valid success probability, the lower quantile of the real-cast
negative-binomial law is the least natural index whose regularized-incomplete-beta cumulative
mass reaches the requested level. This characterization includes success probability one, when
the first crossing is zero. Shape zero is handled separately by its Dirac law.

Every valid law has lower support endpoint zero. Its upper endpoint is positive infinity exactly
when the shape is positive and the success probability is strictly below one; at either Dirac
boundary the upper endpoint is zero.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {r p u : ℝ}

/-- A natural number is the lower quantile of a positive-shape negative-binomial law exactly
when it is the least index whose incomplete-beta cumulative mass reaches the level. -/
@[simp]
theorem quantile_map_cast_negativeBinomialMeasure_eq_iff (hr : 0 < r) (hp : 0 < p)
    (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {j : ℕ | u ≤ regularizedIncompleteBeta r (j + 1) p} k := by
  by_cases hp1 : p ≤ 1
  · let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1
    rw [Measure.quantile_map_natCast_eq_iff _ hu]
    simp only [negativeBinomialMeasure_real_Iic hr hp hp1]
  · have hI (j : ℕ) : regularizedIncompleteBeta r (j + 1) p = 1 :=
      regularizedIncompleteBeta_eq_one_of_one_le hr.le (by positivity) (not_le.1 hp1).le
    rw [negativeBinomialMeasure_eq_zero_of_invalid (fun h ↦ hp1 h.2.2), Measure.map_zero,
      Measure.quantile_zero]
    simp only [hI, hu.2.le, ofPred_true]
    rw [isLeast_univ_iff, isBot_iff_eq_bot, Nat.bot_eq_zero]
    exact_mod_cast eq_comm

/-- At shape zero, every valid negative-binomial law is concentrated at zero, so its lower
quantiles are zero, at every level and also at invalid success probabilities. -/
theorem quantile_map_cast_negativeBinomialMeasure_zero :
    ((negativeBinomialMeasure 0 p).map (Nat.cast : ℕ → ℝ)).quantile u = 0 := by
  by_cases h : 0 < p ∧ p ≤ 1
  · rw [negativeBinomialMeasure_zero h.1 h.2, Measure.map_dirac, Nat.cast_zero]
    rcases le_or_gt u 0 with h0 | h0
    · exact Measure.quantile_of_nonpos _ h0
    rcases le_or_gt u 1 with h1 | h1
    · exact Measure.quantile_dirac 0 h0 h1
    · exact Measure.quantile_of_one_lt _ h1
  · rw [negativeBinomialMeasure_eq_zero_of_invalid (fun h' ↦ h h'.2), Measure.map_zero,
      Measure.quantile_zero]

/-- At success probability one, every valid negative-binomial law is concentrated at zero, so
its lower quantiles are zero, at every level and also at invalid shapes. -/
theorem quantile_map_cast_negativeBinomialMeasure_one :
    ((negativeBinomialMeasure r 1).map (Nat.cast : ℕ → ℝ)).quantile u = 0 := by
  by_cases hr : 0 ≤ r
  · rw [negativeBinomialMeasure_eq_dirac_of_successProbability_eq_one hr,
      Measure.map_dirac, Nat.cast_zero]
    rcases le_or_gt u 0 with h0 | h0
    · exact Measure.quantile_of_nonpos _ h0
    rcases le_or_gt u 1 with h1 | h1
    · exact Measure.quantile_dirac 0 h0 h1
    · exact Measure.quantile_of_one_lt _ h1
  · rw [negativeBinomialMeasure_eq_zero_of_invalid (fun h ↦ hr h.1), Measure.map_zero,
      Measure.quantile_zero]

/-- Every valid real-cast negative-binomial law has lower support endpoint zero, including the
shape-zero and success-probability-one Dirac boundaries. -/
theorem tendsto_quantile_map_cast_negativeBinomialMeasure_nhdsGT_zero (hr : 0 ≤ r)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    Tendsto ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)).quantile
      (𝓝[>] 0) (𝓝 0) := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  have hmass : 0 < (negativeBinomialMeasure r p).real (Iic 0) := by
    -- The explicit set type makes `Iic_bot` specialize to naturals before rewriting the measure.
    rw [show (Iic 0 : Set ℕ) = {0} from Iic_bot,
      negativeBinomialMeasure_real_singleton hr hp hp1]
    exact (negativeBinomialWeightReal_pos_iff hr hp hp1 0).2 (Or.inl rfl)
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT hmass] with v hv
  have hv1 : v < 1 := hv.2.trans_le measureReal_le_one
  have hquantile :
      ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)).quantile v = 0 := by
    have h : ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)).quantile v =
        ((0 : ℕ) : ℝ) := by
      rw [Measure.quantile_map_natCast_eq_iff _ ⟨hv.1, hv1⟩]
      exact ⟨hv.2.le, fun j _ ↦ Nat.zero_le j⟩
    simpa using h
  exact hquantile.symm

/-- The upper support endpoint of a valid real-cast negative-binomial law is positive infinity
exactly away from the shape-zero and success-probability-one Dirac boundaries. -/
theorem tendsto_quantile_map_cast_negativeBinomialMeasure_nhdsLT_one (hr : 0 ≤ r)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    Tendsto (fun v ↦
      (((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)).quantile v : EReal))
      (𝓝[<] 1) (𝓝 (if r = 0 ∨ p = 1 then (0 : EReal) else ⊤)) := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  by_cases hdeg : r = 0 ∨ p = 1
  · rw [ite_eq_left hdeg]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with v hv
    rcases hdeg with rfl | rfl
    · exact_mod_cast (quantile_map_cast_negativeBinomialMeasure_zero).symm
    · exact_mod_cast (quantile_map_cast_negativeBinomialMeasure_one).symm
  · rw [ite_eq_right hdeg]
    have hr0 : 0 < r := lt_of_le_of_ne hr (fun h ↦ hdeg (Or.inl h.symm))
    have hp1' : p < 1 := lt_of_le_of_ne hp1 (fun h ↦ hdeg (Or.inr h))
    apply EReal.tendsto_coe_nhds_top_iff.2
    refine tendsto_atTop.2 fun b ↦ ?_
    have hb : cdf ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) b < 1 := by
      by_cases hb0 : 0 ≤ b
      · rw [cdf_map_cast_negativeBinomialMeasure hr0 hp hp1 hb0]
        exact (regularizedIncompleteBeta_lt_one_iff hr0 (by positivity)).2 hp1'
      · rw [Measure.cdf_map_natCast_of_neg _ (lt_of_not_ge hb0)]
        exact zero_lt_one
    filter_upwards [Ioo_mem_nhdsLT hb] with v hv
    exact ((Measure.lt_quantile_iff _ ((cdf_nonneg _ b).trans_lt hv.1) hv.2).2 hv.1).le

end TauCeti.Probability
