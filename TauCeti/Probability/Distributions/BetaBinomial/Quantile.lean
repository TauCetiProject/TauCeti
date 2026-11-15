/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.BetaBinomial.Cdf
public import TauCeti.Probability.Quantile.Discrete
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of beta-binomial laws

An interior quantile of a real-cast beta-binomial law is the least natural count whose explicit
Beta-function cumulative sum reaches the level. The quantile is zero through the mass at zero
and equals the trial count above one minus its mass there. Consequently its one-sided endpoint
limits are zero and the trial count, including the zero-trial Dirac law.

The crossing theorem specializes `Measure.quantile_map_natCast_eq_iff`. The endpoint argument
follows the finite-support calculation in
`TauCeti.Probability.Distributions.Hypergeometric.Quantile`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {a b u : ℝ} {n : ℕ}

/-- A natural count is the beta-binomial quantile exactly when it is the least crossing of the
explicit finite cumulative sum. Equality at an attained cumulative mass is included. -/
theorem quantile_map_cast_betaBinomialMeasure_eq_iff (ha : 0 < a) (hb : 0 < b)
    (hu : u ∈ Ioo 0 1) (n k : ℕ) :
    ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {i : ℕ | u ≤ ∑ j ∈ Finset.Iic i,
        n.choose j * beta (a + j) (b + (n - j)) / beta a b} k := by
  let _ := isProbabilityMeasure_betaBinomialMeasure ha hb n
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  simp only [betaBinomialMeasure_real_Iic ha hb]

/-- The beta-binomial quantile is zero exactly through its mass `B(a,b+n)/B(a,b)` at zero. -/
theorem quantile_map_cast_betaBinomialMeasure_eq_zero_iff (ha : 0 < a) (hb : 0 < b)
    (hu : u ∈ Ioo 0 1) :
    ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)).quantile u = 0 ↔
      u ≤ beta a (b + n) / beta a b := by
  simpa [IsLeast, lowerBounds, ← Nat.range_succ_eq_Iic] using
    (quantile_map_cast_betaBinomialMeasure_eq_iff ha hb hu n 0)

/-- Above one minus the mass at the trial count, the beta-binomial quantile equals that count. -/
theorem quantile_map_cast_betaBinomialMeasure_eq_upper (ha : 0 < a) (hb : 0 < b)
    (hu : u ∈ Ioo 0 1) (hlevel : 1 - beta (a + n) b / beta a b < u) :
    ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)).quantile u = n := by
  let _ := isProbabilityMeasure_betaBinomialMeasure ha hb n
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  constructor
  · simpa only [Set.mem_ofPred_eq, betaBinomialMeasure_real_Iic_eq_one ha hb le_rfl]
      using hu.2.le
  · intro j hj
    by_contra hnj
    have hsubset : (Iic j : Set ℕ) ⊆ ({n} : Set ℕ)ᶜ := by
      intro k hk
      exact ne_of_lt (hk.trans_lt (lt_of_not_ge hnj))
    have hmass : (betaBinomialMeasure n a b).real (Iic j) ≤
        1 - beta (a + n) b / beta a b := by
      calc
        _ ≤ (betaBinomialMeasure n a b).real ({n} : Set ℕ)ᶜ :=
          measureReal_mono hsubset
        _ = _ := by
          rw [probReal_compl_eq_one_sub .of_discrete, betaBinomialMeasure_real_singleton ha hb]
          simp
    exact (not_le_of_gt hlevel) (hj.trans hmass)

/-- As the level tends to zero from above, beta-binomial quantiles tend to zero. -/
theorem tendsto_quantile_map_cast_betaBinomialMeasure_nhdsGT_zero
    (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Tendsto (fun u ↦
      (((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  let _ := isProbabilityMeasure_betaBinomialMeasure ha hb n
  have hmass : 0 < beta a (b + n) / beta a b :=
    div_pos (beta_pos ha (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n))) (beta_pos ha hb)
  have hmass_le : beta a (b + n) / beta a b ≤ 1 := by
    have h := (measureReal_mono (μ := betaBinomialMeasure n a b)
      (subset_univ {0})).trans_eq probReal_univ
    rw [betaBinomialMeasure_real_singleton ha hb] at h
    simpa only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.cast_zero, add_zero,
      sub_zero] using h
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hmass] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le hmass_le⟩
  rw [(quantile_map_cast_betaBinomialMeasure_eq_zero_iff ha hb hu').2 hu.2.le]
  rfl

/-- As the level tends to one from below, beta-binomial quantiles tend to the trial count. -/
theorem tendsto_quantile_map_cast_betaBinomialMeasure_nhdsLT_one
    (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Tendsto (fun u ↦
      (((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (n : EReal)) := by
  let _ := isProbabilityMeasure_betaBinomialMeasure ha hb n
  have hmass : 0 < beta (a + n) b / beta a b :=
    div_pos (beta_pos (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)) hb) (beta_pos ha hb)
  have hmass_le : beta (a + n) b / beta a b ≤ 1 := by
    have h := (measureReal_mono (μ := betaBinomialMeasure n a b)
      (subset_univ {n})).trans_eq probReal_univ
    rw [betaBinomialMeasure_real_singleton ha hb] at h
    simpa only [Nat.choose_self, Nat.cast_one, one_mul, sub_self, add_zero] using h
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (sub_lt_self 1 hmass)] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨(sub_nonneg.mpr hmass_le).trans_lt hu.1, hu.2⟩
  rw [quantile_map_cast_betaBinomialMeasure_eq_upper ha hb hu' hu.1]
  norm_cast

end TauCeti.Probability
