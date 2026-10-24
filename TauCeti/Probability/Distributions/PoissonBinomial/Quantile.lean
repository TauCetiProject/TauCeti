/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.PoissonBinomial.Cdf
public import TauCeti.Probability.Quantile.Discrete
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of Poisson-binomial laws

Every interior quantile of a real-cast Poisson-binomial count is the least natural number
whose explicit cumulative success-set sum reaches the requested level. Near zero the quantile
is the number of certain successes; near one it is the number of trials with nonzero success
probability. This includes empty families and deterministic trials.

The endpoint argument follows the finite-support quantile calculations in
`TauCeti.Probability.Distributions.Hypergeometric.Quantile`, using the native discrete quantile
characterization from `TauCeti.Probability.Quantile.Discrete`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {u : ℝ}

open Classical in
/-- A count is the quantile exactly when it is the least index whose explicit cumulative
success-set sum reaches the level. -/
theorem quantile_map_cast_poissonBinomialMeasure_eq_iff (p : ι → unitInterval)
    (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {j : ℕ | u ≤
        ∑ s : Finset ι with s.card ≤ j, (poissonBinomialWeight p s : ℝ)} k := by
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  simp only [poissonBinomialMeasure_real_Iic]

open Classical in
/-- Through the mass at the smallest possible count, the quantile equals the number of
certain successes. -/
theorem quantile_map_cast_poissonBinomialMeasure_eq_lower (p : ι → unitInterval)
    (hu : u ∈ Ioo 0 1)
    (hlevel : u ≤ (poissonBinomialMeasure p).real
      {(Finset.univ.filter fun i ↦ p i = 1).card}) :
    ((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)).quantile u =
      ((Finset.univ.filter fun i ↦ p i = 1).card : ℕ) := by
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  constructor
  · exact hlevel.trans (measureReal_mono (by simp))
  · intro j hj
    simp only [Set.mem_ofPred_eq] at hj
    by_contra hnot
    have hzero := poissonBinomialMeasure_real_Iic_eq_zero_of_lt_lower p
      (lt_of_not_ge hnot)
    rw [hzero] at hj
    exact hu.1.not_ge hj

open Classical in
/-- Above one minus the mass at the largest possible count, the quantile equals the number
of trials with nonzero success probability. -/
theorem quantile_map_cast_poissonBinomialMeasure_eq_upper (p : ι → unitInterval)
    (hu : u ∈ Ioo 0 1)
    (hlevel : 1 - (poissonBinomialMeasure p).real
      {(Finset.univ.filter fun i ↦ p i ≠ 0).card} < u) :
    ((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)).quantile u =
      ((Finset.univ.filter fun i ↦ p i ≠ 0).card : ℕ) := by
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  constructor
  · simpa only [Set.mem_ofPred_eq,
      poissonBinomialMeasure_real_Iic_eq_one_of_upper_le p le_rfl] using hu.2.le
  · intro j hj
    simp only [Set.mem_ofPred_eq] at hj
    by_contra hnot
    have hsubset : (Iic j : Set ℕ) ⊆
        ({(Finset.univ.filter fun i ↦ p i ≠ 0).card} : Set ℕ)ᶜ := by
      intro k hk
      exact ne_of_lt (hk.trans_lt (lt_of_not_ge hnot))
    have hmass : (poissonBinomialMeasure p).real (Iic j) ≤
        1 - (poissonBinomialMeasure p).real
          {(Finset.univ.filter fun i ↦ p i ≠ 0).card} := by
      calc
        _ ≤ (poissonBinomialMeasure p).real
            ({(Finset.univ.filter fun i ↦ p i ≠ 0).card} : Set ℕ)ᶜ :=
          measureReal_mono hsubset
        _ = _ := probReal_compl_eq_one_sub .of_discrete
    exact (not_le_of_gt hlevel) (hj.trans hmass)

open Classical in
/-- As the level tends to zero from above, quantiles tend to the number of certain successes. -/
theorem tendsto_quantile_map_cast_poissonBinomialMeasure_nhdsGT_zero (p : ι → unitInterval) :
    Tendsto
      (fun u ↦ (((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ((Finset.univ.filter fun i ↦ p i = 1).card : ℕ)) := by
  have hLU : (Finset.univ.filter fun i ↦ p i = 1).card ≤
      (Finset.univ.filter fun i ↦ p i ≠ 0).card :=
    Finset.card_le_card fun i hi ↦ by simp_all
  have hmass : 0 < (poissonBinomialMeasure p).real
      {(Finset.univ.filter fun i ↦ p i = 1).card} :=
    ENNReal.toReal_pos
      ((poissonBinomialMeasure_singleton_ne_zero_iff p _).mpr ⟨le_rfl, hLU⟩)
      (by finiteness)
  have hmass_le : (poissonBinomialMeasure p).real
      {(Finset.univ.filter fun i ↦ p i = 1).card} ≤ 1 :=
    (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hmass] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le hmass_le⟩
  rw [quantile_map_cast_poissonBinomialMeasure_eq_lower p hu' hu.2.le]
  norm_cast

open Classical in
/-- As the level tends to one from below, quantiles tend to the number of trials with nonzero
success probability. -/
theorem tendsto_quantile_map_cast_poissonBinomialMeasure_nhdsLT_one (p : ι → unitInterval) :
    Tendsto
      (fun u ↦ (((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ((Finset.univ.filter fun i ↦ p i ≠ 0).card : ℕ)) := by
  have hLU : (Finset.univ.filter fun i ↦ p i = 1).card ≤
      (Finset.univ.filter fun i ↦ p i ≠ 0).card :=
    Finset.card_le_card fun i hi ↦ by simp_all
  have hmass : 0 < (poissonBinomialMeasure p).real
      {(Finset.univ.filter fun i ↦ p i ≠ 0).card} :=
    ENNReal.toReal_pos
      ((poissonBinomialMeasure_singleton_ne_zero_iff p _).mpr ⟨hLU, le_rfl⟩)
      (by finiteness)
  have hmass_le : (poissonBinomialMeasure p).real
      {(Finset.univ.filter fun i ↦ p i ≠ 0).card} ≤ 1 :=
    (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (sub_lt_self 1 hmass)] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨(sub_nonneg.mpr hmass_le).trans_lt hu.1, hu.2⟩
  rw [quantile_map_cast_poissonBinomialMeasure_eq_upper p hu' hu.1]
  norm_cast

end TauCeti.Probability
