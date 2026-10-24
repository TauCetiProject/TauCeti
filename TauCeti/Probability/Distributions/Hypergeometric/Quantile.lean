/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypergeometric.Cdf
public import TauCeti.Probability.Quantile.Discrete
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of hypergeometric laws

An interior lower quantile of a real-cast hypergeometric law is the least natural number at
which its explicit finite cumulative sum reaches the requested level.  The support runs from
`n - (N - K)` to `min K n`: the lower endpoint is the number of marked objects forced into a
sample of size `n`, and the upper endpoint is the largest possible number of marked draws.

This file gives the least-crossing characterization and proves that the quantiles tend to those
two support endpoints as the probability level approaches zero and one.  The formulas include
all valid degenerate populations and samples.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {N K n k : ℕ} {u : ℝ}

/-- A natural number is the hypergeometric quantile exactly when it is the least index whose
explicit finite cumulative mass reaches the requested level. -/
theorem quantile_map_cast_hypergeometricMeasure_eq_iff (hK : K ≤ N) (hn : n ≤ N)
    (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast
        {i : ℕ | u ≤ ∑ j ∈ Finset.Iic i,
          if j ≤ n then
            (K.choose j : ℝ) * ((N - K).choose (n - j) : ℝ) / (N.choose n : ℝ)
          else 0}
        k := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  have hcumulative (i : ℕ) :
      (hypergeometricMeasure N K n).real (Iic i) =
        ∑ j ∈ Finset.Iic i,
          if j ≤ n then
            (K.choose j : ℝ) * ((N - K).choose (n - j) : ℝ) / (N.choose n : ℝ)
          else 0 := by
    rw [← Set.Iic_def, hypergeometricMeasure_real_Iic_eq_sum hK hn]
  constructor <;> intro h
  · simpa only [hcumulative] using h
  · simpa only [hcumulative] using h

private theorem hypergeometricMeasure_real_singleton_pos (hK : K ≤ N) (hn : n ≤ N)
    {k : ℕ} (hk : k ≤ K ∧ k ≤ n ∧ n - k ≤ N - K) :
    0 < (hypergeometricMeasure N K n).real {k} := by
  rw [measureReal_def, hypergeometricMeasure_singleton hK hn]
  exact ENNReal.toReal_pos ((hypergeometricWeight_ne_zero_iff N K n k).2 hk)
    (hypergeometricWeight_ne_top N K n k hn)

/-- At sufficiently small positive levels, a valid hypergeometric quantile is the lower support
endpoint `n - (N - K)`. -/
theorem quantile_map_cast_hypergeometricMeasure_eq_lower (hK : K ≤ N) (hn : n ≤ N)
    (hu : u ∈ Ioo 0 1)
    (hlevel : u ≤ (hypergeometricMeasure N K n).real {n - (N - K)}) :
    ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u =
      (n - (N - K) : ℕ) := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  constructor
  · exact hlevel.trans (measureReal_mono (by simp))
  · intro j hj
    simp only [Set.mem_ofPred_eq] at hj
    by_contra hnot
    have hzero := hypergeometricMeasure_real_Iic_eq_zero_of_lt_lower hK hn
      (lt_of_not_ge hnot)
    rw [hzero] at hj
    exact hu.1.not_ge hj

/-- Above one minus the mass at the upper support endpoint, a valid hypergeometric quantile is
`min K n`. -/
theorem quantile_map_cast_hypergeometricMeasure_eq_upper (hK : K ≤ N) (hn : n ≤ N)
    (hu : u ∈ Ioo 0 1)
    (hlevel : 1 - (hypergeometricMeasure N K n).real {min K n} < u) :
    ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u = min K n := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  constructor
  · simp only [Set.mem_ofPred_eq]
    rw [hypergeometricMeasure_real_Iic_eq_one_of_upper_le hK hn le_rfl]
    exact hu.2.le
  · intro j hj
    simp only [Set.mem_ofPred_eq] at hj
    by_contra hnot
    have hsubset : (Iic j : Set ℕ) ⊆ ({min K n} : Set ℕ)ᶜ := by
      intro i hi
      simp only [mem_compl_iff, mem_singleton_iff]
      exact ne_of_lt (hi.trans_lt (lt_of_not_ge hnot))
    have hmass : (hypergeometricMeasure N K n).real (Iic j) ≤
        1 - (hypergeometricMeasure N K n).real {min K n} := by
      calc
        _ ≤ (hypergeometricMeasure N K n).real ({min K n} : Set ℕ)ᶜ :=
          measureReal_mono hsubset
        _ = _ := probReal_compl_eq_one_sub .of_discrete
    exact (not_le_of_gt hlevel) (hj.trans hmass)

/-- As the level tends to zero from above, valid hypergeometric quantiles tend to the smallest
possible marked count `n - (N - K)`. -/
theorem tendsto_quantile_map_cast_hypergeometricMeasure_nhdsGT_zero
    (hK : K ≤ N) (hn : n ≤ N) :
    Tendsto
      (fun u ↦
        (((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (nhdsWithin 0 (Ioi 0)) (nhds (n - (N - K) : ℕ)) := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  have hlower : n - (N - K) ≤ K ∧ n - (N - K) ≤ n ∧
      n - (n - (N - K)) ≤ N - K := by omega
  have hmass : 0 < (hypergeometricMeasure N K n).real {n - (N - K)} :=
    hypergeometricMeasure_real_singleton_pos hK hn hlower
  have hmass_le : (hypergeometricMeasure N K n).real {n - (N - K)} ≤ 1 :=
    (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hmass] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le hmass_le⟩
  rw [quantile_map_cast_hypergeometricMeasure_eq_lower hK hn hu' hu.2.le]
  norm_cast

/-- As the level tends to one from below, valid hypergeometric quantiles tend to the largest
possible marked count `min K n`. -/
theorem tendsto_quantile_map_cast_hypergeometricMeasure_nhdsLT_one
    (hK : K ≤ N) (hn : n ≤ N) :
    Tendsto
      (fun u ↦
        (((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (nhdsWithin 1 (Iio 1)) (nhds (min K n : ℕ)) := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  have hupper : min K n ≤ K ∧ min K n ≤ n ∧ n - min K n ≤ N - K := by
    omega
  have hmass : 0 < (hypergeometricMeasure N K n).real {min K n} :=
    hypergeometricMeasure_real_singleton_pos hK hn hupper
  have hmass_le : (hypergeometricMeasure N K n).real {min K n} ≤ 1 :=
    (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (sub_lt_self 1 hmass)] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨(sub_nonneg.mpr hmass_le).trans_lt hu.1, hu.2⟩
  rw [quantile_map_cast_hypergeometricMeasure_eq_upper hK hn hu' hu.1]
  norm_cast

end TauCeti.Probability
