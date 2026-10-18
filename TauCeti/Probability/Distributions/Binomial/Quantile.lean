/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Binomial.Cdf
public import TauCeti.Probability.Quantile.Discrete
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of binomial laws

An interior lower quantile of the real cast of `Bin(n, p)` is the least natural number at which
the binomial cumulative mass reaches the requested level.  This file states that crossing directly
through the regularized incomplete beta formula, and records the zero-trial and deterministic
success-probability boundaries.

The endpoint limits distinguish those deterministic boundaries: near level zero the quantile tends
to `n` when `p = 1` and to zero otherwise; near level one it tends to zero when `p = 0` and to `n`
otherwise.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ProbabilityTheory

namespace TauCeti.Probability

variable {n k : ℕ} {p : unitInterval} {u : ℝ}

/-- A natural number is the binomial quantile exactly when it is the least index whose explicit
incomplete-beta cumulative mass reaches the requested level.  At and beyond the upper support
endpoint the cumulative mass is one. -/
theorem quantile_map_cast_binomial_eq_iff (hu : u ∈ Ioo 0 1) (k : ℕ) :
    Bin(ℝ, n, p).quantile u = k ↔
      IsLeast
        {j : ℕ | u ≤ if n ≤ j then 1 else
          regularizedIncompleteBeta ((n : ℝ) - j) ((j : ℝ) + 1) (1 - (p : ℝ))}
        k := by
  rw [Measure.quantile_map_natCast_eq_iff Bin(n, p) hu]
  constructor <;> intro h
  · simpa only [binomial_real_Iic] using h
  · simpa only [binomial_real_Iic] using h

/-- The binomial quantile is zero exactly through the mass `(1 - p) ^ n` at zero. -/
theorem quantile_map_cast_binomial_eq_zero_iff (hu : u ∈ Ioo 0 1) :
    Bin(ℝ, n, p).quantile u = 0 ↔ u ≤ (1 - (p : ℝ)) ^ n := by
  have hleast : IsLeast {j : ℕ | u ≤ Bin(n, p).real (Iic j)} 0 ↔
      u ≤ (1 - (p : ℝ)) ^ n := by
    have hiic : (Iic (0 : ℕ) : Set ℕ) = {0} := by ext j; simp
    constructor
    · intro h
      simpa only [Set.mem_ofPred_eq, hiic, binomial_real_zero] using h.1
    · intro h
      refine ⟨?_, fun j _ ↦ Nat.zero_le j⟩
      simpa only [Set.mem_ofPred_eq, hiic, binomial_real_zero] using h
  simpa only [Nat.cast_zero] using
    (Measure.quantile_map_natCast_eq_iff Bin(n, p) hu 0).trans hleast

/-- Above `1 - p ^ n`, the binomial quantile is the upper support endpoint `n`. -/
theorem quantile_map_cast_binomial_eq_self (hu : u ∈ Ioo 0 1)
    (hlevel : 1 - (p : ℝ) ^ n < u) :
    Bin(ℝ, n, p).quantile u = n := by
  rw [Measure.quantile_map_natCast_eq_iff Bin(n, p) hu]
  constructor
  · simpa only [Set.mem_ofPred_eq, binomial_real_Iic, ite_eq_left le_rfl] using hu.2.le
  · intro j hj
    by_contra hnj
    have hjn : j < n := lt_of_not_ge hnj
    have hsubset : (Iic j : Set ℕ) ⊆ ({n} : Set ℕ)ᶜ := by
      intro i hi
      simp only [mem_compl_iff, mem_singleton_iff]
      exact ne_of_lt (hi.trans_lt hjn)
    have hmass : Bin(n, p).real (Iic j) ≤ 1 - (p : ℝ) ^ n := by
      calc
        Bin(n, p).real (Iic j) ≤ Bin(n, p).real ({n} : Set ℕ)ᶜ :=
          measureReal_mono hsubset
        _ = 1 - Bin(n, p).real ({n} : Set ℕ) :=
          probReal_compl_eq_one_sub .of_discrete
        _ = 1 - (p : ℝ) ^ n := by rw [binomial_real_self]
    exact (not_le_of_gt hlevel) (hj.trans hmass)

/-- With no trials, every interior binomial quantile is zero. -/
-- Not a simp lemma: `map_cast_binomial_zero` already simplifies its left-hand side, so `simpNF`
-- rejects the annotation.
theorem quantile_map_cast_binomial_zero (p : unitInterval) (hu : u ∈ Ioo 0 1) :
    Bin(ℝ, 0, p).quantile u = 0 := by
  rw [quantile_map_cast_binomial_eq_zero_iff hu]
  exact hu.2.le

/-- At success probability zero, every interior binomial quantile is zero. -/
@[simp]
theorem quantile_map_cast_binomial_prob_zero (n : ℕ) (hu : u ∈ Ioo 0 1) :
    Bin(ℝ, n, (0 : unitInterval)).quantile u = 0 := by
  rw [quantile_map_cast_binomial_eq_zero_iff hu]
  simp [hu.2.le]

/-- At success probability one, every interior binomial quantile is the number of trials. -/
@[simp]
theorem quantile_map_cast_binomial_prob_one (n : ℕ) (hu : u ∈ Ioo 0 1) :
    Bin(ℝ, n, (1 : unitInterval)).quantile u = n := by
  apply quantile_map_cast_binomial_eq_self hu
  simpa using hu.1

/-- As the level tends to zero from above, binomial quantiles tend to the lower endpoint of their
support, including the deterministic `p = 1` boundary. -/
theorem tendsto_quantile_map_cast_binomial_nhdsGT_zero (n : ℕ) (p : unitInterval) :
    Tendsto (fun u ↦ (Bin(ℝ, n, p).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (if p = 1 then (n : EReal) else 0)) := by
  refine tendsto_const_nhds.congr' ?_
  by_cases hp : p = 1
  · subst p
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    rw [quantile_map_cast_binomial_prob_one n hu, ite_eq_left rfl]
    norm_cast
  · have hp' : (p : ℝ) < 1 := unitInterval.coe_lt_one.mpr
      (unitInterval.lt_one_iff_ne_one.mpr hp)
    have hmass : 0 < (1 - (p : ℝ)) ^ n := pow_pos (sub_pos.mpr hp') n
    have hmass_le : (1 - (p : ℝ)) ^ n ≤ 1 := by
      exact pow_le_one₀ (sub_nonneg.mpr (unitInterval.le_one p))
        (by linarith [unitInterval.nonneg p])
    filter_upwards [Ioo_mem_nhdsGT hmass] with u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le hmass_le⟩
    rw [(quantile_map_cast_binomial_eq_zero_iff hu').2 hu.2.le, ite_eq_right hp]
    rfl

/-- As the level tends to one from below, binomial quantiles tend to the upper endpoint of their
support, including the deterministic `p = 0` boundary. -/
theorem tendsto_quantile_map_cast_binomial_nhdsLT_one (n : ℕ) (p : unitInterval) :
    Tendsto (fun u ↦ (Bin(ℝ, n, p).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if p = 0 then 0 else (n : EReal))) := by
  refine tendsto_const_nhds.congr' ?_
  by_cases hp : p = 0
  · subst p
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rw [quantile_map_cast_binomial_prob_zero n hu, ite_eq_left rfl]
    simp
  · have hp' : 0 < (p : ℝ) := unitInterval.coe_pos.mpr
      (unitInterval.pos_iff_ne_zero.mpr hp)
    have hmass : 0 < (p : ℝ) ^ n := pow_pos hp' n
    have hmass_le : (p : ℝ) ^ n ≤ 1 :=
      pow_le_one₀ (unitInterval.nonneg p) (unitInterval.le_one p)
    filter_upwards [Ioo_mem_nhdsLT (sub_lt_self 1 hmass)] with u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨(sub_nonneg.mpr hmass_le).trans_lt hu.1, hu.2⟩
    rw [quantile_map_cast_binomial_eq_self hu' hu.1, ite_eq_right hp]
    norm_cast

end TauCeti.Probability
