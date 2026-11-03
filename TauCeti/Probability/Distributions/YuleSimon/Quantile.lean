/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.YuleSimon.Basic
public import TauCeti.Probability.Quantile.Discrete
public import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Quantiles of Yule–Simon laws

An interior lower quantile of a real-cast Yule–Simon law is the least positive integer `k`
whose upper tail `k B(k, ρ + 1)` is at most the complementary level. The weak inequality
retains equality at cumulative jumps. Positivity of the index is essential: the beta-function
expression vanishes at zero, whereas the probability of exceeding zero is one.

The quantile is one through the first-atom mass `ρ / (ρ + 1)`. Its one-sided limits at levels
zero and one are respectively one and positive infinity, the endpoints of its support.

## References

* N. L. Johnson, A. W. Kemp, and S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Section 6.10.3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped Nat

namespace TauCeti.Probability

variable {ρ u : ℝ}

/-- A natural number is the Yule–Simon lower quantile exactly when it is the least positive
index whose explicit beta-function tail is at most `1 - u`. -/
theorem quantile_map_cast_yuleSimonMeasure_eq_iff (hρ : 0 < ρ) (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {n : ℕ | n ≠ 0 ∧ n * beta n (ρ + 1) ≤ 1 - u} k := by
  have := isProbabilityMeasure_yuleSimonMeasure hρ
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  have hcross : {n : ℕ | u ≤ (yuleSimonMeasure ρ).real (Iic n)} =
      {n : ℕ | n ≠ 0 ∧ n * beta n (ρ + 1) ≤ 1 - u} := by
    ext n
    by_cases hn : n = 0
    · subst n
      have hzero : (Iic 0 : Set ℕ) = {0} := Iic_bot
      simp [hzero, measureReal_def, hu.1.not_ge]
    · simp only [mem_ofPred_eq, yuleSimonMeasure_real_Iic hρ hn]
      constructor
      · intro h
        exact ⟨hn, by linarith⟩
      · rintro ⟨_, h⟩
        linarith
  rw [hcross]

/-- The initial constant segment of a Yule–Simon quantile includes the full mass at one. -/
@[simp]
theorem quantile_map_cast_yuleSimonMeasure_eq_one_iff (hρ : 0 < ρ) (hu : u ∈ Ioo 0 1) :
    ((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)).quantile u = 1 ↔ u ≤ ρ / (ρ + 1) := by
  have hfirst : 1 - beta 1 (ρ + 1) = ρ / (ρ + 1) := by
    rw [beta_comm, beta_one_right (by positivity)]
    field_simp
    ring
  have hquant := quantile_map_cast_yuleSimonMeasure_eq_iff hρ hu 1
  simp only [Nat.cast_one] at hquant
  rw [hquant]
  constructor
  · intro h
    have htail := h.1.2
    simp only [Nat.cast_one, one_mul] at htail
    rw [← hfirst]
    linarith
  · intro h
    refine ⟨⟨Nat.one_ne_zero, ?_⟩, fun n hn ↦ Nat.one_le_iff_ne_zero.2 hn.1⟩
    simp only [Nat.cast_one, one_mul]
    rw [← hfirst] at h
    linarith

/-- Yule–Simon quantiles tend to the lower support endpoint one as the level tends to zero
from above. This limit does not concern the totalized value at level zero. -/
theorem tendsto_quantile_map_cast_yuleSimonMeasure_nhdsGT_zero (hρ : 0 < ρ) :
    Tendsto (fun u ↦
      (((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 1) := by
  have hmass : 0 < ρ / (ρ + 1) := div_pos hρ (by positivity)
  have hmass_lt : ρ / (ρ + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hmass] with u hu
  have hq := (quantile_map_cast_yuleSimonMeasure_eq_one_iff hρ
    ⟨hu.1, hu.2.trans hmass_lt⟩).2 hu.2.le
  simpa using congrArg (fun x : ℝ ↦ (x : EReal)) hq.symm

/-- Yule–Simon quantiles tend to positive infinity as the level tends to one from below,
since every finite cutoff leaves a positive upper tail. -/
theorem tendsto_quantile_map_cast_yuleSimonMeasure_nhdsLT_one (hρ : 0 < ρ) :
    Tendsto (fun u ↦
      (((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  have := isProbabilityMeasure_yuleSimonMeasure hρ
  rw [EReal.tendsto_coe_nhds_top_iff]
  refine tendsto_atTop.2 fun b ↦ ?_
  have hb : cdf ((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)) b < 1 := by
    by_cases hb1 : 1 ≤ b
    · rw [cdf_map_cast_yuleSimonMeasure hρ hb1]
      have hfloor : (0 : ℝ) < ⌊b⌋₊ := by
        exact_mod_cast (Nat.one_le_floor_iff b).2 hb1
      exact sub_lt_self _ (mul_pos hfloor (beta_pos hfloor (by positivity)))
    · rw [cdf_map_cast_yuleSimonMeasure_of_lt_one hρ (lt_of_not_ge hb1)]
      exact zero_lt_one
  filter_upwards [Ioo_mem_nhdsLT hb] with u hu
  exact ((Measure.lt_quantile_iff _
    ((cdf_nonneg _ _).trans_lt hu.1) hu.2).2 hu.1).le

end TauCeti.Probability
