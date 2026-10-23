/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Skellam.Cdf
public import TauCeti.Probability.Quantile.Discrete
public import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Probability.Distributions.Poisson.Quantile

/-!
# Quantiles of Skellam laws

The quantile of a real-cast Skellam law at an interior probability level is the least integer
whose Poisson-conditioned cumulative series reaches that level. Equality at a cumulative jump
is retained. No strict monotonicity or continuous inverse is asserted for this discrete law.

The one-sided limits in `EReal` are minus infinity at level zero when the subtracted rate is
positive, and plus infinity at level one when the first rate is positive. A zero rate instead
gives the corresponding finite endpoint zero, including the two-zero-rate Dirac law.

## References

* J. G. Skellam, *The frequency distribution of the difference between two Poisson variates
  belonging to different populations*, Journal of the Royal Statistical Society 109 (1946), 296.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped NNReal

namespace TauCeti.Probability

/-- An integer is the Skellam lower quantile exactly when it is the least crossing of the
explicit cumulative series, including when the level equals a cumulative mass. -/
theorem quantile_map_intCast_skellamMeasure_eq_iff (r₁ r₂ : ℝ≥0) {u : ℝ}
    (hu : u ∈ Ioo 0 1) (k : ℤ) :
    ((skellamMeasure r₁ r₂).map (Int.cast : ℤ → ℝ)).quantile u = k ↔
      IsLeast {n : ℤ | u ≤
        ∑' j : ℕ, (exp (-(r₂ : ℝ)) * (r₂ : ℝ) ^ j / j.factorial) *
          if 0 ≤ n + j then
            ∑ i ∈ Finset.range ((n + j).toNat + 1),
              exp (-(r₁ : ℝ)) * (r₁ : ℝ) ^ i / i.factorial
          else 0} k := by
  rw [Measure.quantile_map_intCast_eq_iff _ hu]
  simp_rw [skellamMeasure_real_Iic]

/-- With only a subtracted Poisson count, the final constant segment starts strictly above the
mass below zero. The strict inequality is essential at a cumulative jump. -/
theorem quantile_map_intCast_skellamMeasure_zero_left_eq_zero_iff (r : ℝ≥0) {u : ℝ}
    (hu : u ∈ Ioo 0 1) :
    ((skellamMeasure 0 r).map (Int.cast : ℤ → ℝ)).quantile u = 0 ↔
      1 - exp (-(r : ℝ)) < u := by
  have hzero : (skellamMeasure 0 r).real (Iic 0) = 1 := by
    rw [skellamMeasure_zero_left, map_measureReal_apply (by fun_prop) measurableSet_Iic]
    have hpre : (fun n : ℕ ↦ -(n : ℤ)) ⁻¹' Iic 0 = univ := by
      ext n
      simp
    rw [hpre, probReal_univ]
  have hpred : (skellamMeasure 0 r).real (Iic (-1)) = 1 - exp (-(r : ℝ)) := by
    rw [skellamMeasure_real_Iic_eq_one_sub]
    norm_num only [neg_neg, sub_self]
    rw [skellamMeasure_zero_right, map_measureReal_apply (by fun_prop) measurableSet_Iic]
    have hpre : (Nat.cast : ℕ → ℤ) ⁻¹' Iic 0 = {0} := by
      ext n
      simp
    rw [hpre, poissonMeasure_real_singleton]
    simp
  rw [← Int.cast_zero (R := ℝ), Measure.quantile_map_intCast_eq_iff _ hu]
  constructor
  · intro h
    by_contra! hn
    have hbelow : (-1 : ℤ) ∈ {j | u ≤ (skellamMeasure 0 r).real (Iic j)} := by
      simpa only [mem_ofPred_eq, hpred] using hn
    have hle := h.2 hbelow
    omega
  · intro h
    refine ⟨by simpa only [mem_ofPred_eq, hzero] using hu.2.le, ?_⟩
    intro j hj
    by_contra! hj0
    have hle : (skellamMeasure 0 r).real (Iic j) ≤
        (skellamMeasure 0 r).real (Iic (-1)) :=
      measureReal_mono (Iic_subset_Iic.mpr (by omega))
    rw [hpred] at hle
    exact h.not_ge (hj.trans hle)

/-- At two zero rates every interior quantile is zero. -/
theorem quantile_map_intCast_skellamMeasure_zero_zero {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((skellamMeasure 0 0).map (Int.cast : ℤ → ℝ)).quantile u = 0 :=
  (quantile_map_intCast_skellamMeasure_zero_left_eq_zero_iff 0 hu).2
    (by simpa using hu.1)

/-- The lower endpoint is zero if the subtracted rate vanishes, and minus infinity otherwise.
The limit is through interior levels, independently of the quantile's totalized endpoint value. -/
theorem tendsto_quantile_map_intCast_skellamMeasure_nhdsGT_zero (r₁ r₂ : ℝ≥0) :
    Tendsto (fun u ↦
      (((skellamMeasure r₁ r₂).map (Int.cast : ℤ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (if r₂ = 0 then 0 else ⊥)) := by
  by_cases h₂ : r₂ = 0
  · subst r₂
    rw [ite_eq_left rfl]
    have hcast : (skellamMeasure r₁ 0).map (Int.cast : ℤ → ℝ) = Po(ℝ, r₁) := by
      rw [skellamMeasure_zero_right, Measure.map_map (by fun_prop) (by fun_prop)]
      simp [Function.comp_def]
    rw [hcast]
    exact tendsto_quantile_map_cast_poissonMeasure_nhdsGT_zero r₁
  · rw [ite_eq_right h₂, EReal.tendsto_coe_nhds_bot_iff]
    refine tendsto_atBot.2 fun b ↦ ?_
    have hb : 0 < cdf ((skellamMeasure r₁ r₂).map (Int.cast : ℤ → ℝ)) b := by
      rw [Measure.cdf_map_intCast]
      exact skellamMeasure_real_Iic_pos r₁ (pos_iff_ne_zero.mpr h₂) _
    filter_upwards [Ioo_mem_nhdsGT hb] with u hu
    exact (Measure.quantile_le_iff _ hu.1
      (hu.2.trans_le (cdf_le_one _ _))).2 hu.2.le

/-- The upper endpoint is zero if the first rate vanishes, and plus infinity otherwise.
The zero-rate cases retain the finite endpoint of a negative Poisson or Dirac law. -/
theorem tendsto_quantile_map_intCast_skellamMeasure_nhdsLT_one (r₁ r₂ : ℝ≥0) :
    Tendsto (fun u ↦
      (((skellamMeasure r₁ r₂).map (Int.cast : ℤ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if r₁ = 0 then 0 else ⊤)) := by
  by_cases h₁ : r₁ = 0
  · subst r₁
    rw [ite_eq_left rfl]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (sub_lt_self 1 (exp_pos (-(r₂ : ℝ))))] with u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 :=
      ⟨(sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr r₂.coe_nonneg))).trans_lt hu.1, hu.2⟩
    exact congrArg (fun x : ℝ ↦ (x : EReal))
      ((quantile_map_intCast_skellamMeasure_zero_left_eq_zero_iff r₂ hu').2 hu.1).symm
  · rw [ite_eq_right h₁, EReal.tendsto_coe_nhds_top_iff]
    refine tendsto_atTop.2 fun b ↦ ?_
    have hb : cdf ((skellamMeasure r₁ r₂).map (Int.cast : ℤ → ℝ)) b < 1 := by
      rw [Measure.cdf_map_intCast]
      exact skellamMeasure_real_Iic_lt_one (pos_iff_ne_zero.mpr h₁) r₂ _
    filter_upwards [Ioo_mem_nhdsLT hb] with u hu
    exact ((Measure.lt_quantile_iff _
      ((cdf_nonneg _ _).trans_lt hu.1) hu.2).2 hu.1).le

end TauCeti.Probability
