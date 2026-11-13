/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Zero.Hurdle
public import TauCeti.Probability.Distributions.Poisson.Zero.Inflated

/-!
# Quantile endpoints of zero-modified Poisson laws

The zero-truncated Poisson quantile has endpoint limits `1` and `+∞` at positive rate.
Zero inflation retains lower endpoint `0`; its upper endpoint is `+∞` unless the rate is
zero or the inflation weight is one. For a hurdle law, the lower endpoint is `1` at zero
hurdle weight and `0` otherwise, and the upper endpoint is `+∞` unless the weight is one.

All limits are taken through interior probability levels and valued in `EReal`. The hurdle
statements include every probability boundary: at rate zero only weight one is admissible.
The zero-truncated law at rate zero is the zero measure, not a probability distribution.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, sections 4.10.1 and 8.2.3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped NNReal Nat unitInterval

namespace TauCeti.Probability

/-- The lower endpoint of a positive-rate zero-truncated Poisson quantile is one. -/
theorem tendsto_quantile_map_cast_poissonMeasure_cond_compl_zero_nhdsGT_zero
    {r : ℝ≥0} (hr : r ≠ 0) :
    Tendsto (fun u ↦ (((Po(r)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 1) := by
  let := isProbabilityMeasure_poissonMeasure_cond_compl_zero hr
  have hmass : 0 < (Po(r)[|{0}ᶜ]).real {1} := by
    rw [poissonMeasure_cond_compl_zero_real_singleton one_ne_zero]
    have hrpos : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    have hexp : 0 < exp (r : ℝ) - 1 := sub_pos.mpr (one_lt_exp_iff.mpr hrpos)
    positivity
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hmass] with u hu
  have hlevel : u < 1 := hu.2.trans_le measureReal_le_one
  have hq : ((Po(r)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u = 1 := by
    rw [← Nat.cast_one, Measure.quantile_map_natCast_eq_succ_iff _ ⟨hu.1, hlevel⟩ 0]
    constructor
    · simpa [Measure.cond_compl_zero_real_Iic, Set.Iic_bot,
        poissonMeasure_real_singleton_zero] using hu.1
    · exact hu.2.le.trans (measureReal_mono (by simp : ({1} : Set ℕ) ⊆ Iic (0 + 1)))
  simpa using congrArg (fun x : ℝ ↦ (x : EReal)) hq.symm

/-- The upper endpoint of a positive-rate zero-truncated Poisson quantile is infinity. -/
theorem tendsto_quantile_map_cast_poissonMeasure_cond_compl_zero_nhdsLT_one
    {r : ℝ≥0} (hr : r ≠ 0) :
    Tendsto (fun u ↦ (((Po(r)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  let := isProbabilityMeasure_poissonMeasure_cond_compl_zero hr
  apply Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one
  intro x
  by_cases hx : 0 ≤ x
  · rw [cdf_map_cast_poissonMeasure_cond_compl_zero hr hx]
    have hrpos : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    have hden : 0 < 1 - exp (-(r : ℝ)) :=
      sub_pos.mpr (exp_lt_one_iff.mpr (neg_neg_of_pos hrpos))
    have hgamma := regularizedGamma_pos (by positivity : 0 < (⌊x⌋₊ : ℝ) + 1) hrpos
    apply (div_lt_one hden).2
    linarith
  · rw [Measure.cdf_map_natCast_of_neg _ (lt_of_not_ge hx)]
    exact zero_lt_one

/-- The lower endpoint of every zero-inflated Poisson quantile is zero. -/
theorem tendsto_quantile_map_cast_poissonMeasure_atomMixture_zero_nhdsGT_zero
    (r : ℝ≥0) (w : unitInterval) :
    Tendsto (fun u ↦ (((Po(r).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  have hmass : 0 < (w : ℝ) + (1 - (w : ℝ)) * exp (-(r : ℝ)) := by
    rcases eq_or_lt_of_le w.2.1 with hw | hw
    · simp [← hw, exp_pos]
    · exact add_pos_of_pos_of_nonneg hw (mul_nonneg (sub_nonneg.mpr w.2.2) (exp_pos _).le)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min hmass zero_lt_one)] with u hu
  have hq := (quantile_map_cast_poissonMeasure_atomMixture_zero_eq_zero_iff r w
    ⟨hu.1, hu.2.trans_le (min_le_right _ _)⟩).2 (hu.2.le.trans (min_le_left _ _))
  simpa using congrArg (fun x : ℝ ↦ (x : EReal)) hq.symm

/-- The upper endpoint of a zero-inflated Poisson quantile is infinity, except at the
rate-zero or weight-one Dirac boundaries. -/
theorem tendsto_quantile_map_cast_poissonMeasure_atomMixture_zero_nhdsLT_one
    (r : ℝ≥0) (w : unitInterval) :
    Tendsto (fun u ↦ (((Po(r).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if r = 0 ∨ w = 1 then 0 else ⊤)) := by
  classical
  by_cases h : r = 0 ∨ w = 1
  · rcases h with hr | hw
    · have heq : (Measure.dirac (0 : ℕ)).atomMixture 0 w = Measure.dirac 0 := by
        rw [Measure.atomMixture_def, ← add_smul,
          ← ENNReal.ofReal_add w.2.1 (sub_nonneg.mpr w.2.2)]
        simp
      simp [hr, poissonMeasure_zero, heq]
    · simp [hw]
  · rw [ite_eq_right h]
    apply Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one
    intro x
    by_cases hx : 0 ≤ x
    · rw [cdf_map_cast_poissonMeasure_atomMixture_zero r w hx]
      have hrpos : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (fun hr ↦ h (.inl hr)))
      have hw : (w : ℝ) < 1 := unitInterval.coe_lt_one.mpr
        (unitInterval.lt_one_iff_ne_one.mpr (fun hw ↦ h (.inr hw)))
      have hgamma := regularizedGamma_pos (by positivity : 0 < (⌊x⌋₊ : ℝ) + 1) hrpos
      nlinarith [mul_pos (sub_pos.mpr hw) hgamma]
    · rw [Measure.cdf_map_natCast_of_neg _ (lt_of_not_ge hx)]
      exact zero_lt_one

/-- A probability hurdle Poisson law has lower quantile endpoint one at weight zero and
zero at every positive weight. At rate zero only weight one is admissible. -/
theorem tendsto_quantile_map_cast_poissonMeasure_cond_compl_zero_atomMixture_zero_nhdsGT_zero
    {r : ℝ≥0} (w : unitInterval) (h : r ≠ 0 ∨ w = 1) :
    Tendsto (fun u ↦ ((((Po(r)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (if w = 0 then 1 else 0)) := by
  classical
  by_cases hw : w = 1
  · simp [hw]
  have hr : r ≠ 0 := h.resolve_right hw
  by_cases hw0 : w = 0
  · simpa [hw0] using tendsto_quantile_map_cast_poissonMeasure_cond_compl_zero_nhdsGT_zero hr
  · rw [ite_eq_right hw0]
    refine tendsto_const_nhds.congr' ?_
    have hwpos : 0 < (w : ℝ) :=
      unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hw0)
    filter_upwards [Ioo_mem_nhdsGT hwpos] with u hu
    have hu1 : u < 1 := hu.2.trans_le w.2.2
    have hq := (Measure.quantile_map_natCast_cond_compl_zero_atomMixture_zero_eq_zero_iff
      Po(r) w (poissonMeasure_singleton_zero_eq_one_iff.not.mpr hr) ⟨hu.1, hu1⟩).2 hu.2.le
    simpa using congrArg (fun x : ℝ ↦ (x : EReal)) hq.symm

/-- A probability hurdle Poisson quantile has upper endpoint infinity unless its weight
is one, in which case the law is Dirac at zero, even at rate zero. -/
theorem tendsto_quantile_map_cast_poissonMeasure_cond_compl_zero_atomMixture_zero_nhdsLT_one
    {r : ℝ≥0} (w : unitInterval) (h : r ≠ 0 ∨ w = 1) :
    Tendsto (fun u ↦ ((((Po(r)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if w = 1 then 0 else ⊤)) := by
  classical
  by_cases hw : w = 1
  · simp [hw]
  have hr : r ≠ 0 := h.resolve_right hw
  let := isProbabilityMeasure_poissonMeasure_cond_compl_zero hr
  rw [ite_eq_right hw]
  apply Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one
  intro x
  by_cases hx : 0 ≤ x
  · rw [cdf_map_cast_poissonMeasure_cond_compl_zero_atomMixture_zero w hr hx]
    have hrpos : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    have hden : 0 < 1 - exp (-(r : ℝ)) := sub_pos.mpr (exp_lt_one_iff.mpr (neg_neg_of_pos hrpos))
    have hwpos : 0 < 1 - (w : ℝ) :=
      sub_pos.mpr (unitInterval.coe_lt_one.mpr (unitInterval.lt_one_iff_ne_one.mpr hw))
    have hgamma := regularizedGamma_pos (by positivity : 0 < (⌊x⌋₊ : ℝ) + 1) hrpos
    rw [mul_div_assoc]
    have hdiv : (1 - regularizedGamma (⌊x⌋₊ + 1) (r : ℝ) - exp (-(r : ℝ))) /
        (1 - exp (-(r : ℝ))) < 1 := (div_lt_one hden).2 (by linarith)
    have := mul_lt_mul_of_pos_left hdiv hwpos
    linarith
  · rw [Measure.cdf_map_natCast_of_neg _ (lt_of_not_ge hx)]
    exact zero_lt_one

end TauCeti.Probability
