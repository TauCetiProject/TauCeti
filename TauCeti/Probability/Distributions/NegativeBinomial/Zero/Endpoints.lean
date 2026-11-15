/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NegativeBinomial.Zero.Inflated
public import TauCeti.Probability.Distributions.NegativeBinomial.Zero.Hurdle

/-!
# Quantile endpoints of zero-modified negative-binomial laws

For positive shape and success probability strictly between zero and one, the zero-truncated
negative-binomial quantile has lower endpoint one and upper endpoint positive infinity.

The real-cast zero-inflated negative-binomial law has lower quantile endpoint zero. Its upper
endpoint is positive infinity unless the shape is zero, the success probability is one, or the
inflation weight is one, in which cases the law is Dirac at zero.

For a negative-binomial hurdle law, the lower endpoint is one at zero hurdle weight and zero
at positive weight. The upper endpoint is positive infinity except at weight one. The hurdle
statements cover its whole probability range, including weight one even when truncation removes
all mass from the base law. All limits are taken through interior probability levels in `EReal`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, section 8.2.3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped unitInterval

namespace TauCeti.Probability

variable {r p : ℝ} (w : unitInterval)

/-- Zero-truncated negative-binomial quantiles tend to one as the level tends to zero
from above. -/
theorem tendsto_quantile_map_cast_negativeBinomialMeasure_cond_compl_zero_nhdsGT_zero
    (hr : 0 < r) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun u ↦
      ((((negativeBinomialMeasure r p)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 1) := by
  have := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  exact (negativeBinomialMeasure r p).tendsto_quantile_map_natCast_cond_compl_zero_nhdsGT_zero
    ((negativeBinomialMeasure_singleton_ne_zero_iff hr.le hp hp1.le 1).2 (Or.inr ⟨hr, hp1⟩))

/-- Zero-truncated negative-binomial quantiles tend to positive infinity as the level tends
to one from below. -/
theorem tendsto_quantile_map_cast_negativeBinomialMeasure_cond_compl_zero_nhdsLT_one
    (hr : 0 < r) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun u ↦
      ((((negativeBinomialMeasure r p)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  have := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  apply (negativeBinomialMeasure r p).tendsto_quantile_map_natCast_cond_compl_zero_nhdsLT_one
  simpa [hr.ne', hp1.ne] using
    tendsto_quantile_map_cast_negativeBinomialMeasure_nhdsLT_one hr.le hp hp1.le

/-- Every valid zero-inflated negative-binomial law has lower quantile endpoint zero,
including the shape-zero, success-probability-one, and weight-one Dirac boundaries. -/
theorem tendsto_quantile_map_cast_negativeBinomialMeasure_atomMixture_zero_nhdsGT_zero
    (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1) :
    Tendsto (fun u ↦
      ((((negativeBinomialMeasure r p).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u :
        EReal)) (𝓝[>] 0) (𝓝 0) := by
  have hmass : 0 < (w : ℝ) + (1 - (w : ℝ)) * p ^ r := by
    have hpow := rpow_pos_of_pos hp r
    by_cases hw : (w : ℝ) = 1
    · simp [hw]
    · have hden : 0 < 1 - (w : ℝ) := sub_pos.mpr (lt_of_le_of_ne w.2.2 hw)
      exact add_pos_of_nonneg_of_pos w.2.1 (mul_pos hden hpow)
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT (lt_min hmass zero_lt_one)] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le (min_le_right _ _)⟩
  rw [(quantile_map_cast_negativeBinomialMeasure_atomMixture_zero_eq_zero_iff w hr hp hp1 hu').2
    (hu.2.le.trans (min_le_left _ _))]
  rfl

open scoped Classical in
/-- The upper quantile endpoint of a valid zero-inflated negative-binomial law is infinite
exactly when the shape is positive, the success probability is below one, and the inflation
weight is below one. -/
theorem tendsto_quantile_map_cast_negativeBinomialMeasure_atomMixture_zero_nhdsLT_one
    (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1) :
    Tendsto (fun u ↦
      ((((negativeBinomialMeasure r p).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u :
        EReal)) (𝓝[<] 1) (𝓝 (if r = 0 ∨ p = 1 ∨ w = 1 then (0 : EReal) else ⊤)) := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  by_cases hdeg : r = 0 ∨ p = 1 ∨ w = 1
  · rw [ite_eq_left hdeg]
    have hmass : (w : ℝ) + (1 - (w : ℝ)) * p ^ r = 1 := by
      rcases hdeg with hr0 | hpone | hw
      · simp [hr0]
      · simp [hpone]
      · simp [hw]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rw [(quantile_map_cast_negativeBinomialMeasure_atomMixture_zero_eq_zero_iff w hr hp hp1 hu).2
      (by linarith [hu.2])]
    rfl
  · rw [ite_eq_right hdeg]
    have hr0 : 0 < r := lt_of_le_of_ne hr (by tauto)
    have hpone : p < 1 := lt_of_le_of_ne hp1 (by tauto)
    have hw : (w : ℝ) < 1 :=
      lt_of_le_of_ne w.2.2 (unitInterval.coe_ne_one.2 (by tauto))
    apply Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one
    intro x
    by_cases hx : 0 ≤ x
    · rw [cdf_map_cast_negativeBinomialMeasure_atomMixture_zero w hr0 hp hp1 hx]
      have hbeta : regularizedIncompleteBeta r (⌊x⌋₊ + 1) p < 1 :=
        (regularizedIncompleteBeta_lt_one_iff hr0 (by positivity)).2 hpone
      nlinarith
    · rw [Measure.cdf_map_natCast_of_neg _ (lt_of_not_ge hx)]
      exact zero_lt_one

open scoped Classical in
/-- The lower quantile endpoint of a probability negative-binomial hurdle law is one at zero
hurdle weight and zero at positive weight. Weight one is allowed for arbitrary base parameters. -/
theorem
    tendsto_quantile_map_cast_negativeBinomialMeasure_cond_compl_zero_atomMixture_zero_nhdsGT_zero
    (h : (0 < r ∧ 0 < p ∧ p < 1) ∨ w = 1) :
    Tendsto (fun u ↦
      (((((negativeBinomialMeasure r p)[|{0}ᶜ]).atomMixture 0 w).map
        (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (if w = 0 then (1 : EReal) else 0)) := by
  rcases h with ⟨hr, hp, hp1⟩ | rfl
  · let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
    let _ := isProbabilityMeasure_negativeBinomialMeasure_cond_compl_zero hr hp hp1
    by_cases hw : w = 0
    · simpa [hw] using
        tendsto_quantile_map_cast_negativeBinomialMeasure_cond_compl_zero_nhdsGT_zero hr hp hp1
    · rw [ite_eq_right hw]
      have hwpos : 0 < (w : ℝ) :=
        lt_of_le_of_ne w.2.1 (unitInterval.coe_ne_zero.2 hw).symm
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT (lt_min hwpos zero_lt_one)] with u hu
      have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le (min_le_right _ _)⟩
      rw [(Measure.quantile_map_natCast_cond_compl_zero_atomMixture_zero_eq_zero_iff _ _
        (negativeBinomialMeasure_singleton_zero_ne_one hr hp hp1) hu').2
          (hu.2.le.trans (min_le_left _ _))]
      rfl
  · simp only [one_ne_zero, ite_false, Measure.atomMixture_one]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    simp [Measure.quantile_dirac 0 hu.1 hu.2.le]

open scoped Classical in
/-- The upper quantile endpoint of a probability negative-binomial hurdle law is positive
infinity at weight below one and zero at weight one, including degenerate base parameters. -/
theorem
    tendsto_quantile_map_cast_negativeBinomialMeasure_cond_compl_zero_atomMixture_zero_nhdsLT_one
    (h : (0 < r ∧ 0 < p ∧ p < 1) ∨ w = 1) :
    Tendsto (fun u ↦
      (((((negativeBinomialMeasure r p)[|{0}ᶜ]).atomMixture 0 w).map
        (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if w = 1 then (0 : EReal) else ⊤)) := by
  by_cases hw : w = 1
  · simp only [hw, Measure.atomMixture_one]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    simp [Measure.quantile_dirac 0 hu.1 hu.2.le]
  · rw [ite_eq_right hw]
    obtain ⟨hr, hp, hp1⟩ := h.resolve_right hw
    let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
    let _ := isProbabilityMeasure_negativeBinomialMeasure_cond_compl_zero hr hp hp1
    have hwlt : (w : ℝ) < 1 := lt_of_le_of_ne w.2.2 (unitInterval.coe_ne_one.2 hw)
    have hden : 0 < 1 - p ^ r := sub_pos.mpr (rpow_lt_one hp.le hp1 hr)
    apply Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one
    intro x
    by_cases hx : 0 ≤ x
    · rw [cdf_map_cast_negativeBinomialMeasure_cond_compl_zero_atomMixture_zero w hr hp hp1 hx]
      have hbeta : regularizedIncompleteBeta r (⌊x⌋₊ + 1) p < 1 :=
        (regularizedIncompleteBeta_lt_one_iff hr (by positivity)).2 hp1
      have hratio : (regularizedIncompleteBeta r (⌊x⌋₊ + 1) p - p ^ r) / (1 - p ^ r) < 1 :=
        (div_lt_one hden).2 (by linarith)
      rw [mul_div_assoc]
      nlinarith
    · rw [Measure.cdf_map_natCast_of_neg _ (lt_of_not_ge hx)]
      exact zero_lt_one

end TauCeti.Probability
