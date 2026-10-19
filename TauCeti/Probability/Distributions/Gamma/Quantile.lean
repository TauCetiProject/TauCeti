/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.Gamma.Cdf
public import TauCeti.Probability.Quantile

/-!
# The inverse regularized gamma function

Since the regularized lower incomplete gamma function `P(s, ·)` is the cumulative distribution
function of the Gamma law with shape `s` and rate `1`, its inverse is that law's quantile function.
This file defines `TauCeti.inverseRegularizedGamma` through `MeasureTheory.Measure.quantile` and
specializes the general quantile API to it.

For `0 < s` and `0 < u < 1`, `TauCeti.inverseRegularizedGamma s u` is the unique positive `x` such
that `P(s, x) = u`. It is extended by `0` outside that parameter range.

## Main definition

* `TauCeti.inverseRegularizedGamma` — the inverse `P⁻¹(s, u)` in the argument, defined through the
  quantile of `ProbabilityTheory.gammaMeasure s 1`.

## Main results

* `TauCeti.inverseRegularizedGamma_eq_quantile` identifies the inverse with the Gamma quantile;
* `TauCeti.inverseRegularizedGamma_le_iff` is the Galois characterization
  `P⁻¹(s, u) ≤ x ↔ u ≤ P(s, x)`;
* `TauCeti.regularizedGamma_inverseRegularizedGamma` and
  `TauCeti.inverseRegularizedGamma_regularizedGamma` are the two inverse identities;
* `TauCeti.inverseRegularizedGamma_eq_iff` gives uniqueness of the positive root;
* `TauCeti.strictMonoOn_inverseRegularizedGamma`, `TauCeti.continuousOn_inverseRegularizedGamma`,
  `TauCeti.tendsto_inverseRegularizedGamma_nhdsGT_zero`,
  `TauCeti.tendsto_inverseRegularizedGamma_nhdsLT_one`, and
  `TauCeti.measurable_inverseRegularizedGamma` give regularity, endpoint limits, and joint
  measurability;
* `TauCeti.inverseRegularizedGamma_one` evaluates the inverse at shape `1`.
* `TauCeti.Probability.quantile_gammaMeasure` gives the quantile of a Gamma law of arbitrary
  positive rate by scaling `TauCeti.inverseRegularizedGamma`;
* `TauCeti.Probability.tendsto_quantile_gammaMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_gammaMeasure_nhdsLT_one` give its endpoint limits.

## References

* NIST Digital Library of Mathematical Functions, [§8.2](https://dlmf.nist.gov/8.2).
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Function Topology

namespace TauCeti

variable {s u x : ℝ}

/-- The inverse `P⁻¹(s, u)` of the regularized lower incomplete gamma function in its argument.

For positive `s` this is the quantile of the Gamma law with shape `s` and rate `1`. For
nonpositive `s` it is `0`; the quantile itself supplies the value `0` outside `0 < u < 1`. -/
def inverseRegularizedGamma (s u : ℝ) : ℝ :=
  if 0 < s then (gammaMeasure s 1).quantile u else 0

/-- For positive shape, `P⁻¹(s, ·)` is the quantile function of the Gamma law with shape `s` and
rate `1`. -/
theorem inverseRegularizedGamma_eq_quantile (hs : 0 < s) :
    inverseRegularizedGamma s u = (gammaMeasure s 1).quantile u :=
  ite_eq_left hs

/-- For positive shape, `P⁻¹(s, u)` is the infimum of the points at which `P(s, ·)` reaches
`u`. -/
theorem inverseRegularizedGamma_eq_sInf (hs : 0 < s) :
    inverseRegularizedGamma s u = sInf {x | u ≤ regularizedGamma s x} := by
  rw [inverseRegularizedGamma_eq_quantile hs, Measure.quantile_def]
  congr 1
  ext x
  simp only [mem_ofPred_eq]
  rw [TauCeti.Probability.cdf_gammaMeasure_eq hs one_pos, one_mul]

/-- Outside the valid range of the shape parameter, `P⁻¹(s, u)` is `0`. -/
@[simp]
theorem inverseRegularizedGamma_eq_zero_of_nonpos_left (hs : s ≤ 0) (u : ℝ) :
    inverseRegularizedGamma s u = 0 :=
  ite_eq_right (not_lt.2 hs)

/-- At levels `u ≤ 0`, `P⁻¹(s, u)` is `0`. -/
@[simp]
theorem inverseRegularizedGamma_eq_zero_of_nonpos_right (s : ℝ) (hu : u ≤ 0) :
    inverseRegularizedGamma s u = 0 := by
  by_cases hs : 0 < s
  · rw [inverseRegularizedGamma_eq_quantile hs, Measure.quantile_of_nonpos _ hu]
  · exact ite_eq_right hs

/-- At levels `1 ≤ u`, `P⁻¹(s, u)` is `0`. -/
@[simp]
theorem inverseRegularizedGamma_eq_zero_of_one_le (s : ℝ) (hu : 1 ≤ u) :
    inverseRegularizedGamma s u = 0 := by
  by_cases hs : 0 < s
  · rw [inverseRegularizedGamma_eq_quantile hs, Measure.quantile_def]
    have hset : {x : ℝ | u ≤ cdf (gammaMeasure s 1) x} = ∅ := by
      apply eq_empty_of_forall_notMem
      intro x hx
      simp only [mem_ofPred_eq] at hx
      rw [TauCeti.Probability.cdf_gammaMeasure_eq hs one_pos, one_mul] at hx
      exact (not_le_of_gt (regularizedGamma_lt_one s x)) (hu.trans hx)
    rw [hset, Real.sInf_empty]
  · exact ite_eq_right hs

/-- `P⁻¹(s, u)` is `0` whenever `s` or `u` lies outside the valid range `0 < s`, `0 < u < 1`. -/
theorem inverseRegularizedGamma_eq_zero_of_not (h : ¬(0 < s ∧ u ∈ Ioo 0 1)) :
    inverseRegularizedGamma s u = 0 := by
  rcases not_and_or.mp h with hs | hu
  · exact inverseRegularizedGamma_eq_zero_of_nonpos_left (le_of_not_gt hs) u
  · simp only [mem_Ioo, not_and_or, not_lt] at hu
    rcases hu with hu | hu
    · exact inverseRegularizedGamma_eq_zero_of_nonpos_right s hu
    · exact inverseRegularizedGamma_eq_zero_of_one_le s hu

private theorem strictMonoOn_cdf_gammaMeasure (hs : 0 < s) :
    StrictMonoOn (cdf (gammaMeasure s 1)) (cdf (gammaMeasure s 1) ⁻¹' Ioo 0 1) := by
  have h : ⇑(cdf (gammaMeasure s 1)) = regularizedGamma s :=
    funext fun x => by rw [TauCeti.Probability.cdf_gammaMeasure_eq hs one_pos, one_mul]
  rw [h]
  exact (strictMonoOn_regularizedGamma hs).mono fun x hx =>
    mem_Ici.2 ((regularizedGamma_pos_iff hs).1 hx.1).le

/-- The points at which `P(s, ·)` reaches a level `u ∈ (0, 1)` form the closed ray starting at
`P⁻¹(s, u)`. -/
theorem setOf_le_regularizedGamma_eq_Ici (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    {x | u ≤ regularizedGamma s x} = Ici (inverseRegularizedGamma s u) := by
  have h := Measure.setOf_le_cdf_eq_Ici (gammaMeasure s 1) hu.1 hu.2
  simpa [inverseRegularizedGamma_eq_quantile hs,
    TauCeti.Probability.cdf_gammaMeasure_eq hs one_pos] using h

/-- The Galois characterization of `P⁻¹(s, ·)`: for a level `u ∈ (0, 1)`, `P⁻¹(s, u) ≤ x` exactly
when `u ≤ P(s, x)`. -/
theorem inverseRegularizedGamma_le_iff (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    inverseRegularizedGamma s u ≤ x ↔ u ≤ regularizedGamma s x := by
  rw [inverseRegularizedGamma_eq_quantile hs,
    Measure.quantile_le_iff (gammaMeasure s 1) hu.1 hu.2,
    TauCeti.Probability.cdf_gammaMeasure_eq hs one_pos, one_mul]

/-- The negation of `TauCeti.inverseRegularizedGamma_le_iff`. -/
theorem lt_inverseRegularizedGamma_iff (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    x < inverseRegularizedGamma s u ↔ regularizedGamma s x < u := by
  rw [inverseRegularizedGamma_eq_quantile hs,
    Measure.lt_quantile_iff (gammaMeasure s 1) hu.1 hu.2,
    TauCeti.Probability.cdf_gammaMeasure_eq hs one_pos, one_mul]

/-- `P⁻¹(s, u)` is positive, for `0 < s` and `0 < u < 1`. -/
theorem inverseRegularizedGamma_pos (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    0 < inverseRegularizedGamma s u := by
  rw [lt_inverseRegularizedGamma_iff hs hu, regularizedGamma_eq_zero_of_nonpos_right s le_rfl]
  exact hu.1

/-- `P⁻¹(s, u)` is nonnegative, for every parameter value. -/
theorem inverseRegularizedGamma_nonneg (s u : ℝ) : 0 ≤ inverseRegularizedGamma s u := by
  by_cases h : 0 < s ∧ u ∈ Ioo 0 1
  · exact (inverseRegularizedGamma_pos h.1 h.2).le
  · rw [inverseRegularizedGamma_eq_zero_of_not h]

/-- `P⁻¹(s, ·)` is a right inverse of `P(s, ·)` on the levels `0 < u < 1`. -/
@[simp]
theorem regularizedGamma_inverseRegularizedGamma (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    regularizedGamma s (inverseRegularizedGamma s u) = u := by
  have h := Measure.cdf_quantile _ (TauCeti.Probability.continuous_cdf_gammaMeasure hs one_pos)
    hu.1 hu.2
  rwa [TauCeti.Probability.cdf_gammaMeasure_eq hs one_pos, one_mul,
    ← inverseRegularizedGamma_eq_quantile hs] at h

/-- The strict form of `TauCeti.inverseRegularizedGamma_le_iff`. -/
theorem inverseRegularizedGamma_lt_iff (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    inverseRegularizedGamma s u < x ↔ u < regularizedGamma s x := by
  rw [inverseRegularizedGamma_eq_quantile hs, Measure.quantile_lt_iff _
    (TauCeti.Probability.continuous_cdf_gammaMeasure hs one_pos) (strictMonoOn_cdf_gammaMeasure hs)
    hu.1 hu.2,
    TauCeti.Probability.cdf_gammaMeasure_eq hs one_pos, one_mul]

/-- Uniqueness: for `0 < s` and `0 < u < 1`, the only solution of `P(s, x) = u` is
`x = P⁻¹(s, u)`. -/
theorem inverseRegularizedGamma_eq_iff (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    inverseRegularizedGamma s u = x ↔ regularizedGamma s x = u := by
  refine ⟨fun h => h ▸ regularizedGamma_inverseRegularizedGamma hs hu, fun hx => ?_⟩
  have hx0 : 0 < x := (regularizedGamma_pos_iff hs).1 (hx ▸ hu.1)
  refine (strictMonoOn_regularizedGamma hs).injOn (inverseRegularizedGamma_pos hs hu).le
    (mem_Ici.2 hx0.le) ?_
  rw [regularizedGamma_inverseRegularizedGamma hs hu, hx]

/-- `P⁻¹(s, ·)` is a left inverse of `P(s, ·)` on the open half-line `0 < x`. -/
@[simp]
theorem inverseRegularizedGamma_regularizedGamma (hs : 0 < s) (hx : 0 < x) :
    inverseRegularizedGamma s (regularizedGamma s x) = x :=
  (inverseRegularizedGamma_eq_iff hs ⟨regularizedGamma_pos hs hx, regularizedGamma_lt_one s x⟩).2
    rfl

/-- `P⁻¹(s, ·)` is strictly increasing on the levels `0 < u < 1`. -/
theorem strictMonoOn_inverseRegularizedGamma (hs : 0 < s) :
    StrictMonoOn (inverseRegularizedGamma s) (Ioo 0 1) := fun a ha b hb hab => by
  simpa only [inverseRegularizedGamma_eq_quantile hs] using Measure.strictMonoOn_quantile _
    (TauCeti.Probability.continuous_cdf_gammaMeasure hs one_pos) ha hb hab

/-- `P⁻¹(s, ·)` is continuous on the levels `0 < u < 1`. -/
theorem continuousOn_inverseRegularizedGamma (hs : 0 < s) :
    ContinuousOn (inverseRegularizedGamma s) (Ioo 0 1) :=
  (Measure.continuousOn_quantile _ (TauCeti.Probability.continuous_cdf_gammaMeasure hs one_pos)
    (strictMonoOn_cdf_gammaMeasure hs)).congr fun _ _ => inverseRegularizedGamma_eq_quantile hs

/-- `P⁻¹(s, u)` tends to `0` from above as the level `u` decreases to `0`. -/
theorem tendsto_inverseRegularizedGamma_nhdsGT_zero (hs : 0 < s) :
    Tendsto (inverseRegularizedGamma s) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun u =>
    ha.trans_le (inverseRegularizedGamma_nonneg s u), fun b hb => ?_⟩, ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT (regularizedGamma_pos hs hb)] with u hu
    exact (inverseRegularizedGamma_lt_iff hs
      ⟨hu.1, hu.2.trans (regularizedGamma_lt_one s b)⟩).2 hu.2
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with u hu
    exact inverseRegularizedGamma_pos hs hu

/-- `P⁻¹(s, u)` tends to `∞` as the level `u` increases to `1`. -/
theorem tendsto_inverseRegularizedGamma_nhdsLT_one (hs : 0 < s) :
    Tendsto (inverseRegularizedGamma s) (𝓝[<] 1) atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [Ioo_mem_nhdsLT (regularizedGamma_lt_one s b)] with u hu
  refine not_lt.1 fun h => lt_asymm hu.1 ?_
  exact (inverseRegularizedGamma_lt_iff hs
    ⟨(regularizedGamma_nonneg s b).trans_lt hu.1, hu.2⟩).1 h

/-- `P⁻¹(s, u)` is jointly measurable in the shape parameter and the level, including outside
the valid parameter range. -/
@[fun_prop]
theorem measurable_inverseRegularizedGamma :
    Measurable fun p : ℝ × ℝ => inverseRegularizedGamma p.1 p.2 := by
  have hV : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.2 ∈ Ioo 0 1} :=
    (measurableSet_lt measurable_const measurable_fst).inter (measurable_snd measurableSet_Ioo)
  refine measurable_of_Iic fun x => ?_
  -- On the valid range the sublevel sets come from the Galois characterization; off it the
  -- function is the constant `0`.
  have hpre : (fun p : ℝ × ℝ => inverseRegularizedGamma p.1 p.2) ⁻¹' Iic x =
      ({p | 0 < p.1 ∧ p.2 ∈ Ioo 0 1} ∩ {p | p.2 ≤ regularizedGamma p.1 x}) ∪
        ({p | 0 < p.1 ∧ p.2 ∈ Ioo 0 1}ᶜ ∩ {_p | 0 ≤ x}) := by
    ext ⟨s, u⟩
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
    by_cases h : 0 < s ∧ u ∈ Ioo 0 1
    · rw [inverseRegularizedGamma_le_iff h.1 h.2]
      tauto
    · rw [inverseRegularizedGamma_eq_zero_of_not h]
      tauto
  rw [hpre]
  exact (hV.inter (measurableSet_le measurable_snd (by fun_prop))).union
    (hV.compl.inter (MeasurableSet.const _))

/-- At shape `1`, `P⁻¹(1, u) = -log (1 - u)`: the inverse of the standard exponential cdf. -/
theorem inverseRegularizedGamma_one (hu : u ∈ Ioo 0 1) :
    inverseRegularizedGamma 1 u = -Real.log (1 - u) := by
  have h1u : 0 < 1 - u := sub_pos.2 hu.2
  rw [inverseRegularizedGamma_eq_iff one_pos hu,
    regularizedGamma_one (neg_nonneg.2 (Real.log_nonpos h1u.le (by linarith [hu.1]))),
    neg_neg, Real.exp_log h1u, sub_sub_cancel]

namespace Probability

variable {a r : ℝ}

/-- The quantile of a Gamma law with positive shape `a` and rate `r` is
`P⁻¹(a, u) / r`, where `P⁻¹` is the inverse regularized lower incomplete Gamma function. -/
theorem quantile_gammaMeasure (ha : 0 < a) (hr : 0 < r) (hu : u ∈ Ioo 0 1) :
    (gammaMeasure a r).quantile u = inverseRegularizedGamma a u / r := by
  apply le_antisymm
  · rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_gammaMeasure_eq ha hr,
      mul_div_cancel₀ _ hr.ne', regularizedGamma_inverseRegularizedGamma ha hu]
  · rw [div_le_iff₀ hr]
    exact (inverseRegularizedGamma_le_iff ha hu).2 <| by
      simpa only [cdf_gammaMeasure_eq ha hr, mul_comm] using Measure.le_cdf_quantile
        (gammaMeasure a r) hu.2

/-- The quantile of a positive-parameter Gamma law tends to the lower support endpoint `0` as
the level tends to `0` from above. -/
theorem tendsto_quantile_gammaMeasure_nhdsGT_zero (ha : 0 < a) (hr : 0 < r) :
    Tendsto (fun u ↦ (gammaMeasure a r).quantile u) (𝓝[>] 0) (𝓝[>] 0) := by
  have hlim : Tendsto (fun u ↦ inverseRegularizedGamma a u / r) (𝓝[>] 0) (𝓝[>] 0) := by
    simpa only [div_eq_inv_mul, mul_comm, mul_zero] using
      Filter.TendstoNhdsWithinIoi.const_mul (inv_pos.mpr hr)
        (tendsto_inverseRegularizedGamma_nhdsGT_zero ha)
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT one_pos] with u hu
  exact (quantile_gammaMeasure ha hr hu).symm

/-- The quantile of a positive-parameter Gamma law tends to infinity as the level tends to `1`
from below. -/
theorem tendsto_quantile_gammaMeasure_nhdsLT_one (ha : 0 < a) (hr : 0 < r) :
    Tendsto (fun u ↦ (gammaMeasure a r).quantile u) (𝓝[<] 1) atTop := by
  have hlim : Tendsto (fun u ↦ inverseRegularizedGamma a u / r) (𝓝[<] 1) atTop :=
    (tendsto_inverseRegularizedGamma_nhdsLT_one ha).atTop_div_const hr
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_gammaMeasure ha hr hu).symm

end Probability

end TauCeti

end
