/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Geometric.Cdf
public import TauCeti.Probability.Quantile
public import Mathlib.Topology.Instances.EReal.Lemmas

import TauCeti.Probability.Distributions.Dirac
import TauCeti.Probability.Distributions.NegativeBinomial.Basic

/-!
# Quantiles of geometric laws

The geometric law counts failures before the first success. For success probability strictly
between zero and one, its real-cast lower quantile at an interior level `u` is
`⌈log (1 - u) / log (1 - p)⌉₊ - 1`, with natural subtraction before casting to the reals.
The ratio is positive, so the natural ceiling agrees with the integer ceiling.
At a cumulative-mass jump the quantile selects the smaller integer.

Both success-probability endpoints have quantile zero: probability one gives immediate success,
and Mathlib totalizes probability zero as a Dirac law at zero. All lower endpoint limits are zero;
the upper endpoint limit is positive infinity exactly for the nondegenerate laws.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed.,
  Wiley, 2005, Chapter 5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

/-- The geometric lower quantile is the ceiling of the logarithmic cumulative crossing,
minus one. The subtraction takes place in `ℕ` before casting to `ℝ`. -/
@[simp]
theorem quantile_map_cast_geometricMeasure {p : unitInterval} (hp : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)).quantile u =
      ((⌈Real.log (1 - u) / Real.log (1 - (p : ℝ))⌉₊ - 1 : ℕ) : ℝ) := by
  have hp0 : p ≠ 0 := unitInterval.pos_iff_ne_zero.mp (unitInterval.coe_pos.mp hp)
  have hq : 0 < 1 - (p : ℝ) := sub_pos.mpr hp1
  have hlog : Real.log (1 - (p : ℝ)) < 0 := Real.log_neg hq (by linarith)
  have hr : 0 < Real.log (1 - u) / Real.log (1 - (p : ℝ)) :=
    div_pos_of_neg_of_neg (Real.log_neg (sub_pos.mpr hu.2) (sub_lt_self _ hu.1)) hlog
  have hceil := Nat.ceil_pos.mpr hr
  have hcross (k : ℕ) :
      u ≤ 1 - (1 - (p : ℝ)) ^ (k + 1) ↔
        ⌈Real.log (1 - u) / Real.log (1 - (p : ℝ))⌉₊ - 1 ≤ k := by
    calc
      u ≤ 1 - (1 - (p : ℝ)) ^ (k + 1) ↔
          (1 - (p : ℝ)) ^ (k + 1) ≤ 1 - u := by constructor <;> intro h <;> linarith
      _ ↔ Real.log ((1 - (p : ℝ)) ^ (k + 1)) ≤ Real.log (1 - u) :=
        (Real.log_le_log_iff (pow_pos hq _) (sub_pos.mpr hu.2)).symm
      _ ↔ Real.log (1 - u) / Real.log (1 - (p : ℝ)) ≤ ((k + 1 : ℕ) : ℝ) := by
        rw [Real.log_pow, div_le_iff_of_neg hlog]
      _ ↔ ⌈Real.log (1 - u) / Real.log (1 - (p : ℝ))⌉₊ ≤ k + 1 := Nat.ceil_le.symm
      _ ↔ ⌈Real.log (1 - u) / Real.log (1 - (p : ℝ))⌉₊ - 1 ≤ k := by omega
  refine eq_of_forall_ge_iff fun x ↦ ?_
  rw [Measure.quantile_le_iff _ hu.1 hu.2]
  by_cases hx : 0 ≤ x
  · rw [cdf_map_cast_geometricMeasure hp0 hx, hcross, Nat.le_floor_iff hx]
  · rw [Measure.cdf_map_natCast_of_neg _ (lt_of_not_ge hx)]
    exact iff_of_false (not_le.mpr hu.1)
      (not_le.mpr ((lt_of_not_ge hx).trans_le (Nat.cast_nonneg _)))

/-- At success probability zero, Mathlib's totalized geometric law has quantile zero. -/
@[simp]
theorem quantile_map_cast_geometricMeasure_zero {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)).quantile u = 0 := by
  simp [geometricMeasure_zero, Measure.quantile_dirac 0 hu.1 hu.2.le]

/-- At success probability one there are no failures, so the geometric quantile is zero. -/
@[simp]
theorem quantile_map_cast_geometricMeasure_one {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((geometricMeasure (1 : unitInterval)).map (Nat.cast : ℕ → ℝ)).quantile u = 0 := by
  rw [geometricMeasure_eq_negativeBinomialMeasure_one _ (by norm_num)]
  simp [negativeBinomialMeasure_eq_dirac_of_successProbability_eq_one zero_le_one,
    Measure.quantile_dirac 0 hu.1 hu.2.le]

/-- Every real-cast geometric law has lower support endpoint zero, including both Dirac
boundaries. -/
theorem tendsto_quantile_map_cast_geometricMeasure_nhdsGT_zero (p : unitInterval) :
    Tendsto ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)).quantile (𝓝[>] 0) (𝓝 0) := by
  by_cases hp : p = 0
  · subst p
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    exact (quantile_map_cast_geometricMeasure_zero hu).symm
  have hp0 : 0 < (p : ℝ) := unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp)
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT hp0] with u hu
  have hu1 : u < 1 := hu.2.trans_le p.2.2
  have hnonneg : 0 ≤ ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)).quantile u :=
    ordConnected_Ici.quantile_mem
      ((ae_map_iff (by fun_prop) measurableSet_Ici).2
        (Eventually.of_forall fun k : ℕ ↦ Nat.cast_nonneg k)) hu.1 hu1
  have hle : ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)).quantile u ≤ 0 := by
    rw [Measure.quantile_le_iff _ hu.1 hu1, cdf_map_cast_geometricMeasure hp le_rfl]
    simpa using hu.2.le
  exact (le_antisymm hle hnonneg).symm

/-- The upper support endpoint of a real-cast geometric law is positive infinity except at
success probability zero or one, where the law is concentrated at zero. -/
theorem tendsto_quantile_map_cast_geometricMeasure_nhdsLT_one (p : unitInterval) :
    Tendsto (fun u ↦
      (((geometricMeasure p).map (Nat.cast : ℕ → ℝ)).quantile u : EReal)) (𝓝[<] 1)
      (𝓝 (if p = 0 ∨ p = 1 then (0 : EReal) else ⊤)) := by
  by_cases hp : p = 0 ∨ p = 1
  · rw [ite_eq_left hp]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rcases hp with rfl | rfl <;> simp [hu]
  · rw [ite_eq_right hp]
    have hp0 : p ≠ 0 := fun h ↦ hp (Or.inl h)
    have hp1 : (p : ℝ) < 1 :=
      unitInterval.coe_lt_one.mpr (unitInterval.lt_one_iff_ne_one.mpr (fun h ↦ hp (Or.inr h)))
    apply EReal.tendsto_coe_nhds_top_iff.2
    refine tendsto_atTop.2 fun b ↦ ?_
    have hb : cdf ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) b < 1 := by
      by_cases hb : 0 ≤ b
      · rw [cdf_map_cast_geometricMeasure hp0 hb]
        exact sub_lt_self _ (pow_pos (sub_pos.mpr hp1) _)
      · rw [Measure.cdf_map_natCast_of_neg _ (lt_of_not_ge hb)]
        exact zero_lt_one
    filter_upwards [Ioo_mem_nhdsLT hb] with u hu
    exact ((Measure.lt_quantile_iff _
      ((cdf_nonneg _ b).trans_lt hu.1) hu.2).2 hu.1).le

end TauCeti.Probability
