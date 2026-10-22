/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Tail
public import TauCeti.Probability.Quantile.Discrete
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of Poisson laws

At an interior probability level, the lower quantile of the real cast of a Poisson law is the
least natural number whose explicit cumulative mass reaches the level. Equivalently, it is the
least index at which the regularized lower incomplete Gamma function is at most the complementary
level.
Both characterizations retain equality at a cumulative jump, as required for lower quantiles.

The quantile is zero through the mass `exp (-r)` of the origin. Its one-sided limit at level
zero is therefore zero for every nonnegative rate. At level one the limit is positive infinity
for positive rate, and zero at the rate-zero Dirac boundary.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped NNReal Nat

namespace TauCeti.Probability

variable {r : ℝ≥0} {u : ℝ}

/-- A natural number is the Poisson lower quantile exactly when it is the least index whose
explicit cumulative mass reaches the interior probability level. -/
theorem quantile_map_cast_poissonMeasure_eq_iff (r : ℝ≥0) (hu : u ∈ Ioo 0 1) (k : ℕ) :
    Po(ℝ, r).quantile u = k ↔
      IsLeast {n : ℕ | u ≤ ∑ j ∈ Finset.range (n + 1),
        exp (-(r : ℝ)) * (r : ℝ) ^ j / (j)!} k := by
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  simp_rw [poissonMeasure_real_Iic, ← sum_range_poissonMeasure_real_singleton,
    poissonMeasure_real_singleton]

/-- The complementary incomplete-Gamma criterion for a Poisson quantile, including equality
at an attained cumulative mass and the zero-rate boundary. -/
theorem quantile_map_cast_poissonMeasure_eq_iff_regularizedGamma (r : ℝ≥0)
    (hu : u ∈ Ioo 0 1) (k : ℕ) :
    Po(ℝ, r).quantile u = k ↔
      IsLeast {n : ℕ | regularizedGamma (n + 1) (r : ℝ) ≤ 1 - u} k := by
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  simp_rw [poissonMeasure_real_Iic, le_sub_comm]

/-- The initial constant segment of a Poisson quantile ends at the mass of zero. -/
@[simp]
theorem quantile_map_cast_poissonMeasure_eq_zero_iff (r : ℝ≥0) (hu : u ∈ Ioo 0 1) :
    Po(ℝ, r).quantile u = 0 ↔ u ≤ exp (-(r : ℝ)) := by
  simpa [IsLeast, lowerBounds] using quantile_map_cast_poissonMeasure_eq_iff r hu 0

/-- The rate-zero Poisson law has zero quantile at every interior probability level. -/
@[simp]
theorem quantile_map_cast_poissonMeasure_zero (hu : u ∈ Ioo 0 1) :
    Po(ℝ, 0).quantile u = 0 :=
  (quantile_map_cast_poissonMeasure_eq_zero_iff 0 hu).2 (by simpa using hu.2.le)

/-- Poisson quantiles tend to the lower support endpoint zero as the level tends to zero
from above, for every nonnegative rate. -/
theorem tendsto_quantile_map_cast_poissonMeasure_nhdsGT_zero (r : ℝ≥0) :
    Tendsto (fun u ↦ (Po(ℝ, r).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (exp_pos (-(r : ℝ)))] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 :=
    ⟨hu.1, hu.2.trans_le (exp_le_one_iff.mpr (neg_nonpos.mpr r.coe_nonneg))⟩
  exact congrArg (fun x : ℝ ↦ (x : EReal))
    ((quantile_map_cast_poissonMeasure_eq_zero_iff r hu').2 hu.2.le).symm

/-- Poisson quantiles tend to the upper support endpoint as the level tends to one from
below: infinity at positive rate, and zero at rate zero. -/
theorem tendsto_quantile_map_cast_poissonMeasure_nhdsLT_one (r : ℝ≥0) :
    Tendsto (fun u ↦ (Po(ℝ, r).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if r = 0 then 0 else ⊤)) := by
  by_cases hr : r = 0
  · simp only [hr, ite_true]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    simp [quantile_map_cast_poissonMeasure_zero hu]
  · rw [ite_eq_right hr, EReal.tendsto_coe_nhds_top_iff]
    refine tendsto_atTop.2 fun b ↦ ?_
    have hb : cdf Po(ℝ, r) b < 1 := by
      by_cases hb0 : 0 ≤ b
      · rw [cdf_map_cast_poissonMeasure r hb0]
        exact sub_lt_self _ (regularizedGamma_pos (by positivity)
          (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)))
      · rw [cdf_map_cast_poissonMeasure_of_neg r (lt_of_not_ge hb0)]
        exact zero_lt_one
    filter_upwards [Ioo_mem_nhdsLT hb] with u hu
    exact ((Measure.lt_quantile_iff _ ((cdf_nonneg Po(ℝ, r) b).trans_lt hu.1) hu.2).2 hu.1).le

end TauCeti.Probability
