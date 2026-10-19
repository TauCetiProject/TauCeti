/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Mixed.Basic
public import TauCeti.Probability.Quantile.Discrete
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of mixed Poisson laws

An interior quantile of a real-cast mixed Poisson law is the least natural number whose
Poisson-mixture cumulative mass reaches the level. This retains equality at an attained
cumulative mass, as required for lower quantiles.

The quantile is zero through the mixed mass at zero, the expectation of `exp (-Λ)`. This mass
is strictly positive for every probability mixing law, so mixed Poisson quantiles converge to
zero as the level tends to zero from above.

## References

* J. Grandell, *Mixed Poisson Processes*, Chapman & Hall (1997), ch. 2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open TauCeti.Probability
open scoped NNReal Nat

namespace MeasureTheory.Measure

variable {u : ℝ}

/-- A natural number is the mixed Poisson lower quantile exactly when it is the least index whose
explicit cumulative mass reaches the interior probability level. -/
theorem quantile_map_cast_mixedPoissonMeasure_eq_iff (ρ : Measure ℝ≥0)
    [IsProbabilityMeasure ρ] (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((mixedPoissonMeasure ρ).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {n : ℕ | u ≤ ∑ j ∈ Finset.range (n + 1),
        ∫ x, (exp (-(x : ℝ)) * (x : ℝ) ^ j / j !) ∂ρ} k := by
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  simp_rw [mixedPoissonMeasure_real_Iic]

/-- The mixed Poisson quantile is zero exactly through its mass at zero, the expectation of
`exp (-Λ)` under the mixing law. -/
@[simp]
theorem quantile_map_cast_mixedPoissonMeasure_eq_zero_iff (ρ : Measure ℝ≥0)
    [IsProbabilityMeasure ρ] (hu : u ∈ Ioo 0 1) :
    ((mixedPoissonMeasure ρ).map (Nat.cast : ℕ → ℝ)).quantile u = 0 ↔
      u ≤ ∫ x, exp (-(x : ℝ)) ∂ρ := by
  simpa [IsLeast, lowerBounds] using
    quantile_map_cast_mixedPoissonMeasure_eq_iff ρ hu 0

/-- Mixed Poisson quantiles tend to the lower support endpoint zero as the level tends to zero
from above, for every probability mixing law. -/
theorem tendsto_quantile_map_cast_mixedPoissonMeasure_nhdsGT_zero
    (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] :
    Tendsto (fun u ↦
      (((mixedPoissonMeasure ρ).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  have hint : Integrable (fun x : ℝ≥0 ↦ exp (-(x : ℝ))) ρ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (neg_nonpos.mpr x.coe_nonneg)
  have hmass : 0 < ∫ x : ℝ≥0, exp (-(x : ℝ)) ∂ρ := integral_exp_pos hint
  have hmass_le : ∫ x : ℝ≥0, exp (-(x : ℝ)) ∂ρ ≤ 1 := by
    calc
      _ ≤ ∫ _ : ℝ≥0, (1 : ℝ) ∂ρ := integral_mono_ae hint (integrable_const 1) <|
        ae_of_all _ fun x ↦ exp_le_one_iff.mpr (neg_nonpos.mpr x.coe_nonneg)
      _ = 1 := by simp
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hmass] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le hmass_le⟩
  rw [(quantile_map_cast_mixedPoissonMeasure_eq_zero_iff ρ hu').2 hu.2.le]
  rfl

end MeasureTheory.Measure
