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

An interior quantile of a real-cast mixed Poisson count is the least natural number whose
cumulative mixed-Poisson mass reaches the requested level. This file states that crossing using
the explicit cumulative mass series, so it can be evaluated directly from the mixing law.

Every mixed Poisson law has positive mass at zero: conditionally on any finite rate `x`, the
zero-count probability is `exp (-x)`. Consequently its lower quantiles are zero on a nonempty
initial interval, and their one-sided limit at probability level zero is zero.

## References

* J. Grandell, *Mixed Poisson Processes*, Chapman & Hall (1997), ch. 2.
* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley
  (2005), §8.3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open TauCeti.Probability
open scoped NNReal

namespace MeasureTheory.Measure

variable {u : ℝ}

/-- A natural number is a mixed Poisson lower quantile exactly when it is the least index whose
explicit cumulative mixed-Poisson mass reaches the interior probability level. -/
theorem quantile_map_cast_mixedPoissonMeasure_eq_iff (ρ : Measure ℝ≥0)
    [IsProbabilityMeasure ρ] (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((mixedPoissonMeasure ρ).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {n : ℕ | u ≤ ∑ j ∈ Finset.range (n + 1),
        ∫ x, exp (-(x : ℝ)) * (x : ℝ) ^ j / Nat.factorial j ∂ρ} k := by
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  simp_rw [mixedPoissonMeasure_real_Iic]

/-- The initial constant segment of a mixed Poisson quantile ends at the mixed probability of a
zero count, `∫ x, exp (-x) ∂ρ`. -/
@[simp]
theorem quantile_map_cast_mixedPoissonMeasure_eq_zero_iff (ρ : Measure ℝ≥0)
    [IsProbabilityMeasure ρ] (hu : u ∈ Ioo 0 1) :
    ((mixedPoissonMeasure ρ).map (Nat.cast : ℕ → ℝ)).quantile u = 0 ↔
      u ≤ ∫ x, exp (-(x : ℝ)) ∂ρ := by
  simpa [IsLeast, lowerBounds] using quantile_map_cast_mixedPoissonMeasure_eq_iff ρ hu 0

/-- Mixed Poisson quantiles tend to the lower support endpoint zero as the probability level
tends to zero from above. -/
theorem tendsto_quantile_map_cast_mixedPoissonMeasure_nhdsGT_zero (ρ : Measure ℝ≥0)
    [IsProbabilityMeasure ρ] :
    Tendsto
      (fun u ↦ (((mixedPoissonMeasure ρ).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  have hmass : 0 < (mixedPoissonMeasure ρ).real {0} :=
    mixedPoissonMeasure_real_singleton_zero_pos ρ
  have hmass_le : (mixedPoissonMeasure ρ).real {0} ≤ 1 :=
    (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hmass] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le hmass_le⟩
  have hzero : ((mixedPoissonMeasure ρ).map (Nat.cast : ℕ → ℝ)).quantile u = 0 := by
    rw [quantile_map_cast_mixedPoissonMeasure_eq_zero_iff ρ hu']
    have hmass_eq : (mixedPoissonMeasure ρ).real {0} =
        ∫ x, exp (-(x : ℝ)) ∂ρ := by
      simpa using mixedPoissonMeasure_real_singleton ρ 0
    exact hu.2.le.trans_eq hmass_eq
  exact congrArg (fun x : ℝ ↦ (x : EReal)) hzero.symm

end MeasureTheory.Measure
