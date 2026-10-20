/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.Cdf
public import TauCeti.Probability.Quantile.Discrete

/-!
# Quantiles of compound Poisson laws

For real jumps the lower quantile is characterized by the Poisson-weighted cdf series, with
the empty-sum atom displayed separately. For natural or integer jumps it is the least native
integer whose cumulative series reaches the requested level. These adjunctions allow atoms,
gaps in the support, and singular jump laws, without asserting a unique cdf root.

For natural jumps, every interior level at most `exp (-r)` has quantile zero. At zero rate,
all the laws reduce to the point mass at zero.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. I, ch. XII, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal Nat

namespace TauCeti.Probability

/-- The real compound Poisson quantile adjunction in terms of the explicit cdf series. The
empty-sum atom is retained, so this does not require continuity of the cdf. -/
theorem quantile_compoundPoissonMeasure_le_iff (r : ℝ≥0) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {u : ℝ} (hu : u ∈ Ioo 0 1) (x : ℝ) :
    (compoundPoissonMeasure r μ).quantile u ≤ x ↔
      u ≤ (if 0 ≤ x then exp (-(r : ℝ)) else 0) +
        ∑' n : ℕ, (exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1) !) *
          cdf (μ.convolutionPower (n + 1)) x := by
  rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_compoundPoissonMeasure]

/-- A natural number is the compound Poisson quantile exactly when it is the least crossing
of the Poisson-weighted native cumulative series. -/
theorem quantile_map_natCast_compoundPoissonMeasure_eq_iff (r : ℝ≥0) (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {u : ℝ} (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((compoundPoissonMeasure r μ).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {j : ℕ | u ≤ ∑' n : ℕ,
        (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) *
          (μ.convolutionPower n).real (Iic j)} k := by
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  simp_rw [(hasSum_compoundPoissonMeasure_real_apply r μ measurableSet_Iic).tsum_eq]

/-- An integer is the compound Poisson quantile exactly when it is the least crossing of the
native cumulative series, including laws with negative jumps. -/
theorem quantile_map_intCast_compoundPoissonMeasure_eq_iff (r : ℝ≥0) (μ : Measure ℤ)
    [IsProbabilityMeasure μ] {u : ℝ} (hu : u ∈ Ioo 0 1) (k : ℤ) :
    ((compoundPoissonMeasure r μ).map (Int.cast : ℤ → ℝ)).quantile u = k ↔
      IsLeast {j : ℤ | u ≤ ∑' n : ℕ,
        (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) *
          (μ.convolutionPower n).real (Iic j)} k := by
  rw [Measure.quantile_map_intCast_eq_iff _ hu]
  simp_rw [(hasSum_compoundPoissonMeasure_real_apply r μ measurableSet_Iic).tsum_eq]

/-- For natural jumps, the no-jump probability gives an initial segment on which the lower
quantile is zero. Additional zero jumps can extend this segment. -/
@[simp]
theorem quantile_map_natCast_compoundPoissonMeasure_eq_zero (r : ℝ≥0) (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {u : ℝ} (hu : u ∈ Ioo 0 1) (hur : u ≤ exp (-(r : ℝ))) :
    ((compoundPoissonMeasure r μ).map (Nat.cast : ℕ → ℝ)).quantile u = 0 := by
  apply le_antisymm _ (Measure.quantile_map_natCast_nonneg _ hu)
  rw [Measure.quantile_le_iff _ hu.1 hu.2,
    Measure.cdf_map_natCast _ le_rfl, Nat.floor_zero]
  exact hur.trans ((exp_neg_le_compoundPoissonMeasure_real_singleton_zero r μ).trans
    (measureReal_mono (singleton_subset_iff.mpr (mem_Iic.mpr le_rfl))))

end TauCeti.Probability
