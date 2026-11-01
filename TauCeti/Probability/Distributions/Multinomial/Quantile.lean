/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.Binomial.Quantile
public import TauCeti.Probability.Distributions.Multinomial.Marginal

/-!
# Coordinate quantiles of multinomial laws

The count in cell `i` of a multinomial vector with `n` trials and cell weights `p` is binomial
with `n` trials and success probability `p i`. Its real lower quantile at an interior level is
therefore the least count at which the binomial cumulative mass, written as a regularized
incomplete Beta function, reaches the level.

The one-sided endpoint limits are those of the binomial law. Near level zero the quantile tends
to `n` when the cell has weight one and to zero otherwise; near level one it tends to zero when
the cell has weight zero and to `n` otherwise.

## Main results

* `TauCeti.Probability.quantile_map_cast_eval_multinomialMeasure_eq_iff`: the coordinate quantile
  is the least crossing of the incomplete-Beta cumulative mass.
* `TauCeti.Probability.tendsto_quantile_map_cast_eval_multinomialMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_map_cast_eval_multinomialMeasure_nhdsLT_one`: the
  endpoint limits.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997,
  Chapter 35.
-/

public section

noncomputable section

open Convexity Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {n : ℕ} {p : StdSimplex NNReal ι} {u : ℝ}

/-- The real cast of a multinomial cell count is the real cast of its binomial marginal. -/
private theorem map_cast_eval_multinomialMeasure (n : ℕ) (p : StdSimplex NNReal ι) (i : ι) :
    (multinomialMeasure n p).map (fun k ↦ (k i : ℝ)) =
      Bin(ℝ, n, p.multinomialCellProbability i) := by
  rw [← map_eval_multinomialMeasure,
    Measure.map_map measurable_from_nat (measurable_pi_apply i), Function.comp_def]

/-- A natural number is the lower quantile of the count in cell `i` of a multinomial law exactly
when it is the least count whose cumulative binomial mass, the regularized incomplete Beta
function at `1 - p i`, reaches the level. At and beyond `n` the cumulative mass is one. -/
theorem quantile_map_cast_eval_multinomialMeasure_eq_iff (i : ι) (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((multinomialMeasure n p).map (fun x ↦ (x i : ℝ))).quantile u = k ↔
      IsLeast
        {j : ℕ | u ≤ if n ≤ j then 1 else
          regularizedIncompleteBeta ((n : ℝ) - j) ((j : ℝ) + 1) (1 - (p.weights i : ℝ))}
        k := by
  rw [map_cast_eval_multinomialMeasure, quantile_map_cast_binomial_eq_iff hu,
    StdSimplex.coe_multinomialCellProbability]

/-- As the level tends to zero from above, the quantiles of a multinomial cell count tend to the
lower endpoint of its support: `n` for a cell of weight one, zero otherwise. -/
theorem tendsto_quantile_map_cast_eval_multinomialMeasure_nhdsGT_zero (n : ℕ)
    (p : StdSimplex NNReal ι) (i : ι) :
    Tendsto (fun u ↦ (((multinomialMeasure n p).map (fun x ↦ (x i : ℝ))).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (if p.weights i = 1 then (n : EReal) else 0)) := by
  simpa only [map_cast_eval_multinomialMeasure,
    StdSimplex.multinomialCellProbability_eq_one_iff] using
    tendsto_quantile_map_cast_binomial_nhdsGT_zero n (p.multinomialCellProbability i)

/-- As the level tends to one from below, the quantiles of a multinomial cell count tend to the
upper endpoint of its support: zero for a cell of weight zero, `n` otherwise. -/
theorem tendsto_quantile_map_cast_eval_multinomialMeasure_nhdsLT_one (n : ℕ)
    (p : StdSimplex NNReal ι) (i : ι) :
    Tendsto (fun u ↦ (((multinomialMeasure n p).map (fun x ↦ (x i : ℝ))).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if p.weights i = 0 then 0 else (n : EReal))) := by
  simpa only [map_cast_eval_multinomialMeasure,
    StdSimplex.multinomialCellProbability_eq_zero_iff] using
    tendsto_quantile_map_cast_binomial_nhdsLT_one n (p.multinomialCellProbability i)

end TauCeti.Probability
