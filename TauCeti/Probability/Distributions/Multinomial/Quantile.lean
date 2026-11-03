/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Binomial.Quantile
public import TauCeti.Probability.Distributions.Multinomial.Marginal

/-!
# Quantiles of multinomial coordinates

A coordinate of a multinomial count vector has a binomial law. Consequently, after casting the
coordinate to the reals, its interior quantiles and one-sided endpoint limits are the corresponding
binomial quantities. This includes zero trials and the deterministic cell-probability boundaries.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

noncomputable section

open Convexity Filter MeasureTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

private theorem map_cast_eval_multinomialMeasure (n : ℕ) (p : StdSimplex NNReal ι)
    (i : ι) :
    (multinomialMeasure n p).map (fun k ↦ (k i : ℝ)) =
      ((multinomialMeasure n p).map (fun k ↦ k i)).map (Nat.cast : ℕ → ℝ) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The real-cast quantile of a multinomial coordinate is the quantile of its binomial
marginal. -/
theorem quantile_map_cast_eval_multinomialMeasure (n : ℕ) (p : StdSimplex NNReal ι)
    (i : ι) (u : ℝ) :
    ((multinomialMeasure n p).map (fun k ↦ (k i : ℝ))).quantile u =
      ((ProbabilityTheory.binomial n (p.multinomialCellProbability i)).map
        (Nat.cast : ℕ → ℝ)).quantile u := by
  rw [map_cast_eval_multinomialMeasure, map_eval_multinomialMeasure]

/-- At level zero, a multinomial coordinate quantile tends to the trial count when all mass is
in that cell, and to zero otherwise. -/
theorem tendsto_quantile_map_cast_eval_multinomialMeasure_nhdsGT_zero
    (n : ℕ) (p : StdSimplex NNReal ι) (i : ι) :
    Tendsto (fun u ↦
      (((multinomialMeasure n p).map (fun k ↦ (k i : ℝ))).quantile u : EReal))
      (𝓝[>] 0)
      (𝓝 (if p.multinomialCellProbability i = 1 then (n : EReal) else 0)) := by
  rw [map_cast_eval_multinomialMeasure, map_eval_multinomialMeasure]
  exact tendsto_quantile_map_cast_binomial_nhdsGT_zero n (p.multinomialCellProbability i)

/-- At level one, a multinomial coordinate quantile tends to zero when its cell has zero mass,
and to the trial count otherwise. -/
theorem tendsto_quantile_map_cast_eval_multinomialMeasure_nhdsLT_one
    (n : ℕ) (p : StdSimplex NNReal ι) (i : ι) :
    Tendsto (fun u ↦
      (((multinomialMeasure n p).map (fun k ↦ (k i : ℝ))).quantile u : EReal))
      (𝓝[<] 1)
      (𝓝 (if p.multinomialCellProbability i = 0 then 0 else (n : EReal))) := by
  rw [map_cast_eval_multinomialMeasure, map_eval_multinomialMeasure]
  exact tendsto_quantile_map_cast_binomial_nhdsLT_one n (p.multinomialCellProbability i)

end TauCeti.Probability
