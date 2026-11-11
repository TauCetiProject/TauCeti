/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.Probability.Distributions.Binomial.Quantile
public import TauCeti.Probability.Distributions.Multinomial.Marginal

/-!
# Quantiles of multinomial coordinates

A coordinate of a multinomial count vector has a binomial law. Consequently, after casting the
coordinate to the reals, its interior quantiles and one-sided endpoint limits are the corresponding
binomial quantities. This includes zero trials and the deterministic cell-probability boundaries.
The interior quantile is also characterized as the least crossing of the binomial cumulative mass.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

noncomputable section

open Convexity Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The real-cast quantile of a multinomial coordinate is the quantile of its binomial
marginal. -/
theorem quantile_map_cast_eval_multinomialMeasure (n : ℕ) (p : StdSimplex NNReal ι)
    (i : ι) (u : ℝ) :
    ((multinomialMeasure n p).map (fun k ↦ (k i : ℝ))).quantile u =
      ((ProbabilityTheory.binomial n (p.multinomialCellProbability i)).map
        (Nat.cast : ℕ → ℝ)).quantile u := by
  -- Expose the cast as a composition for the reverse `Measure.map_map` rewrite.
  rw [show (fun k : ι → ℕ ↦ (k i : ℝ)) =
      (Nat.cast : ℕ → ℝ) ∘ fun k ↦ k i by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    map_eval_multinomialMeasure]

/-- A natural number is the lower quantile of a multinomial coordinate exactly when it is the
least count whose binomial cumulative mass reaches the level. -/
theorem quantile_map_cast_eval_multinomialMeasure_eq_iff (n : ℕ)
    (p : StdSimplex NNReal ι) (i : ι) {u : ℝ} (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((multinomialMeasure n p).map (fun x ↦ (x i : ℝ))).quantile u = k ↔
      IsLeast
        {j : ℕ | u ≤ if n ≤ j then 1 else
          regularizedIncompleteBeta ((n : ℝ) - j) ((j : ℝ) + 1) (1 - (p.weights i : ℝ))}
        k := by
  rw [quantile_map_cast_eval_multinomialMeasure,
    quantile_map_cast_binomial_eq_iff hu, StdSimplex.coe_multinomialCellProbability]

/-- At level zero, a multinomial coordinate quantile tends to the trial count when all mass is
in that cell, and to zero otherwise. -/
theorem tendsto_quantile_map_cast_eval_multinomialMeasure_nhdsGT_zero
    (n : ℕ) (p : StdSimplex NNReal ι) (i : ι) :
    Tendsto (fun u ↦
      (((multinomialMeasure n p).map (fun k ↦ (k i : ℝ))).quantile u : EReal))
      (𝓝[>] 0)
      (𝓝 (if p.multinomialCellProbability i = 1 then (n : EReal) else 0)) := by
  -- Expose the cast as a composition for the reverse `Measure.map_map` rewrite.
  rw [show (fun k : ι → ℕ ↦ (k i : ℝ)) =
      (Nat.cast : ℕ → ℝ) ∘ fun k ↦ k i by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    map_eval_multinomialMeasure]
  exact tendsto_quantile_map_cast_binomial_nhdsGT_zero n (p.multinomialCellProbability i)

/-- At level one, a multinomial coordinate quantile tends to zero when its cell has zero mass,
and to the trial count otherwise. -/
theorem tendsto_quantile_map_cast_eval_multinomialMeasure_nhdsLT_one
    (n : ℕ) (p : StdSimplex NNReal ι) (i : ι) :
    Tendsto (fun u ↦
      (((multinomialMeasure n p).map (fun k ↦ (k i : ℝ))).quantile u : EReal))
      (𝓝[<] 1)
      (𝓝 (if p.multinomialCellProbability i = 0 then 0 else (n : EReal))) := by
  -- Expose the cast as a composition for the reverse `Measure.map_map` rewrite.
  rw [show (fun k : ι → ℕ ↦ (k i : ℝ)) =
      (Nat.cast : ℕ → ℝ) ∘ fun k ↦ k i by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    map_eval_multinomialMeasure]
  exact tendsto_quantile_map_cast_binomial_nhdsLT_one n (p.multinomialCellProbability i)

end TauCeti.Probability
