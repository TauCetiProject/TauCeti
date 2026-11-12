/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.SimpleFunc.DyadicSquare
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.TimeMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Simple-value approximation on a fixed trading grid

Squaring an L⁴ holding gives an L² height, but not a bounded simple height.
For measurable heights, composition with `dyadicSquareApprox` supplies explicit bounded
simple heights on the same grid, using native `SimpleFunc.comp`. Left-measurable heights
give predictable holdings through `isStronglyPredictable_simpleHolding`. The holding
processes converge in finite-horizon time-product L²; convergence itself only needs L⁴
heights. In particular this applies to squared Brownian values at the left endpoints.
This value approximation is independent of time-mesh approximation and needs no
regularity of paths or Brownian noise.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2 (elementary predictable integrands).
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace TauCeti.Finance

/-- On any fixed finite grid, bounded dyadic simple-value approximations of L⁴ heights
converge to the squared-height holding in time-product L². The grid need not be monotone:
the statement remains valid for overlapping cells, repeated dates and empty grids. -/
theorem tendsto_eLpNorm_simpleHolding_dyadicSquareApprox_sub_sq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (τ : ℕ → ℝ≥0) (n : ℕ) {a : ℕ → Ω → ℝ}
    (ha : ∀ j < n, MemLp (a j) 4 P) (T : ℝ≥0) :
    Tendsto (fun k ↦ eLpNorm (fun p : ℝ≥0 × Ω ↦
      simpleHolding τ n (fun j ω ↦ dyadicSquareApprox k (a j ω)) p.1 p.2 -
        simpleHolding τ n (fun j ω ↦ a j ω ^ 2) p.1 p.2) 2
          ((Probability.timeMeasure T).prod P)) atTop (𝓝 0) := by
  let μ := (Probability.timeMeasure T).prod P
  let e (k j : ℕ) (p : ℝ≥0 × Ω) := dyadicSquareApprox k (a j p.2) - a j p.2 ^ 2
  have heq (k : ℕ) : (fun p : ℝ≥0 × Ω ↦
      simpleHolding τ n (fun j ω ↦ dyadicSquareApprox k (a j ω)) p.1 p.2 -
        simpleHolding τ n (fun j ω ↦ a j ω ^ 2) p.1 p.2) =
      ∑ j ∈ Finset.range n, {p : ℝ≥0 × Ω | p.1 ∈ Ioc (τ j) (τ (j + 1))}.indicator
        (e k j) := by
    funext p
    simp only [simpleHolding_def, ← Finset.sum_sub_distrib, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Set.indicator, mem_ofPred_eq, e]
    split_ifs <;> simp
  have hle (k : ℕ) : eLpNorm (fun p : ℝ≥0 × Ω ↦
      simpleHolding τ n (fun j ω ↦ dyadicSquareApprox k (a j ω)) p.1 p.2 -
        simpleHolding τ n (fun j ω ↦ a j ω ^ 2) p.1 p.2) 2 μ ≤
      ∑ j ∈ Finset.range n, eLpNorm (e k j) 2 μ := by
    rw [heq]
    exact (eLpNorm_sum_le (by norm_num)).trans (Finset.sum_le_sum fun j _ ↦
      eLpNorm_indicator_le _ (measurableSet_Ioc.preimage measurable_fst).nullMeasurableSet)
  have hlim : Tendsto (fun k ↦ ∑ j ∈ Finset.range n, eLpNorm (e k j) 2 μ)
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Finset.range n)
      (fun j hj ↦ ((ha j (Finset.mem_range.mp hj)).comp_snd
        (Probability.timeMeasure T)).tendsto_eLpNorm_dyadicSquareApprox_sub_sq)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) hle

end TauCeti.Finance
