/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.SimpleFunc.DyadicSquare
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.TimeMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

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

More generally, `eLpNorm_simpleHolding_sub_le` bounds the Lᵖ error by the sum of
height errors weighted by time-cell masses. Thus `tendsto_eLpNorm_simpleHolding_sub_of_tendsto`
transports height convergence along any filter, for `1 ≤ p`, to any fixed finite grid
of measurable finite-mass cells in an s-finite time measure.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2 (elementary predictable integrands).
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace TauCeti.Finance

/-- The Lᵖ error on a fixed grid is bounded by the sum of the height errors weighted
by the time-cell masses. Neither the grid nor the heights need be measurable globally;
only the finitely many time cells must be measurable. -/
theorem eLpNorm_simpleHolding_sub_le
    {ι Ω : Type*} [LinearOrder ι] [MeasurableSpace ι] [MeasurableSpace Ω]
    {ν : Measure ι} [SFinite ν] {P : Measure Ω} [SFinite P]
    (τ : ℕ → ι) (n : ℕ) (a b : ℕ → Ω → ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hI : ∀ j < n, MeasurableSet (Ioc (τ j) (τ (j + 1)))) :
    eLpNorm (fun q : ι × Ω ↦ simpleHolding τ n a q.1 q.2 -
      simpleHolding τ n b q.1 q.2) p (ν.prod P) ≤
      ∑ j ∈ Finset.range n, ν (Ioc (τ j) (τ (j + 1))) ^ (1 / p).toReal *
        eLpNorm (a j - b j) p P := by
  have heq : (fun q : ι × Ω ↦ simpleHolding τ n a q.1 q.2 -
      simpleHolding τ n b q.1 q.2) =
      ∑ j ∈ Finset.range n, (Prod.fst ⁻¹' Ioc (τ j) (τ (j + 1))).indicator
        ((a j - b j) ∘ Prod.snd) := by
    funext q
    simp only [simpleHolding_def, ← Finset.sum_sub_distrib, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Set.indicator, mem_preimage, Function.comp_apply, Pi.sub_apply]
    split_ifs <;> simp
  rw [heq]
  refine (eLpNorm_sum_le hp).trans (Finset.sum_le_sum fun j hj ↦ ?_)
  have hIj := hI j (Finset.mem_range.mp hj)
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (hIj.preimage measurable_fst).nullMeasurableSet]
  have hset : Prod.fst ⁻¹' Ioc (τ j) (τ (j + 1)) =
      Ioc (τ j) (τ (j + 1)) ×ˢ (univ : Set Ω) := by ext q; simp
  rw [hset, ← Measure.restrict_prod_eq_prod_univ]
  exact eLpNorm_comp_le_of_map_le_smul measurable_snd.aemeasurable
    (by simp [Measure.map_snd_prod]) p

/-- On a fixed finite grid of finite-mass measurable cells, convergence of every height
in Lᵖ implies convergence of the holding in time-product Lᵖ, along any filter. -/
theorem tendsto_eLpNorm_simpleHolding_sub_of_tendsto
    {ι Ω κ : Type*} [LinearOrder ι] [MeasurableSpace ι] [MeasurableSpace Ω]
    {ν : Measure ι} [SFinite ν] {P : Measure Ω} [SFinite P]
    (τ : ℕ → ι) (n : ℕ) {a : κ → ℕ → Ω → ℝ} {b : ℕ → Ω → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {l : Filter κ}
    (hI : ∀ j < n, MeasurableSet (Ioc (τ j) (τ (j + 1))))
    (hfin : ∀ j < n, ν (Ioc (τ j) (τ (j + 1))) ≠ ∞)
    (ha : ∀ j < n, Tendsto (fun k ↦ eLpNorm (a k j - b j) p P) l (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (fun q : ι × Ω ↦ simpleHolding τ n (a k) q.1 q.2 -
      simpleHolding τ n b q.1 q.2) p (ν.prod P)) l (𝓝 0) := by
  have hlim : Tendsto (fun k ↦ ∑ j ∈ Finset.range n,
      ν (Ioc (τ j) (τ (j + 1))) ^ (1 / p).toReal * eLpNorm (a k j - b j) p P)
      l (𝓝 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum (Finset.range n) (fun j hj ↦
        ENNReal.Tendsto.const_mul (ha j (Finset.mem_range.mp hj))
          (Or.inr (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
            (hfin j (Finset.mem_range.mp hj)))))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) (fun k ↦ eLpNorm_simpleHolding_sub_le τ n (a k) b hp hI)

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
  refine tendsto_eLpNorm_simpleHolding_sub_of_tendsto τ n (by norm_num)
    (fun _ _ ↦ measurableSet_Ioc) (fun _ _ ↦ measure_ne_top _ _) ?_
  intro j hj
  let : ENNReal.HolderTriple 4 4 2 := .of_toReal (by norm_num [Real.holderTriple_iff])
  have hsq : MemLp (fun ω ↦ a j ω ^ 2) 2 P := by
    simpa only [pow_two, Pi.mul_def] using (ha j hj).mul (ha j hj)
  exact hsq.tendsto_eLpNorm_dyadicSquareApprox_sub_sq (by norm_num)

end TauCeti.Finance
