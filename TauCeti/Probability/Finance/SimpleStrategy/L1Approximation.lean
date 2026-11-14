/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Approximation of integrable predictable holdings

For a finite predictable measure with no initial-time mass, every integrable real process
admits L¹ approximation by bounded holdings on finite deterministic grids. Each height is
measurable at the left endpoint. No square integrability of the original process is needed.
This applies to expected absolute-variation measures for finite-variation trading gains.
The ambient form accepts a finite measure on the product sigma-algebra and a strongly
predictable process, and transfers the predictable statement through `Measure.trim`.

The construction uses Mathlib's simple-function approximation, then the finite-grid L²
approximation in `TauCeti.Probability.Finance.SimpleStrategy.Approximation`. Simple functions
are square integrable under a finite measure, and the finite-measure L²-to-L¹ comparison
`TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm` controls the second
approximation. The grids need not be nested.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2 (elementary predictable processes).
-/

public section

noncomputable section

open MeasureTheory Set Filter TauCeti.Finance
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Filtration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ)

/-- Every integrable process for a finite predictable measure without initial-time mass
is an L¹ limit of bounded finite-grid holdings with left-measurable heights. The grids start
at zero and may vary arbitrarily with the approximation index. -/
theorem exists_seq_simpleHolding_tendsto_eLpNorm_one
    (μ : @Measure (ℝ≥0 × Ω) ℱ.predictable) [IsFiniteMeasure μ]
    (hzero : μ ({0} ×ˢ (univ : Set Ω)) = 0)
    {H : ℝ≥0 → Ω → ℝ} (hH : Integrable (Function.uncurry H) μ) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, τ k 0 = 0) ∧ (∀ k, StrictMonoOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      Tendsto (fun k ↦ eLpNorm
        (fun p ↦ simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) 1 μ)
        atTop (𝓝 0) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hs (k : ℕ) := (memLp_one_iff_integrable.mpr hH).exists_simpleFunc_eLpNorm_sub_lt
    ENNReal.one_ne_top (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top k))
  choose g hg _ using hs
  have helem (k : ℕ) := ℱ.exists_simpleHolding_eLpNorm_sub_lt μ
    (fun _ _ _ _ ↦ measure_ne_top _ _) hzero
    (H := fun t ω ↦ g k (t, ω)) ((g k).memLp_of_isFiniteMeasure 2 μ)
    (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top k))
  choose n τ a C hτ₀ hτ ha hb herr using helem
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hb, ?_⟩
  have hfirst := TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm one_le_two
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ zero_le) fun k ↦ (herr k).le)
  have hsecond : Tendsto (fun k ↦ eLpNorm (fun p ↦ g k p - H p.1 p.2) 1 μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ zero_le) fun k ↦ by
        have h := hg k
        rw [eLpNorm_sub_comm] at h
        exact h.le
  have hsum := hfirst.add hsecond
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) fun k ↦ ?_
  calc
    _ = eLpNorm ((fun p ↦ simpleHolding (τ k) (n k) (a k) p.1 p.2 - g k p) +
        (fun p ↦ g k p - H p.1 p.2)) 1 μ := by congr 1; ext p; simp
    _ ≤ _ := eLpNorm_add_le le_rfl

/-- Ambient form of `exists_seq_simpleHolding_tendsto_eLpNorm_one`: for a finite measure on
the product sigma-algebra without initial-time mass, every integrable strongly predictable
process is an L¹ limit of bounded finite-grid holdings with left-measurable heights. -/
theorem exists_seq_simpleHolding_tendsto_eLpNorm_one_of_isStronglyPredictable
    (ν : Measure (ℝ≥0 × Ω)) [IsFiniteMeasure ν] (hzero : ν ({0} ×ˢ (univ : Set Ω)) = 0)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyPredictable ℱ H)
    (hint : Integrable (Function.uncurry H) ν) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, τ k 0 = 0) ∧ (∀ k, StrictMonoOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      Tendsto (fun k ↦ eLpNorm
        (fun p ↦ simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) 1 ν)
        atTop (𝓝 0) := by
  have hset : MeasurableSet[ℱ.predictable] ({0} ×ˢ (univ : Set Ω)) := by
    simpa only [NNReal.bot_eq_zero] using
      measurableSet_predictable_singleton_bot_prod (𝓕 := ℱ) MeasurableSet.univ
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, hb, hlim⟩ :=
    ℱ.exists_seq_simpleHolding_tendsto_eLpNorm_one (ν.trim ℱ.predictable_le_prod)
      ((trim_measurableSet_eq _ hset).trans hzero) (hint.trim ℱ.predictable_le_prod hH)
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hb, hlim.congr fun k ↦ ?_⟩
  exact eLpNorm_trim ℱ.predictable_le_prod
    ((isStronglyPredictable_simpleHolding (ℱ := ℱ) (ha k)).sub hH)

end MeasureTheory.Filtration
