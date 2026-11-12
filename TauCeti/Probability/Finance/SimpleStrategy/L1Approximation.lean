/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Approximation

/-!
# Approximation of integrable predictable holdings

For a finite predictable measure with no initial-time mass, every integrable real process
admits L¹ approximation by bounded holdings on finite deterministic grids. Each height is
measurable at the left endpoint. No square integrability of the original process is needed.
This applies to expected absolute-variation measures for finite-variation trading gains.

The construction uses Mathlib's simple-function approximation, then the finite-grid L²
approximation in `TauCeti.Probability.Finance.SimpleStrategy.Approximation`. Simple functions
are square integrable under a finite measure, and the finite-measure L²-to-L¹ inequality
controls the second approximation. The grids need not be nested.

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
  let D : ℝ≥0∞ := μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hD : D ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ)
  have hbound (k : ℕ) : eLpNorm
      (fun p ↦ simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) 1 μ ≤
        (k : ℝ≥0∞)⁻¹ * D + (k : ℝ≥0∞)⁻¹ := by
    have hmeas := (isStronglyPredictable_simpleHolding (ℱ := ℱ) (ha k)).sub
      (g k).stronglyMeasurable
    have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (by norm_num :
      (1 : ℝ≥0∞) ≤ 2) hmeas.aestronglyMeasurable
    have hfirst : eLpNorm
        (fun p ↦ simpleHolding (τ k) (n k) (a k) p.1 p.2 - g k p) 1 μ ≤
          (k : ℝ≥0∞)⁻¹ * D :=
      hcompare.trans (by gcongr; exact (herr k).le)
    have hsecond : eLpNorm (fun p ↦ g k p - H p.1 p.2) 1 μ < (k : ℝ≥0∞)⁻¹ := by
      have h := hg k
      rw [eLpNorm_sub_comm] at h
      exact h
    calc
      _ = eLpNorm ((fun p ↦ simpleHolding (τ k) (n k) (a k) p.1 p.2 - g k p) +
          (fun p ↦ g k p - H p.1 p.2)) 1 μ := by congr 1; ext p; simp
      _ ≤ _ := eLpNorm_add_le le_rfl
      _ ≤ _ := add_le_add hfirst hsecond.le
  have hlim := (ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero
    (Or.inr hD)).add ENNReal.tendsto_inv_nat_nhds_zero
  simp only [zero_mul, zero_add] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) hbound

end MeasureTheory.Filtration
