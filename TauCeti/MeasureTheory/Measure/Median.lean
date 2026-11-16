/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import TauCeti.Probability.Quantile

/-!
# Medians of real functions

A **median** of a real function `f` on a finite measure space is a level `m` such that each of
the sublevel set `{f ≤ m}` and the superlevel set `{m ≤ f}` carries at least half of the total
mass. Every almost everywhere measurable `f` has one, integrable or not: the quantile
`MeasureTheory.Measure.quantile` at level `1/2` of the law of `f` under the normalized measure.

Medians serve as the centre of level-set arguments where the mean does not. A truncation of
`(f - m)⁺` vanishes on `{f ≤ m}`, so on a set of at least half the measure, and the same holds for
`(m - f)⁺` on `{m ≤ f}`; inequalities that need a large zero set, such as the weak-type Poincaré
inequality behind the Sobolev–Poincaré inequality, apply to both. Nothing comparable holds for
the mean: `{f ≤ ∫ f}` may have arbitrarily small measure.

## Main declarations

* `TauCeti.exists_measure_univ_le_two_mul_measure_setOf_le_and_ge`: every almost everywhere
  measurable real function on a finite measure space has a median.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}

/-- **Existence of a median.** An almost everywhere measurable real function `f` on a finite
measure space has a median: a level `m` such that both `{f ≤ m}` and `{m ≤ f}` have at least half
of the total measure. One median is the quantile at level `1/2` of the law of `f` under the
normalized measure. -/
theorem exists_measure_univ_le_two_mul_measure_setOf_le_and_ge (hf : AEMeasurable f μ) :
    ∃ m, μ univ ≤ 2 * μ {x | f x ≤ m} ∧ μ univ ≤ 2 * μ {x | m ≤ f x} := by
  rcases eq_or_ne (μ univ) 0 with h0 | h0
  · exact ⟨0, by simp [h0]⟩
  -- The law `ν` of `f` under the normalized measure `μ / μ(univ)`.
  set ν : Measure ℝ := (μ univ)⁻¹ • μ.map f
  have hν : ∀ s, MeasurableSet s → ν s = (μ univ)⁻¹ * μ (f ⁻¹' s) := fun s hs => by
    rw [smul_apply, Measure.map_apply_of_aemeasurable hf hs, smul_eq_mul]
  have : IsProbabilityMeasure ν := ⟨by
    rw [hν univ MeasurableSet.univ, preimage_univ,
      ENNReal.inv_mul_cancel h0 (measure_ne_top μ univ)]⟩
  -- A set of `ν`-mass at least `1/2` pulls back to a set carrying half of the mass of `μ`.
  have hhalf : ∀ s, MeasurableSet s → 2⁻¹ ≤ ν s → μ univ ≤ 2 * μ (f ⁻¹' s) := fun s hs h => by
    rw [hν s hs, ← ENNReal.div_eq_inv_mul,
      ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl (measure_ne_top μ univ))] at h
    calc μ univ = 2 * (2⁻¹ * μ univ) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ ≤ 2 * μ (f ⁻¹' s) := by gcongr
  have h2 : ENNReal.ofReal 2⁻¹ = 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  -- The median is the quantile of `ν` at level `1/2`: the cumulative distribution function
  -- reaches `1/2` there, and the mass strictly to its left is at most `1/2`.
  have hle : 2⁻¹ ≤ ν (Iic (ν.quantile 2⁻¹)) := by
    have h := ν.le_cdf_quantile (t := 2⁻¹) (by norm_num)
    rw [ProbabilityTheory.cdf_eq_real] at h
    exact h2 ▸ (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top ν _)).2 h
  have hge : 2⁻¹ ≤ ν (Ici (ν.quantile 2⁻¹)) := by
    have h : ν (Iio (ν.quantile 2⁻¹)) ≤ 2⁻¹ :=
      h2 ▸ (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top ν _) (by norm_num)).2
        (ν.measureReal_Iio_quantile_le (t := 2⁻¹) (by norm_num))
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, ← ENNReal.one_sub_inv_two]
    exact tsub_le_tsub_left h 1
  exact ⟨ν.quantile 2⁻¹, hhalf _ measurableSet_Iic hle, hhalf _ measurableSet_Ici hge⟩

end TauCeti
