/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Radon–Nikodym derivatives in Lᵖ

If `ν ≤ μ` and `μ` is finite, the density of `ν` with respect to `μ` times any fixed vector
belongs to every `Lᵖ(μ)`. In particular, it can be paired with an `L²` function to integrate
against `ν`.
-/

public section

namespace MeasureTheory.Measure

/-- If `ν ≤ μ` with `μ` finite, the real Radon–Nikodym derivative of `ν` with respect to `μ`
times any fixed vector belongs to `Lᵖ(μ)`. -/
theorem memLp_toReal_rnDeriv_smul_const {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Measure X) {μ : Measure X}
    [IsFiniteMeasure μ] (hν : ν ≤ μ) (p : ENNReal) (c : E) :
    MemLp (fun x ↦ (ν.rnDeriv μ x).toReal • c) p μ := by
  have hm := ((ν.measurable_rnDeriv μ).ennreal_toReal.stronglyMeasurable.smul_const c)
  refine MemLp.of_bound hm.aestronglyMeasurable ‖c‖ ?_
  filter_upwards [rnDeriv_le_one_of_le hν] with x hx
  rw [norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using ENNReal.toReal_mono (by simp) hx)

end MeasureTheory.Measure
