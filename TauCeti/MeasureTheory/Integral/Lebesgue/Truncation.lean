/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Lebesgue integrals of truncations

The truncations `min f M` of a function `f : α → ℝ≥0∞` at finite levels `M` increase to `f`, so by
monotone convergence their Lebesgue integrals tend to that of `f` as `M → ∞`. Neither `f` nor its
integral needs to be finite.

## Main statements

* `TauCeti.tendsto_lintegral_min_atTop`: `∫⁻ x, min (f x) M ∂μ → ∫⁻ x, f x ∂μ` as `M → ∞`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Integrals of truncations.** If `f : α → ℝ≥0∞` is almost everywhere measurable, then the
integrals of its truncations `min f M` tend to the integral of `f` as the finite level `M` tends
to `∞`, whether or not that integral is finite. -/
theorem tendsto_lintegral_min_atTop {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    Tendsto (fun M : ℝ≥0 ↦ ∫⁻ x, min (f x) M ∂μ) atTop (𝓝 (∫⁻ x, f x ∂μ)) := by
  -- Monotone convergence along integer levels; the integral at level `M` lies between the
  -- integral at level `⌊M⌋₊` and the integral of `f`.
  have hnat : Tendsto (fun n : ℕ ↦ ∫⁻ x, min (f x) n ∂μ) atTop (𝓝 (∫⁻ x, f x ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun _ ↦ hf.min aemeasurable_const)
      (.of_forall fun _ _ _ hmn ↦ min_le_min_left _ (by exact_mod_cast hmn))
      (.of_forall fun x ↦ ?_)
    simpa using tendsto_const_nhds.min ENNReal.tendsto_nat_nhds_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hnat.comp tendsto_nat_floor_atTop)
    tendsto_const_nhds (fun M ↦ lintegral_mono fun _ ↦ min_le_min_left _ ?_)
    fun _ ↦ lintegral_mono fun _ ↦ min_le_left _ _
  simpa using ENNReal.coe_le_coe.2 (Nat.floor_le (a := M) zero_le)

end TauCeti
