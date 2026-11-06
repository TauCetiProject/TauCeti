/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Lebesgue integrals of truncations

The truncations `min f M` of a function `f : α → ℝ≥0∞` at finite levels `M` increase to `f`, so by
monotone convergence their Lebesgue integrals tend to that of `f` as `M → ∞`. Neither `f` nor its
integral needs to be finite.

## Main statements

* `TauCeti.tendsto_lintegral_min_atTop`: `∫⁻ x, min (f x) M ∂μ → ∫⁻ x, f x ∂μ` as `M → ∞`.
* `TauCeti.lintegral_enorm_rpow_eq_setLIntegral`: the `q`-th power integral of a truncation to a
  measurable set is the truncated integral.
* `TauCeti.setLIntegral_enorm_rpow_lt_congr`, `TauCeti.setLIntegral_enorm_rpow_le_congr`:
  truncated integrals of `‖v‖ₑ ^ q` do not change when the truncating function is replaced by an
  almost everywhere equal one.
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

/-- The `q`-th power integral of a truncation of `f` is a truncated integral of `‖f‖ ^ q`. -/
theorem lintegral_enorm_rpow_eq_setLIntegral {E : Type*} [TopologicalSpace E]
    [ESeminormedAddMonoid E] {q : ℝ} {f g : α → E} {R : Set α} (hR : MeasurableSet R)
    (hg : g =ᵐ[μ] R.indicator f) (hq : 0 < q) :
    ∫⁻ x, ‖g x‖ₑ ^ q ∂μ = ∫⁻ x in R, ‖f x‖ₑ ^ q ∂μ := by
  rw [← lintegral_indicator hR]
  refine lintegral_congr_ae ?_
  filter_upwards [hg] with x hx
  by_cases hxR : x ∈ R <;> simp [hx, hxR, ENNReal.zero_rpow_of_pos hq]

/-- Truncating `v` at a height does not change, up to a null set, the integral over the part
where `‖v‖` is above that height, when `v` is replaced by an almost everywhere equal function. -/
theorem setLIntegral_enorm_rpow_lt_congr {G : Type*} [TopologicalSpace G]
    [ESeminormedAddMonoid G] {q : ℝ} {v g : α → G} (hvg : v =ᵐ[μ] g) (a : ℝ≥0∞) :
    ∫⁻ x in {x | a < ‖g x‖ₑ}, ‖v x‖ₑ ^ q ∂μ = ∫⁻ x in {x | a < ‖v x‖ₑ}, ‖v x‖ₑ ^ q ∂μ := by
  have hsets : {x | a < ‖v x‖ₑ} =ᵐ[μ] {x | a < ‖g x‖ₑ} := by
    filter_upwards [hvg] with x hx
    exact congrArg (fun z : ℝ≥0∞ => a < z) (congrArg enorm hx)
  rw [Measure.restrict_congr_set hsets]

/-- The analogue of `setLIntegral_enorm_rpow_lt_congr` for the part where `‖v‖` is at most the
height. -/
theorem setLIntegral_enorm_rpow_le_congr {G : Type*} [TopologicalSpace G]
    [ESeminormedAddMonoid G] {q : ℝ} {v g : α → G} (hvg : v =ᵐ[μ] g) (a : ℝ≥0∞) :
    ∫⁻ x in {x | ‖g x‖ₑ ≤ a}, ‖v x‖ₑ ^ q ∂μ = ∫⁻ x in {x | ‖v x‖ₑ ≤ a}, ‖v x‖ₑ ^ q ∂μ := by
  have hsets : {x | ‖v x‖ₑ ≤ a} =ᵐ[μ] {x | ‖g x‖ₑ ≤ a} := by
    filter_upwards [hvg] with x hx
    exact congrArg (fun z : ℝ≥0∞ => z ≤ a) (congrArg enorm hx)
  rw [Measure.restrict_congr_set hsets]

end TauCeti
