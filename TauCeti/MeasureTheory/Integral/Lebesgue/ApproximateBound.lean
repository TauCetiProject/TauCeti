/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Functions approximately bounded by functions of vanishing integral

Let `f i : α → ℝ≥0∞` have Lebesgue integrals tending to zero along a filter, and let `g` be
bounded by `f i + ε` almost everywhere for eventually all `i`, for each `ε > 0`. On a finite
measure space, `g` then has zero integral: its integral is at most `∫⁻ f i + ε μ(α)` for each `ε`.

This applies to a uniform limit `g` of functions bounded by `f i`, for instance to the norm of a
defect that is the uniform limit of defects controlled in `L¹`.

## Main statements

* `TauCeti.lintegral_eq_zero_of_eventually_le_add`: a function approximately bounded by functions
  whose integrals tend to zero has zero integral.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Approximate bounds by functions of vanishing integral.** On a finite measure space, if
`∫⁻ f i → 0` along a nontrivial filter and, for every `ε > 0`, eventually `g ≤ f i + ε` almost
everywhere, then `∫⁻ g = 0`. -/
theorem lintegral_eq_zero_of_eventually_le_add [IsFiniteMeasure μ] {l : Filter ι} [l.NeBot]
    {g : α → ℝ≥0∞} {f : ι → α → ℝ≥0∞} (hf : Tendsto (fun i ↦ ∫⁻ x, f i x ∂μ) l (𝓝 0))
    (h : ∀ ε : ℝ≥0, 0 < ε → ∀ᶠ i in l, ∀ᵐ x ∂μ, g x ≤ f i x + ε) :
    ∫⁻ x, g x ∂μ = 0 := by
  -- For each `ε > 0` the integral of `g` is at most `ε μ(α)`.
  have hle (ε : ℝ≥0) (hε : 0 < ε) : ∫⁻ x, g x ∂μ ≤ ε * μ univ := by
    have hlim : Tendsto (fun i ↦ ∫⁻ x, f i x ∂μ + ε * μ univ) l (𝓝 (ε * μ univ)) := by
      simpa using hf.add_const (ε * μ univ)
    refine ge_of_tendsto hlim ?_
    filter_upwards [h ε hε] with i hi
    calc ∫⁻ x, g x ∂μ ≤ ∫⁻ x, (f i x + ε) ∂μ := lintegral_mono_ae hi
      _ = ∫⁻ x, f i x ∂μ + ε * μ univ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const]
  have hlim : Tendsto (fun ε : ℝ≥0 ↦ (ε : ℝ≥0∞) * μ univ) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ≥0 ↦ (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) :=
      ENNReal.tendsto_coe.2 (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr (measure_ne_top μ univ))
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hle))

end TauCeti
