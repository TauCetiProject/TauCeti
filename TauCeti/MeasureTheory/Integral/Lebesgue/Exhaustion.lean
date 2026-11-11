/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Lebesgue integrals over an increasing family of sets

The Lebesgue integrals of a function `f : α → ℝ≥0∞` over an increasing countable family of sets
tend to its integral over their union. No measurability of `f` or of the sets is assumed. This is
the `ℝ≥0∞`-valued counterpart of Mathlib's `MeasureTheory.tendsto_setIntegral_of_monotone`, and it
computes integrals over unbounded domains by exhausting them with bounded pieces.

## Main statements

* `TauCeti.tendsto_setLIntegral_of_monotone`: `∫⁻_{s i} f → ∫⁻_{⋃ i, s i} f` for monotone `s`.
* `TauCeti.setLIntegral_le_of_forall_inter_le`: `∫_A g ≤ c` when the integrals over the pieces
  `A ∩ V n` of an exhaustion `V` of `A` are eventually bounded by a family converging to `c`.
-/

public section

namespace TauCeti

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Integrals over an exhaustion.** The integrals of `f` over an increasing countable family of
sets `s i` tend to its integral over their union. -/
theorem tendsto_setLIntegral_of_monotone {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [Countable ι] [Preorder ι] [IsDirectedOrder ι] {f : α → ℝ≥0∞} {s : ι → Set α}
    (hs : Monotone s) :
    Tendsto (fun i ↦ ∫⁻ x in s i, f x ∂μ) atTop (𝓝 (∫⁻ x in ⋃ i, s i, f x ∂μ)) := by
  rw [setLIntegral_iUnion_of_directed _ hs.directed_le]
  exact tendsto_atTop_iSup fun i j hij ↦ lintegral_mono' (Measure.restrict_mono (hs hij) le_rfl)
    le_rfl

/-- If the integrals of `g` over `A ∩ V n`, for an increasing family of sets `V n` covering `A`,
indexed by a countable directed order, are eventually bounded by a family converging to `c`, then
the integral of `g` over `A` is at most `c`. -/
theorem setLIntegral_le_of_forall_inter_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [Countable ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {A : Set α} {V : ι → Set α} (hV : Monotone V)
    (hA : A ⊆ ⋃ n, V n) {g : α → ℝ≥0∞} {f : ι → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : Tendsto f atTop (𝓝 c))
    (h : ∀ᶠ n in atTop, ∫⁻ x in A ∩ V n, g x ∂μ ≤ f n) :
    ∫⁻ x in A, g x ∂μ ≤ c := by
  have hAV : ⋃ n, A ∩ V n = A := by rw [← Set.inter_iUnion, Set.inter_eq_left.2 hA]
  have h1 := tendsto_setLIntegral_of_monotone (μ := μ) (f := g) (s := fun n => A ∩ V n)
    fun m n hmn => Set.inter_subset_inter_right A (hV hmn)
  rw [hAV] at h1
  exact le_of_tendsto_of_tendsto h1 hf h

end TauCeti
