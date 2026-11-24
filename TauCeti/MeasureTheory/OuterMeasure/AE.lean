/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Almost everywhere inequalities and limits

Almost everywhere inequalities pass to almost everywhere limits along countably generated
filters in spaces with a closed order relation. The inequalities need only hold frequently,
so the result also applies to subsequences used in integral limit arguments.

A sequence of sets covered almost everywhere by the union of two vanishing sequences also has
outer measure tending to zero (`TauCeti.tendsto_measure_of_ae_subset_union`).
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

section

variable {α ι M : Type*} [FunLike M (Set α) ℝ≥0∞] [OuterMeasureClass M α] {μ : M} {l : Filter ι}

/-- If `A k ⊆ B k ∪ C k` almost everywhere along a filter `l`, and both `μ (B k)` and
`μ (C k)` tend to `0`, then `μ (A k)` tends to `0`. -/
theorem tendsto_measure_of_ae_subset_union {A B C : ι → Set α}
    (hB : Tendsto (fun k ↦ μ (B k)) l (𝓝 0))
    (hC : Tendsto (fun k ↦ μ (C k)) l (𝓝 0))
    (hsub : ∀ᶠ k in l, A k ≤ᵐ[μ] (B k ∪ C k : Set α)) :
    Tendsto (fun k ↦ μ (A k)) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using hB.add hC) (Eventually.of_forall fun _ ↦ zero_le)
    (hsub.mono fun k hk ↦ (measure_mono_ae hk).trans (measure_union_le (B k) (C k)))

end

variable {α ι M : Type*} [FunLike M (Set α) ℝ≥0∞] [OuterMeasureClass M α] {μ : M} {l : Filter ι}
  [l.IsCountablyGenerated]

/-- Almost everywhere inequalities between two families of functions pass to their almost
everywhere limits along a countably generated filter when the order relation is closed.
The inequalities need only hold frequently along the filter. -/
theorem ae_le_of_tendsto_of_tendsto_of_frequently {β : Type*} [TopologicalSpace β] [Preorder β]
    [OrderClosedTopology β] {F₁ F₂ : ι → α → β} {G₁ G₂ : α → β}
    (hlim₁ : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F₁ i x) l (𝓝 (G₁ x)))
    (hlim₂ : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F₂ i x) l (𝓝 (G₂ x)))
    (hF : ∃ᶠ i in l, F₁ i ≤ᵐ[μ] F₂ i) : G₁ ≤ᵐ[μ] G₂ := by
  obtain ⟨u, hu, hle⟩ := exists_seq_forall_of_frequently hF
  filter_upwards [hlim₁, hlim₂, ae_all_iff.2 hle] with x hx₁ hx₂ hle using
    le_of_tendsto_of_tendsto' (hx₁.comp hu) (hx₂.comp hu) hle

end TauCeti
