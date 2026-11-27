/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Almost everywhere inequalities and limits

Almost everywhere inequalities pass to almost everywhere limits along countably generated
filters in spaces with a closed order relation. The inequalities need only hold frequently,
so the result also applies to subsequences used in integral limit arguments. In particular, an
almost everywhere bound `g ≤ C (f + δ)` for every `δ = 1/(k + 1)` gives `g ≤ C f` almost
everywhere.

A sequence of sets covered almost everywhere by the union of two vanishing sequences also has
outer measure tending to zero (`TauCeti.tendsto_measure_of_ae_subset_union`).

A property holding almost everywhere holds at every point of positive mass
(`Filter.Eventually.self_of_ae_of_measure_singleton_ne_zero`).
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

variable {α : Type*} {M : Type*} [FunLike M (Set α) ℝ≥0∞] [OuterMeasureClass M α] {μ : M} in
/-- A property holding almost everywhere holds at every point of positive mass. -/
theorem Filter.Eventually.self_of_ae_of_measure_singleton_ne_zero {p : α → Prop}
    (h : ∀ᵐ y ∂μ, p y) {x : α} (hx : μ {x} ≠ 0) : p x := by
  by_contra hne
  exact hx (measure_mono_null (Set.singleton_subset_iff.2 hne) (ae_iff.1 h))

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

/-- **The limit `δ → 0`.** If `g ≤ C (f + δ)` almost everywhere for every `δ = 1/(k + 1)`, then
`g ≤ C f` almost everywhere. -/
theorem ae_le_mul_of_forall_ae_le_mul_add_one_div {f g : α → ℝ} {C : ℝ}
    (h : ∀ k : ℕ, ∀ᵐ x ∂μ, g x ≤ C * (f x + 1 / ((k : ℝ) + 1))) : ∀ᵐ x ∂μ, g x ≤ C * f x := by
  filter_upwards [ae_all_iff.2 h] with x hx
  simpa using ge_of_tendsto' ((tendsto_one_div_add_atTop_nhds_zero_nat.const_add _).const_mul C) hx

end TauCeti
