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
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

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
