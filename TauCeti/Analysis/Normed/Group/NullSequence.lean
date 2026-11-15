/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Set.Countable
import TauCeti.Order.Filter.Cofinite.Seq

/-!
# Assembling null sequences from countably many finite sets

In a seminormed group, countably many finite sets whose norms are bounded by a sequence tending
to `0`, together with one further finite set, can all be listed in the range of a single sequence
tending to `0`. This is how null sequences are built from finite nets at shrinking scales, as in
Grothendieck's compactness lemma.
-/

public section

open Filter Metric Set Topology

variable {E : Type*} [SeminormedAddGroup E]

namespace TauCeti

/-- Countably many finite sets, the `k`-th inside the closed ball of radius `r k → 0` about the
origin, together with one further finite set, lie in the range of a single sequence tending
to `0`. -/
theorem exists_tendsto_zero_union_iUnion_subset_range {A : Set E} {B : ℕ → Set E}
    {r : ℕ → ℝ} (hA : A.Finite) (hB : ∀ k, (B k).Finite) (hBr : ∀ k, ∀ z ∈ B k, ‖z‖ ≤ r k)
    (hr : Tendsto r atTop (𝓝 0)) :
    ∃ x : ℕ → E, Tendsto x atTop (𝓝 0) ∧ A ∪ ⋃ k, B k ⊆ range x := by
  set S := A ∪ ⋃ k, B k
  have : Countable S := (hA.countable.union (countable_iUnion fun k ↦ (hB k).countable)).to_subtype
  -- Only the finitely many sets `B k` with `k < K` meet the complement of `ball 0 ε`.
  have hS : Tendsto ((↑) : S → E) cofinite (𝓝 0) := by
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hr.eventually (gt_mem_nhds hε))
    rw [mem_map, mem_cofinite]
    refine ((hA.union (finite_iUnion fun k : Fin K ↦ hB k)).preimage
      Subtype.val_injective.injOn).subset ?_
    rintro ⟨z, hzA | hzB⟩ hzU
    · exact Or.inl hzA
    obtain ⟨k, hk⟩ := mem_iUnion.1 hzB
    refine Or.inr (mem_iUnion.2 ⟨⟨k, not_le.1 fun hKk ↦ hzU (hεU ?_)⟩, hk⟩)
    exact mem_ball_zero_iff.2 ((hBr k z hk).trans_lt (hK k hKk))
  obtain ⟨x, hx, hSx⟩ := hS.exists_seq_tendsto_range_subset (pure_le_nhds 0)
  exact ⟨x, hx, Subtype.range_coe (s := S) ▸ hSx⟩

end TauCeti
