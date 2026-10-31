/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Cofinite
import Mathlib.Logic.Encodable.Basic

/-!
# Enumerating a cofinitely convergent countable family by a sequence

A countable family `g : ι → α` tending to a filter `l` along the cofinite filter can be listed,
with padding, as a sequence `ℕ → α` tending to `l` along `atTop`. The padding is a point `b`
lying in every member of `l`, such as the limit `a` when `l = 𝓝 a`. This turns a countable set
whose points outside each neighbourhood of `a` are finitely many into a sequence converging to
`a`, which is how null sequences are assembled from countably many finite sets.
-/

public section

open Filter Set

/-- A countable family tending to `l` along the cofinite filter is part of a sequence tending to
`l`, padded by a point `b` lying in every member of `l`. -/
theorem Filter.Tendsto.exists_seq_tendsto_range_subset {ι α : Type*} [Countable ι] {g : ι → α}
    {l : Filter α} {b : α} (hg : Tendsto g cofinite l) (hb : pure b ≤ l) :
    ∃ x : ℕ → α, Tendsto x atTop l ∧ range g ⊆ range x := by
  obtain ⟨f, hf⟩ := exists_injective_nat ι
  refine ⟨Function.extend f g fun _ ↦ b, ?_, ?_⟩
  · rw [← Nat.cofinite_eq_atTop]
    intro U hU
    -- Off the range of `f` the sequence is `b ∈ U`; on it, `f` lists the finitely many `g i ∉ U`.
    rw [mem_map, mem_cofinite]
    refine ((mem_cofinite.1 (hg hU)).image f).subset fun n hn ↦ ?_
    by_cases hn' : ∃ i, f i = n
    · obtain ⟨i, rfl⟩ := hn'
      rw [mem_compl_iff, mem_preimage, hf.extend_apply] at hn
      exact ⟨i, hn, rfl⟩
    · rw [mem_compl_iff, mem_preimage, Function.extend_apply' _ _ _ hn'] at hn
      exact absurd (hb hU) hn
  · rintro _ ⟨i, rfl⟩
    exact ⟨f i, hf.extend_apply _ _ _⟩
