/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Cycle

/-!
# Chains on a list followed by itself

A list followed by itself is a chain for a relation exactly when the list is a chain as a cycle:
consecutive entries are related, and so is the last entry to the first. This cyclic condition is
invariant under rotating the list, and it can be assembled from two chains, one leading from a
nonempty block to another and one leading back.
-/

public section

namespace List

variable {α : Type*} {R : α → α → Prop}

/-- A list followed by itself is a chain exactly when the list is a chain as a cycle. -/
theorem isChain_append_self_iff {l : List α} :
    (l ++ l).IsChain R ↔ Cycle.Chain R (l : Cycle α) := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [Cycle.chain_coe_cons]
    refine ⟨fun h => h.prefix ⟨l, by simp⟩, fun h => ?_⟩
    simpa using h.append_overlap (l₁ := a :: l) (l₂ := [a]) (l₃ := l)
      (by simpa using h.left_of_append) (by simp)

/-- The chain condition on a list followed by itself is invariant under rotating the list. -/
theorem IsRotated.isChain_append_self_iff {l l' : List α} (h : l ~r l') :
    (l ++ l).IsChain R ↔ (l' ++ l').IsChain R := by
  rw [List.isChain_append_self_iff, List.isChain_append_self_iff, Cycle.coe_eq_coe.2 h]

/-- A cyclic version of `List.IsChain.append_overlap`: chains running from a nonempty block `l₁`
to a nonempty block `l₃` and from `l₃` back to `l₁` close up to a chain on the cycle
`l₁ ++ l₂ ++ l₃ ++ l₄`. -/
theorem IsChain.append_self_of_overlap {l₁ l₂ l₃ l₄ : List α} (h : (l₁ ++ l₂ ++ l₃).IsChain R)
    (h' : (l₃ ++ l₄ ++ l₁).IsChain R) (h₁ : l₁ ≠ []) (h₃ : l₃ ≠ []) :
    (l₁ ++ l₂ ++ l₃ ++ l₄ ++ (l₁ ++ l₂ ++ l₃ ++ l₄)).IsChain R := by
  have g : (l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₁).IsChain R := by
    simpa using h.append_overlap (by simpa using h') h₃
  simpa using g.append_overlap (l₃ := l₂ ++ l₃ ++ l₄) (g.prefix ⟨l₁, by simp⟩) h₁

end List
