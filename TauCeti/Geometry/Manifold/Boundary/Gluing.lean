/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Basic

/-!
# Topological gluing data

A quotient presentation for gluing two spaces along an explicitly supplied equivalence relation.
This is the topological substrate consumed by manifold gluing constructions.
-/

public section

namespace TauCeti

variable {M N : Type*}

namespace TopologicalGluing

variable (r : Setoid (M ⊕ N))

/-- The canonical map from the left summand into a gluing. -/
def inl : M → Quotient r := Quotient.mk' (s := r) ∘ Sum.inl

/-- The canonical map from the right summand into a gluing. -/
def inr : N → Quotient r := Quotient.mk' (s := r) ∘ Sum.inr

/-- Every point of a gluing is represented by one of the two summands. -/
theorem surjective :
    Function.Surjective (Sum.elim (inl r) (inr r)) := by
  intro z
  refine Quotient.inductionOn' z ?_
  intro x
  cases x with
  | inl x => exact ⟨Sum.inl x, rfl⟩
  | inr y => exact ⟨Sum.inr y, rfl⟩

end TopologicalGluing
end TauCeti
