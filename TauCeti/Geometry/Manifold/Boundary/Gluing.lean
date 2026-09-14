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

/-- The quotient space obtained by gluing the summands according to an equivalence relation. -/
def TopologicalGluing (r : Setoid (M ⊕ N)) := Quotient r

namespace TopologicalGluing

variable (r : Setoid (M ⊕ N))

/-- The canonical map from the left summand into a gluing. -/
def inl : M → TopologicalGluing r := Quotient.mk' (s := r) ∘ Sum.inl

/-- The canonical map from the right summand into a gluing. -/
def inr : N → TopologicalGluing r := Quotient.mk' (s := r) ∘ Sum.inr

theorem surjective :
    Function.Surjective (Sum.elim (inl r) (inr r)) := by
  intro z
  refine Quotient.inductionOn' z ?_
  intro x
  cases x with
  | inl x => exact ⟨Sum.inl x, rfl⟩
  | inr y => exact ⟨Sum.inr y, rfl⟩

/-- The two canonical inclusions agree whenever the relation identifies the corresponding points. -/
theorem eq_of_rel {a : M} {b : N} (h : (Sum.inl a : M ⊕ N) ≈ Sum.inr b) :
    inl r a = inr r b :=
  Quotient.sound h

end TopologicalGluing
end TauCeti
