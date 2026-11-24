/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Disjoint

/-!
# Nested or disjoint elements

Two elements of a partial order with a bottom element are nested or disjoint when one lies below
the other or they are disjoint. A family is laminar when its members are pairwise nested or
disjoint. For finite sets this is the classical notion of a laminar family.

## Main declarations

* `TauCeti.NestedOrDisjoint`: the relation defining laminar families.
* `TauCeti.NestedOrDisjoint.inf`: the meet of two elements that are nested with or disjoint from
  a third one is again nested with or disjoint from it.
* `TauCeti.NestedOrDisjoint.sup`: the same for the join of two non-disjoint elements, in a
  distributive lattice.

## References

* B. Korte and J. Vygen, *Combinatorial Optimization: Theory and Algorithms*, Section 2.2, for
  laminar families of finite sets.
-/

public section

namespace TauCeti

variable {α : Type*}

section PartialOrder

variable [PartialOrder α] [OrderBot α] {a b c : α}

/-- Two elements are nested or disjoint when one lies below the other or they are disjoint. A
family is laminar when its members are pairwise nested or disjoint. -/
def NestedOrDisjoint (a b : α) : Prop := a ≤ b ∨ b ≤ a ∨ Disjoint a b

/-- Two elements are nested or disjoint exactly when one lies below the other or they are
disjoint. -/
theorem nestedOrDisjoint_def : NestedOrDisjoint a b ↔ a ≤ b ∨ b ≤ a ∨ Disjoint a b := Iff.rfl

/-- An element is nested with everything above it. -/
theorem NestedOrDisjoint.of_le (h : a ≤ b) : NestedOrDisjoint a b :=
  Or.inl h

/-- An element is nested with everything below it. -/
theorem NestedOrDisjoint.of_ge (h : b ≤ a) : NestedOrDisjoint a b :=
  Or.inr (Or.inl h)

/-- Disjoint elements are nested or disjoint. -/
theorem NestedOrDisjoint.of_disjoint (h : Disjoint a b) : NestedOrDisjoint a b :=
  Or.inr (Or.inr h)

/-- Being nested or disjoint is a symmetric relation. -/
theorem nestedOrDisjoint_comm : NestedOrDisjoint a b ↔ NestedOrDisjoint b a := by
  rw [nestedOrDisjoint_def, nestedOrDisjoint_def, disjoint_comm, or_left_comm]

/-- Every element is nested with itself. -/
@[simp] theorem NestedOrDisjoint.refl (a : α) : NestedOrDisjoint a a :=
  .of_le le_rfl

/-- Being nested or disjoint is a reflexive relation. -/
instance instReflNestedOrDisjoint : Std.Refl (NestedOrDisjoint (α := α)) :=
  ⟨NestedOrDisjoint.refl⟩

/-- Being nested or disjoint is a symmetric relation. -/
@[symm] theorem NestedOrDisjoint.symm (h : NestedOrDisjoint a b) : NestedOrDisjoint b a :=
  nestedOrDisjoint_comm.mp h

/-- Being nested or disjoint is a symmetric relation. -/
instance instSymmNestedOrDisjoint : Std.Symm (NestedOrDisjoint (α := α)) :=
  ⟨fun _ _ ↦ NestedOrDisjoint.symm⟩

/-- The bottom element is nested with every element. -/
@[simp] theorem nestedOrDisjoint_bot_left (a : α) : NestedOrDisjoint ⊥ a :=
  .of_le bot_le

/-- Every element is nested with the bottom element. -/
@[simp] theorem nestedOrDisjoint_bot_right (a : α) : NestedOrDisjoint a ⊥ :=
  .of_ge bot_le

end PartialOrder

/-- Taking the meet of two elements preserves being nested with or disjoint from a third one. -/
theorem NestedOrDisjoint.inf [SemilatticeInf α] [OrderBot α] {a b c : α}
    (ha : NestedOrDisjoint a c) (hb : NestedOrDisjoint b c) : NestedOrDisjoint (a ⊓ b) c := by
  rcases ha with ha | ha | ha
  · exact .of_le (inf_le_of_left_le ha)
  · rcases hb with hb | hb | hb
    · exact .of_le (inf_le_of_right_le hb)
    · exact .of_ge (le_inf ha hb)
    · exact .of_disjoint (hb.mono_left inf_le_right)
  · exact .of_disjoint (ha.mono_left inf_le_left)

/-- The join of two non-disjoint elements is nested with or disjoint from every element that is
nested with or disjoint from both of them. Disjointness of the two elements breaks this: the
finite sets `{1}` and `{2}` are nested with or disjoint from `{1, 3}`, but `{1, 2}` is not.
Distributivity is also needed: in the lattice of subspaces of a four-dimensional vector space,
two planes meeting in a line are both disjoint from a plane that meets their three-dimensional
join in a line lying in neither of them. -/
theorem NestedOrDisjoint.sup [DistribLattice α] [OrderBot α] {a b c : α} (hab : ¬Disjoint a b)
    (ha : NestedOrDisjoint a c) (hb : NestedOrDisjoint b c) : NestedOrDisjoint (a ⊔ b) c := by
  rcases ha with ha | ha | ha
  · rcases hb with hb | hb | hb
    · exact .of_le (sup_le ha hb)
    · exact .of_ge (le_sup_of_le_right hb)
    · exact absurd (hb.mono_right ha).symm hab
  · exact .of_ge (le_sup_of_le_left ha)
  · rcases hb with hb | hb | hb
    · exact absurd (ha.mono_right hb) hab
    · exact .of_ge (le_sup_of_le_right hb)
    · exact .of_disjoint (ha.sup_left hb)

end TauCeti
