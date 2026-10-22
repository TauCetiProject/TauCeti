/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic.Tauto

/-!
# Laminar families and crossing bipartitions of finite sets

Two finite sets are nested or disjoint if one contains the other or they do not meet.
Two bipartitions cross if all four intersections of their sides are nonempty. Choosing the
side avoiding a fixed root identifies pairwise non-crossing bipartitions with laminar families.

## Main declarations

* `Finset.NestedOrDisjoint`: the relation defining laminar families.
* `Finset.Crosses`: crossing of the bipartitions determined by two finite sets.
* `Finset.sideAvoiding`: the side of a bipartition avoiding a chosen root.
* `Finset.pairwise_nestedOrDisjoint_image_sideAvoiding`: the root convention for a family.

## References

* B. Korte and J. Vygen, *Combinatorial Optimization: Theory and Algorithms*, Section 8.6.
* D. Gusfield, *Very Simple Methods for All Pairs Network Flow Analysis*, SIAM J. Comput. 19
  (1990), 143–155.
-/

public section

namespace Finset

variable {V : Type*}

/-!
## Laminar and crossing cuts

A family of sets is laminar when its members are pairwise nested or disjoint. Two cuts, viewed as
bipartitions, cross when each side of one meets each side of the other. Choosing for every cut
its side avoiding a fixed root vertex turns a pairwise non-crossing family of cuts into a laminar
family. This lets uncrossing arguments for symmetric set functions work with laminar families.
-/

section Laminar

/-- Two sets are nested or disjoint when one contains the other or they do not meet. A family
is laminar when its members are pairwise nested or disjoint. -/
def NestedOrDisjoint (S T : Finset V) : Prop := S ⊆ T ∨ T ⊆ S ∨ Disjoint S T

/-- Two sets are nested or disjoint exactly when one contains the other or they do not meet. -/
theorem nestedOrDisjoint_def {S T : Finset V} :
    NestedOrDisjoint S T ↔ S ⊆ T ∨ T ⊆ S ∨ Disjoint S T := Iff.rfl

/-- A set is nested with every superset. -/
theorem NestedOrDisjoint.of_subset {S T : Finset V} (h : S ⊆ T) : NestedOrDisjoint S T :=
  Or.inl h

/-- A set is nested with every subset. -/
theorem NestedOrDisjoint.of_superset {S T : Finset V} (h : T ⊆ S) : NestedOrDisjoint S T :=
  Or.inr (Or.inl h)

/-- Disjoint sets are nested or disjoint. -/
theorem NestedOrDisjoint.of_disjoint {S T : Finset V} (h : Disjoint S T) :
    NestedOrDisjoint S T :=
  Or.inr (Or.inr h)

/-- Being nested or disjoint is a symmetric relation. -/
theorem nestedOrDisjoint_comm {S T : Finset V} :
    NestedOrDisjoint S T ↔ NestedOrDisjoint T S := by
  simp only [NestedOrDisjoint, disjoint_comm (a := S)]
  tauto

/-- Being nested or disjoint is a symmetric relation. -/
theorem NestedOrDisjoint.symm {S T : Finset V} (h : NestedOrDisjoint S T) :
    NestedOrDisjoint T S :=
  nestedOrDisjoint_comm.mp h

variable [DecidableEq V]

/-- Intersecting two sets preserves being nested with or disjoint from a third set. -/
theorem NestedOrDisjoint.inter {S T U : Finset V} (hS : NestedOrDisjoint S U)
    (hT : NestedOrDisjoint T U) : NestedOrDisjoint (S ∩ T) U := by
  simp only [NestedOrDisjoint, subset_iff, disjoint_left, mem_inter] at *
  grind

/-- The union of two meeting sets is nested with or disjoint from every set that is nested with
or disjoint from both of them. Without a common element this fails: `{1}` and `{2}` are nested
with or disjoint from `{1, 3}`, but `{1, 2}` is not. -/
theorem NestedOrDisjoint.union {S T U : Finset V} (hST : (S ∩ T).Nonempty)
    (hS : NestedOrDisjoint S U) (hT : NestedOrDisjoint T U) :
    NestedOrDisjoint (S ∪ T) U := by
  obtain ⟨x, hx⟩ := hST
  simp only [NestedOrDisjoint, subset_iff, disjoint_left, mem_inter, mem_union] at *
  grind

end Laminar

section Crossing

/-- Two cuts `(S, Sᶜ)` and `(T, Tᶜ)` cross when each side of one meets each side of the other. -/
def Crosses (S T : Finset V) : Prop :=
  (∃ v ∈ S, v ∈ T) ∧ (∃ v ∈ S, v ∉ T) ∧ (∃ v ∈ T, v ∉ S) ∧ ∃ v, v ∉ S ∧ v ∉ T

/-- Two cuts cross exactly when each side of one contains a vertex of each side of the other. -/
theorem crosses_def {S T : Finset V} :
    Crosses S T ↔
      (∃ v ∈ S, v ∈ T) ∧ (∃ v ∈ S, v ∉ T) ∧ (∃ v ∈ T, v ∉ S) ∧ ∃ v, v ∉ S ∧ v ∉ T :=
  Iff.rfl

/-- Two cuts cross exactly when the four intersections of their sides are nonempty. -/
theorem crosses_iff [Fintype V] [DecidableEq V] {S T : Finset V} :
    Crosses S T ↔
      (S ∩ T).Nonempty ∧ (S \ T).Nonempty ∧ (T \ S).Nonempty ∧ (Sᶜ ∩ Tᶜ).Nonempty := by
  simp [Crosses, Finset.Nonempty]

/-- Crossing is a symmetric relation. -/
theorem crosses_comm {S T : Finset V} : Crosses S T ↔ Crosses T S := by
  simp only [Crosses]
  grind

/-- Crossing is a symmetric relation. -/
theorem Crosses.symm {S T : Finset V} (h : Crosses S T) : Crosses T S :=
  crosses_comm.mp h

/-- Crossing depends only on the bipartition, not on the side chosen for the first cut. -/
@[simp] theorem crosses_compl_left [Fintype V] [DecidableEq V] {S T : Finset V} :
    Crosses Sᶜ T ↔ Crosses S T := by
  simp only [Crosses, mem_compl, not_not]
  grind

/-- Crossing depends only on the bipartition, not on the side chosen for the second cut. -/
@[simp] theorem crosses_compl_right [Fintype V] [DecidableEq V] {S T : Finset V} :
    Crosses S Tᶜ ↔ Crosses S T := by
  rw [crosses_comm, crosses_compl_left, crosses_comm]

/-- Nested or disjoint sets do not cross. -/
theorem NestedOrDisjoint.not_crosses {S T : Finset V} (h : NestedOrDisjoint S T) :
    ¬Crosses S T := by
  simp only [NestedOrDisjoint, Crosses, subset_iff, disjoint_left] at *
  grind

/-- **Root convention.** Two sets avoiding a common vertex do not cross exactly when they are
nested or disjoint: their union cannot cover all vertices. -/
theorem not_crosses_iff_nestedOrDisjoint {r : V} {S T : Finset V} (hS : r ∉ S) (hT : r ∉ T) :
    ¬Crosses S T ↔ NestedOrDisjoint S T := by
  refine ⟨fun h ↦ ?_, NestedOrDisjoint.not_crosses⟩
  simp only [NestedOrDisjoint, Crosses, subset_iff, disjoint_left] at *
  grind

/-- **Uncrossing preserves non-crossing.** The union of two meeting sets crosses no cut that
neither of them crosses. -/
theorem not_crosses_union [DecidableEq V] {S T U : Finset V} (hST : (S ∩ T).Nonempty)
    (hSU : ¬Crosses S U) (hTU : ¬Crosses T U) : ¬Crosses (S ∪ T) U := by
  obtain ⟨x, hx⟩ := hST
  simp only [Crosses, mem_inter, mem_union] at *
  grind

variable [Fintype V] [DecidableEq V]

/-- The side of the cut `(S, Sᶜ)` not containing the root vertex `r`. -/
def sideAvoiding (r : V) (S : Finset V) : Finset V := if r ∈ S then Sᶜ else S

/-- The side avoiding the root does not contain it. -/
@[simp] theorem notMem_sideAvoiding (r : V) (S : Finset V) : r ∉ sideAvoiding r S := by
  by_cases h : r ∈ S <;> simp [sideAvoiding, h]

/-- A vertex lies in the side avoiding the root exactly when it lies on the opposite side of
the cut from the root. -/
@[simp] theorem mem_sideAvoiding {r v : V} {S : Finset V} :
    v ∈ sideAvoiding r S ↔ (v ∈ S ↔ r ∉ S) := by
  by_cases h : r ∈ S <;> simp [sideAvoiding, h]

/-- A side not containing the root is its own side avoiding the root. -/
@[simp] theorem sideAvoiding_of_notMem {r : V} {S : Finset V} (h : r ∉ S) :
    sideAvoiding r S = S := by
  simp [sideAvoiding, h]

/-- The side avoiding the root of a side containing it is the complement. -/
@[simp] theorem sideAvoiding_of_mem {r : V} {S : Finset V} (h : r ∈ S) :
    sideAvoiding r S = Sᶜ := by
  simp [sideAvoiding, h]

/-- Both sides of a cut have the same side avoiding the root. -/
@[simp] theorem sideAvoiding_compl (r : V) (S : Finset V) :
    sideAvoiding r Sᶜ = sideAvoiding r S := by
  by_cases h : r ∈ S <;> simp [sideAvoiding, h]

/-- Replacing the first cut by its side avoiding the root does not affect crossing. -/
@[simp] theorem crosses_sideAvoiding_left {r : V} {S T : Finset V} :
    Crosses (sideAvoiding r S) T ↔ Crosses S T := by
  by_cases h : r ∈ S <;> simp [sideAvoiding, h]

/-- Replacing the second cut by its side avoiding the root does not affect crossing. -/
@[simp] theorem crosses_sideAvoiding_right {r : V} {S T : Finset V} :
    Crosses S (sideAvoiding r T) ↔ Crosses S T := by
  by_cases h : r ∈ T <;> simp [sideAvoiding, h]

/-- **Root convention.** Representing each cut of a pairwise non-crossing family by its side
avoiding a fixed root vertex gives a laminar family. -/
theorem pairwise_nestedOrDisjoint_image_sideAvoiding {𝒞 : Set (Finset V)}
    (h𝒞 : 𝒞.Pairwise fun S T ↦ ¬Crosses S T) (r : V) :
    (sideAvoiding r '' 𝒞).Pairwise NestedOrDisjoint := by
  rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ hne
  rw [← not_crosses_iff_nestedOrDisjoint (notMem_sideAvoiding r S) (notMem_sideAvoiding r T),
    crosses_sideAvoiding_left, crosses_sideAvoiding_right]
  exact h𝒞 hS hT fun h ↦ hne (h ▸ rfl)

end Crossing

end Finset
