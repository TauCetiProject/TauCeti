/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Path.Basic

/-!
# Trees of Serre graphs

A Serre tree is a nonempty connected graph without a nonempty reduced closed path. The
one-vertex graph without edges is a tree. A rose with a petal is not a tree, since its petal
is a reduced loop.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2.
-/

public section

universe u v

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- A tree is a connected Serre graph in which every reduced closed path is empty. -/
def IsTree : Prop :=
  Γ.Connected ∧ ∀ (u : Γ.V) (p : Γ.Path u u), Path.IsReduced Γ p → p = Quiver.Path.nil

namespace IsTree

/-- Every tree is connected. -/
theorem connected (h : Γ.IsTree) : Γ.Connected := h.1

/-- Every reduced closed path in a tree is empty. -/
theorem eq_nil_of_isReduced (h : Γ.IsTree) {u : Γ.V} (p : Γ.Path u u)
    (hp : Path.IsReduced Γ p) : p = Quiver.Path.nil := h.2 u p hp

end IsTree

/-- Characterization of Serre trees by connectedness and reduced closed paths. -/
theorem isTree_iff : Γ.IsTree ↔
    Γ.Connected ∧ ∀ (u : Γ.V) (p : Γ.Path u u), Path.IsReduced Γ p →
      p = Quiver.Path.nil := Iff.rfl

/-- The graph with one vertex and no edges is a tree. -/
theorem single_vertex_isTree : point.{u, v}.IsTree := by
  rw [isTree_iff]
  refine ⟨?_, ?_⟩
  · rw [point.{u, v}.connected_iff]
    refine ⟨⟨PUnit.unit⟩, ?_⟩
    rw [point.{u, v}.preconnected_iff]
    intro u v
    cases u
    cases v
    exact ⟨(@Quiver.Path.nil point.{u, v}.V point.{u, v}.toQuiver PUnit.unit)⟩
  · intro u p _
    cases p with
    | nil => rfl
    | cons p e => exact e.1.elim

/-- A rose with a petal is not a tree. -/
theorem rose_not_isTree {α : Type*} (a : α) : ¬(rose α).IsTree := by
  intro h
  have hp := h.eq_nil_of_isReduced (rose α) (rosePetal a) (rosePetal_isReduced a)
  rw [rosePetal_eq_toPath] at hp
  cases hp

/-- The one-petal rose is not a tree. -/
theorem rose_one_not_tree : ¬(rose PUnit).IsTree :=
  rose_not_isTree PUnit.unit

end SerreGraph
end TauCeti
