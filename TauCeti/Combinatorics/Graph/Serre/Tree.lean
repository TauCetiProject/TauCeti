/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Reduction

/-!
# Trees of Serre graphs

A Serre graph is acyclic when it has no nonempty reduced closed path, and a tree when it is
moreover nonempty and connected. Equivalently, an acyclic graph has at most one reduced path
between two vertices, and a tree has exactly one. These unique reduced paths are the tree paths
used to build the free basis of the fundamental group of a graph from a spanning tree.

An acyclic graph has no loop, and a restriction `Γ.restrict S hS` is acyclic exactly when no
nonempty reduced closed path of `Γ` has all its darts in `S`.

The one-vertex graph without edges and the segment are trees. A rose with a petal is not a tree,
since its petal is a reduced loop.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2.
-/

public section

universe u v

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- A Serre graph is acyclic, or a forest, when every reduced closed path is empty. -/
def IsAcyclic : Prop :=
  ∀ (u : Γ.V) (p : Γ.Path u u), Path.IsReduced Γ p → p = Quiver.Path.nil

/-- Unfold acyclicity: every reduced closed path is empty. -/
theorem isAcyclic_iff : Γ.IsAcyclic ↔
    ∀ (u : Γ.V) (p : Γ.Path u u), Path.IsReduced Γ p → p = Quiver.Path.nil := Iff.rfl

/-- A tree is a connected acyclic Serre graph. -/
def IsTree : Prop :=
  Γ.Connected ∧ Γ.IsAcyclic

/-- Characterization of Serre trees as connected acyclic graphs. -/
theorem isTree_iff : Γ.IsTree ↔ Γ.Connected ∧ Γ.IsAcyclic := Iff.rfl

namespace IsTree

/-- Every tree is connected. -/
theorem connected (h : Γ.IsTree) : Γ.Connected := h.1

/-- Every tree is acyclic. -/
theorem isAcyclic (h : Γ.IsTree) : Γ.IsAcyclic := h.2

/-- Every reduced closed path in a tree is empty. -/
theorem eq_nil_of_isReduced (h : Γ.IsTree) {u : Γ.V} (p : Γ.Path u u)
    (hp : Path.IsReduced Γ p) : p = Quiver.Path.nil := h.2 u p hp

end IsTree

variable {Γ} in
/-- In an acyclic graph, two reduced paths with the same endpoints are equal. -/
theorem IsAcyclic.eq_of_isReduced (h : Γ.IsAcyclic) {a b : Γ.V} {p q : Γ.Path a b}
    (hp : Path.IsReduced Γ p) (hq : Path.IsReduced Γ q) : p = q := by
  have hpq : Path.reduce Γ (p.comp q.reverse) = Quiver.Path.nil :=
    h a _ (Path.isReduced_reduce Γ _)
  calc p = Path.reduce Γ (p.comp (q.reverse.comp q)) := by
        rw [← Path.reduce_comp_reduce_right, Path.reduce_reverse_comp, Quiver.Path.comp_nil,
          Path.reduce_eq_self_of_isReduced Γ p hp]
    _ = Path.reduce Γ ((Path.reduce Γ (p.comp q.reverse)).comp q) := by
        rw [Path.reduce_comp_reduce_left, Quiver.Path.comp_assoc]
    _ = q := by
        rw [hpq, Quiver.Path.nil_comp, Path.reduce_eq_self_of_isReduced Γ q hq]

variable {Γ} in
/-- An acyclic graph has no loop: a loop dart is a nonempty reduced closed path. -/
theorem IsAcyclic.src_ne_tgt (h : Γ.IsAcyclic) (e : Γ.E) : Γ.src e ≠ Γ.tgt e := by
  have key : ∀ {a b : Γ.V} (f : Quiver.Hom a b), a ≠ b := by
    rintro a _ f rfl
    cases h a f.toPath (Path.isReduced_toPath Γ f)
  exact key (Γ.dart e)

/-- A graph is acyclic exactly when any two reduced paths with the same endpoints are equal. -/
theorem isAcyclic_iff_eq_of_isReduced : Γ.IsAcyclic ↔
    ∀ ⦃a b : Γ.V⦄ (p q : Γ.Path a b), Path.IsReduced Γ p → Path.IsReduced Γ q → p = q :=
  ⟨fun h _ _ _ _ hp hq => h.eq_of_isReduced hp hq,
    fun h u p hp => h p .nil hp (Path.isReduced_nil Γ u)⟩

variable {Γ} in
/-- In a tree, any two vertices are joined by a path. -/
theorem IsTree.nonempty_path (h : Γ.IsTree) (a b : Γ.V) : Nonempty (Γ.Path a b) :=
  Γ.preconnected_iff.mp (Γ.connected_iff.mp h.connected).2 a b

variable {Γ} in
/-- In a tree, any two vertices are joined by exactly one reduced path. -/
theorem IsTree.existsUnique_isReduced (h : Γ.IsTree) (a b : Γ.V) :
    ∃! p : Γ.Path a b, Path.IsReduced Γ p := by
  obtain ⟨p⟩ := h.nonempty_path a b
  exact ⟨Path.reduce Γ p, Path.isReduced_reduce Γ p,
    fun q hq => h.isAcyclic.eq_of_isReduced hq (Path.isReduced_reduce Γ p)⟩

/-- A graph is a tree exactly when it is nonempty and any two vertices are joined by exactly one
reduced path. -/
theorem isTree_iff_existsUnique_isReduced : Γ.IsTree ↔
    Nonempty Γ.V ∧ ∀ a b : Γ.V, ∃! p : Γ.Path a b, Path.IsReduced Γ p := by
  refine ⟨fun h => ⟨(Γ.connected_iff.mp h.connected).1, h.existsUnique_isReduced⟩,
    fun ⟨hV, h⟩ => ?_⟩
  refine ⟨Γ.connected_iff.mpr ⟨hV, Γ.preconnected_iff.mpr fun a b => ⟨(h a b).exists.choose⟩⟩,
    ?_⟩
  exact (Γ.isAcyclic_iff_eq_of_isReduced).mpr fun a b p q hp hq => (h a b).unique hp hq

section Restrict

variable (S : Set Γ.E) (hS : ∀ e ∈ S, Γ.rev e ∈ S)

/-- The restriction is acyclic exactly when every reduced closed path of `Γ` whose darts lie in
`S` is empty. -/
theorem isAcyclic_restrict_iff : (Γ.restrict S hS).IsAcyclic ↔
    ∀ (u : Γ.V) (p : Γ.Path u u), Path.IsReduced Γ p → (∀ e ∈ Path.darts Γ p, e ∈ S) →
      p = Quiver.Path.nil := by
  rw [isAcyclic_iff]
  refine ⟨fun h u p hp hpS => ?_, fun h u q hq => ?_⟩
  · obtain ⟨q, rfl⟩ := Γ.exists_restrict_path S hS p hpS
    rw [h u q ((Γ.isReduced_restrictInclusion_mapPath_iff S hS q).mp hp)]
    rfl
  · have hp := h u _ ((Γ.isReduced_restrictInclusion_mapPath_iff S hS q).mpr hq)
      fun e he => Γ.mem_of_mem_darts_mapPath S hS q he
    cases q with
    | nil => rfl
    | cons q e => cases hp

/-- The restriction to the empty set of darts is acyclic. -/
theorem isAcyclic_restrict_empty : (Γ.restrict ∅ fun _ h => h.elim).IsAcyclic :=
  (Γ.isAcyclic_restrict_iff _ _).mpr fun _ p _ hp => Quiver.Path.eq_nil_of_length_zero _ (by
    rw [← Path.length_darts, List.eq_nil_iff_forall_not_mem.mpr fun e he => hp e he,
      List.length_nil])

end Restrict

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

/-- The segment, two vertices joined by a single pair of darts, is a tree. -/
theorem segment_isTree : segment.IsTree := by
  refine ⟨segment.connected_iff.mpr ⟨⟨true⟩, segment.preconnected_iff.mpr fun a b => ?_⟩,
    fun u p hp => ?_⟩
  · by_cases h : a = b
    · subst h
      exact ⟨.nil⟩
    · exact ⟨(Quiver.Hom.toPath (⟨a, rfl, by
        cases a <;> cases b <;> first | rfl | exact (h rfl).elim⟩ :
        Quiver.Hom a b))⟩
  · -- A closed path of one dart would join a vertex to its negation, and a second dart can
    -- only reverse the first.
    cases p with
    | nil => rfl
    | cons p f =>
      cases p with
      | nil =>
        -- The vertices and darts of the segment are both `Bool`, with `tgt f = !f`.
        exact absurd (f.2.2.trans f.2.1.symm) (Bool.not_ne_self f.1)
      | cons p e =>
        refine absurd ?_ ((Path.isReduced_cons_cons segment p e f).mp hp).2
        exact f.2.1.trans e.2.2.symm

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
