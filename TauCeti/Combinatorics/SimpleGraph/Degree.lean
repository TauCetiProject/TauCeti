/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Vertex degrees and graph actions

A vertex of degree at least three keeps two distinct neighbours after any single vertex is set
aside. This is the step that grows a branch vertex into a star: the vertex set aside is the
neighbour already used, for instance the next vertex along a path, and the two remaining
neighbours are new leaves.

A pretransitive action preserving adjacency makes all degrees equal when each neighbour
set is finite, without requiring a finite vertex set.

## Main results

* `SimpleGraph.degree_eq_of_pretransitive`: a pretransitive graph action preserves degrees.
* `SimpleGraph.exists_adj_adj_ne_of_three_le_degree`: a vertex of degree at least three has two
  distinct neighbours, both different from any given vertex.
-/

public section

namespace TauCeti

/-- **Two distinct neighbours of `v` other than a given vertex `x`, from a degree of at least
three.** -/
theorem _root_.SimpleGraph.exists_adj_adj_ne_of_three_le_degree {V : Type*}
    {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)] (hv : 3 ≤ G.degree v) (x : V) :
    ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b ∧ a ≠ x ∧ b ≠ x := by
  classical
  have hcard : 1 < ((G.neighborFinset v).erase x).card := by
    have := Finset.pred_card_le_card_erase (s := G.neighborFinset v) (a := x)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at this
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at ha hb
  exact ⟨a, b, ha.2, hb.2, hab, ha.1, hb.1⟩

/-- A pretransitive action preserving adjacency gives equal degrees in a locally finite graph. -/
theorem _root_.SimpleGraph.degree_eq_of_pretransitive
    {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {Γ : Type*} [Group Γ] [MulAction Γ V]
    [MulAction.IsPretransitive Γ V]
    (hact : ∀ (g : Γ) ⦃i j : V⦄, G.Adj i j → G.Adj (g • i) (g • j))
    (i j : V) : G.degree i = G.degree j := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Γ i j
  let e : G ≃g G :=
    { MulAction.toPerm g with
      map_rel_iff' := by
        intro x y
        constructor
        · intro h
          simpa using hact g⁻¹ h
        · intro h
          exact hact g h }
  exact (e.degree_eq i).symm

end TauCeti
