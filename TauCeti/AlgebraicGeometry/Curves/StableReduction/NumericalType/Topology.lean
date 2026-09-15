/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Basic
import Mathlib.Tactic.Linarith

/-!
# The topological genus of a numerical type

The intersection matrix of a numerical type determines a finite simple graph: its vertices are
the components, and two distinct vertices are joined when the corresponding components meet.  This
file records the first Betti number of that connected graph,

`g_top = 1 - #components + #edges`,

and proves the elementary graph-theoretic facts needed when comparing it with the arithmetic genus.
The graph is connected by the defining connectedness condition of a numerical type, so its
topological genus is nonnegative; it vanishes exactly when the intersection graph is a tree.

The definition uses `Nat.card` for the finite edge type.  This avoids making the combinatorial
invariant depend on a chosen finite-type instance for the unordered pairs of components.

The terminology is that of the Stacks Project, Section 55.3, especially Lemma 55.3.10.  The
result here supplies the graph-theoretic input for the comparison with arithmetic genus in Lemma
55.3.14.
-/

public section

namespace TauCeti

namespace NumericalType

universe u

variable (T : NumericalType.{u})

/-! ### The intersection graph -/

/-- The simple graph joining distinct components with positive intersection number. -/
def intersectionGraph : SimpleGraph T.Component :=
  SimpleGraph.fromRel T.Adj

@[simp]
lemma intersectionGraph_adj_iff {i j : T.Component} :
    T.intersectionGraph.Adj i j ↔ T.Adj i j := by
  rw [intersectionGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hij, h | h⟩
    · rw [T.adj_iff] at h ⊢
      exact h
    · rw [T.adj_iff] at h
      rw [T.adj_iff]
      exact ⟨hij, by simpa [T.intersection_comm] using h.2⟩
  · intro h
    rw [T.adj_iff] at h
    exact ⟨h.1, Or.inl ((T.adj_iff).mpr h)⟩

/-- The intersection graph of a numerical type is connected. -/
lemma intersectionGraph_connected : T.intersectionGraph.Connected := by
  obtain ⟨i⟩ := T.componentNonempty
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨i, ?_⟩
  intro j
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction T.reflTransGen_adj i j with
  | refl => exact .refl
  | tail hab hbc ih => exact ih.tail ((intersectionGraph_adj_iff T).mpr hbc)

/-! ### Topological genus -/

/-- The topological genus of the intersection graph of a numerical type.

For a connected dual graph this is its first Betti number.  The edge type is the finite type of
unordered pairs of distinct components that are adjacent in `intersectionGraph`. -/
noncomputable def topologicalGenus : ℤ :=
  1 - (Nat.card T.Component : ℤ) + (T.intersectionGraph.edgeSet.ncard : ℤ)

/-- The topological genus of a numerical type is nonnegative. -/
theorem topologicalGenus_nonneg : 0 ≤ T.topologicalGenus := by
  have hcard := T.intersectionGraph_connected.card_vert_le_card_edgeSet_add_one
  have hcard' : Nat.card T.Component ≤ T.intersectionGraph.edgeSet.ncard + 1 := by
    simpa only [Nat.card_coe_set_eq] using hcard
  dsimp [topologicalGenus]
  have hcard'' : (Nat.card T.Component : ℤ) ≤
      (T.intersectionGraph.edgeSet.ncard : ℤ) + 1 := by
    exact_mod_cast hcard'
  omega

/-- The topological genus vanishes exactly when the intersection graph is a tree. -/
theorem topologicalGenus_eq_zero_iff :
    T.topologicalGenus = 0 ↔ T.intersectionGraph.IsTree := by
  have hconn := T.intersectionGraph_connected
  constructor
  · intro hz
    apply (SimpleGraph.isTree_iff_connected_and_card).2
    refine ⟨hconn, ?_⟩
    have hz' : (T.intersectionGraph.edgeSet.ncard : ℤ) + 1 =
        (Nat.card T.Component : ℤ) := by
      dsimp [topologicalGenus] at hz
      linarith
    exact_mod_cast hz'
  · intro htree
    have hcard := (SimpleGraph.isTree_iff_connected_and_card.mp htree).2
    have hcard' : (T.intersectionGraph.edgeSet.ncard : ℤ) + 1 =
        (Nat.card T.Component : ℤ) := by
      have hcardNat : T.intersectionGraph.edgeSet.ncard + 1 = Nat.card T.Component := by
        simpa only [Nat.card_coe_set_eq] using hcard
      exact_mod_cast hcardNat
    dsimp [topologicalGenus]
    omega

end NumericalType

end TauCeti
