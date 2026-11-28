/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.VecNotation

/-!
# Vertex degrees and graph actions

A vertex of degree at least three keeps two distinct neighbours after any single vertex is set
aside. This is the step that grows a branch vertex into a star: the vertex set aside is the
neighbour already used, for instance the next vertex along a path, and the two remaining
neighbours are new leaves.

A pretransitive action preserving adjacency makes all degrees equal when each neighbour
set is finite, without requiring a finite vertex set.

A graph in which every neighbour set has extended cardinality at most `d` has no `(d + 2)`-clique
(`SimpleGraph.cliqueFree_add_two_of_encard_neighborSet_le`), without finiteness or decidability
hypotheses.

A vertex outside a finite set `s` has, among the vertices of `s`, as many neighbours in `G` and in
`Gᶜ` together as `s` has vertices: the degree count behind `SimpleGraph.degree_compl`, relative to
`s`.

## Main results

* `SimpleGraph.degree_eq_of_pretransitive`: a pretransitive graph action preserves degrees.
* `SimpleGraph.exists_adj_adj_ne_of_three_le_degree`: a vertex of degree at least three has two
  distinct neighbours, both different from any given vertex.
* `SimpleGraph.exists_injective_adj_ne_of_three_le_degree`: the same, as an injective
  `Fin 2`-indexed family.
* `SimpleGraph.cliqueFree_add_two_of_encard_neighborSet_le`,
  `SimpleGraph.cliqueFree_add_two_of_degree_le`: bounding all neighbour sets by `d` makes the
  graph `(d + 2)`-clique-free.
* `SimpleGraph.card_filter_adj_add_card_filter_compl_adj`: the neighbours in `s` of a vertex
  outside `s`, in `G` and in `Gᶜ`, number `#s` together.
* `SimpleGraph.IsRegularOfDegree.two_mul_card_edgeFinset`: a `d`-regular graph on `n` vertices has
  `2 e = n d` edges, so for `d ≥ 2` it has at least as many edges as vertices
  (`SimpleGraph.IsRegularOfDegree.card_le_card_edgeFinset`).
-/

public section

namespace SimpleGraph

/-- **Two distinct neighbours of `v` other than a given vertex `x`, from a degree of at least
three.** -/
theorem exists_adj_adj_ne_of_three_le_degree {V : Type*}
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

/-- **Two distinct neighbours of `v` other than a given vertex `x`, indexed by `Fin 2`, from a
degree of at least three.** -/
theorem _root_.SimpleGraph.exists_injective_adj_ne_of_three_le_degree {V : Type*}
    {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)] (hv : 3 ≤ G.degree v) (x : V) :
    ∃ c : Fin 2 → V, Function.Injective c ∧ (∀ i, G.Adj v (c i)) ∧ ∀ i, c i ≠ x := by
  obtain ⟨a, b, ha, hb, hab, hax, hbx⟩ := G.exists_adj_adj_ne_of_three_le_degree hv x
  exact ⟨![a, b], Matrix.injective_pair_iff_ne.mpr hab,
    by simpa [Fin.forall_fin_two] using ⟨ha, hb⟩, by simpa [Fin.forall_fin_two] using ⟨hax, hbx⟩⟩

/-- A pretransitive action preserving adjacency gives equal degrees in a locally finite graph. -/
theorem degree_eq_of_pretransitive
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

/-- A graph in which every neighbour set has extended cardinality at most `d` is
`(d + 2)`-clique-free, without finiteness or decidability hypotheses. -/
theorem cliqueFree_add_two_of_encard_neighborSet_le {V : Type*} {G : SimpleGraph V} {d : ℕ}
    (hdeg : ∀ v, (G.neighborSet v).encard ≤ (d : ℕ∞)) : G.CliqueFree (d + 2) := by
  classical
  intro t ht
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [ht.card_eq]; omega : 0 < t.card)
  have hsub : ((t.erase v : Finset V) : Set V) ⊆ G.neighborSet v := fun w hw ↦ by
    rw [Finset.mem_coe, Finset.mem_erase] at hw
    exact ht.isClique hv hw.2 hw.1.symm
  have hle : ((d + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
    calc ((d + 1 : ℕ) : ℕ∞) = ((t.erase v).card : ℕ∞) := by
          rw [Finset.card_erase_of_mem hv, ht.card_eq]
          rfl
      _ = ((t.erase v : Finset V) : Set V).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
      _ ≤ (G.neighborSet v).encard := Set.encard_le_encard hsub
      _ ≤ (d : ℕ∞) := hdeg v
  exact Nat.not_succ_le_self d (Nat.cast_le.mp hle)

/-- A graph in which every vertex has degree at most `d` is `(d + 2)`-clique-free. -/
theorem cliqueFree_add_two_of_degree_le {V : Type*} {G : SimpleGraph V}
    [∀ v, Fintype (G.neighborSet v)] {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) :
    G.CliqueFree (d + 2) :=
  G.cliqueFree_add_two_of_encard_neighborSet_le fun v ↦ by
    rw [← Set.coe_toFinset (G.neighborSet v), Set.encard_coe_eq_coe_finsetCard,
      Set.toFinset_card, G.card_neighborSet_eq_degree]
    exact Nat.cast_le.mpr (hdeg v)

open Finset in
/-- A vertex `v` outside `s` has `#s` neighbours in `s` in `G` and `Gᶜ` together:
`#{w ∈ s | G.Adj v w} + #{w ∈ s | Gᶜ.Adj v w} = #s`, since `v` is adjacent to each vertex of
`s` in exactly one of `G` and `Gᶜ`. -/
theorem card_filter_adj_add_card_filter_compl_adj {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj] {s : Finset V} {v : V} (hv : v ∉ s) :
    #{w ∈ s | G.Adj v w} + #{w ∈ s | Gᶜ.Adj v w} = #s := by
  rw [← card_filter_add_card_filter_not (s := s) (G.Adj v)]
  congr 2
  refine filter_congr fun w hw ↦ ?_
  simp [compl_adj, show v ≠ w from fun hvw ↦ hv (hvw ▸ hw)]

open Finset in
/-- **The handshake lemma for a regular graph**: a `d`-regular graph on `n` vertices has `e` edges
with `2 e = n d`. -/
theorem IsRegularOfDegree.two_mul_card_edgeFinset {V : Type*} {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] {d : ℕ} (h : G.IsRegularOfDegree d) :
    2 * #G.edgeFinset = Fintype.card V * d := by
  rw [← sum_degrees_eq_twice_card_edges]
  simp [h.degree_eq]

open Finset in
/-- A `d`-regular graph with `d ≥ 2` has at least as many edges as vertices. -/
theorem IsRegularOfDegree.card_le_card_edgeFinset {V : Type*} {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] {d : ℕ} (h : G.IsRegularOfDegree d) (hd : 2 ≤ d) :
    Fintype.card V ≤ #G.edgeFinset := by
  have h₁ := h.two_mul_card_edgeFinset
  have h₂ : Fintype.card V * 2 ≤ Fintype.card V * d := Nat.mul_le_mul_left _ hd
  omega

end SimpleGraph
