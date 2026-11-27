/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Interval
import Mathlib.Data.Set.Finite.Lattice
import TauCeti.Combinatorics.SimpleGraph.Basic

/-!
# Finite simple graphs

A nonempty graph with finitely many edges has an edge minimizing any linearly ordered weight.

On a finite vertex set, `G ↦ G.edgeFinset` maps the graphs between `F` and `H` bijectively onto
the finsets of pairs between `F.edgeFinset` and `H.edgeFinset`. Consequently a product or sum over
an interval of graphs, of a factor that depends on the graph only through its edge set, is one over
an interval of the Boolean lattice `Finset (Sym2 V)`, where the finset interval API applies.

## Main results

* `SimpleGraph.neighborSetFintypeOfFinite` — a `Fintype` structure on the neighbour sets of a graph
  on a finite vertex type, for local selection where decidable adjacency is unavailable.
* `SimpleGraph.exists_minimum_weight_edge` — a finite nonempty edge set has a minimum-weight edge.
* `SimpleGraph.Iso.sum_neighborFinset_comp` — neighbour sums commute with graph isomorphisms.
* `SimpleGraph.sum_neighborFinset_comm` — swapping the order of summation in a double sum over
  neighbours.
* `SimpleGraph.finite_setOf_exists_mem_and_mem` — in a locally finite graph only finitely many
  edges share a vertex with an edge of a finite set of edges.
* `SimpleGraph.edgeSet_fromEdgeSet_of_subset` — a set of edges of `G` is the edge set of the
  graph it generates.
* `SimpleGraph.edgeFinset_symmDiff` — the edge finset of `G₁ ∆ G₂` is
  `G₁.edgeFinset ∆ G₂.edgeFinset`.
* `SimpleGraph.prod_filter_le_le_eq_prod_Icc_edgeFinset` and its additive version
  `SimpleGraph.sum_filter_le_le_eq_sum_Icc_edgeFinset` — a product (sum) over the graphs between
  `F` and `H` of a function of their edge finsets is the product (sum) of that function over
  `Finset.Icc F.edgeFinset H.edgeFinset`.
-/

public section

open Finset
open scoped symmDiff

namespace SimpleGraph

variable {V K M : Type*}

/-- The neighbour sets of a graph on a finite vertex type are finite, from finiteness alone. This
is not an instance: with `DecidableRel G.Adj`, instance search finds the subtype `Fintype`
(`Subtype.fintype`), and the two structures are not definitionally equal. Files that need a
`Fintype` on neighbour sets without decidable adjacency select it as a local instance. It is
exposed because it is instance-reducible: statements elaborated with it as a local instance
record the unfolded `Fintype.ofFinite`, and importers must see the body to match them. -/
@[instance_reducible, expose]
noncomputable def neighborSetFintypeOfFinite [Finite V] (G : SimpleGraph V) (v : V) :
    Fintype (G.neighborSet v) :=
  Fintype.ofFinite _

/-- A graph with a finite nonempty edge set has an edge of minimum weight. -/
theorem exists_minimum_weight_edge (G : SimpleGraph V) [Finite G.edgeSet] (hG : G ≠ ⊥)
    [LinearOrder K] (w : Sym2 V → K) :
    ∃ u v, G.Adj u v ∧ ∀ e ∈ G.edgeSet, w s(u, v) ≤ w e := by
  let _ := Fintype.ofFinite G.edgeSet
  obtain ⟨e, he, hmin⟩ := G.edgeFinset.exists_min_image w (edgeFinset_nonempty.2 hG)
  induction e using Sym2.inductionOn with
  | _ u v =>
    exact ⟨u, v, G.mem_edgeSet.1 (mem_edgeFinset.1 he), fun e he' ↦ hmin e (mem_edgeFinset.2 he')⟩

/-- Summing a pulled-back function over neighbours commutes with a graph isomorphism. -/
theorem Iso.sum_neighborFinset_comp {W R : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] [AddCommMonoid R]
    (e : G ≃g H) (i : V) (a : W → R) :
    ∑ j ∈ G.neighborFinset i, a (e j) = ∑ j ∈ H.neighborFinset (e i), a j := by
  exact Finset.sum_equiv e.toEquiv
    (fun j ↦ by
      simpa only [mem_neighborFinset, RelIso.coe_fn_toEquiv] using e.map_adj_iff.symm)
    (fun _ _ ↦ by rw [RelIso.coe_fn_toEquiv])

/-- **A sum over the oriented edges can be read from either endpoint.** Adjacency is symmetric, so
summing `F i j` over the neighbours `j` of each vertex `i` is summing it over the neighbours `i`
of each vertex `j`. -/
theorem sum_neighborFinset_comm (G : SimpleGraph V) [Fintype V] [G.LocallyFinite]
    [AddCommMonoid M] (F : V → V → M) :
    ∑ i, ∑ j ∈ G.neighborFinset i, F i j = ∑ j, ∑ i ∈ G.neighborFinset j, F i j :=
  sum_comm' fun i j ↦ by
    simp only [mem_univ, true_and, and_true, mem_neighborFinset]
    exact ⟨Adj.symm, Adj.symm⟩

/-- For a locally finite graph, only finitely many edges share a vertex with an edge of a finite
set `F`. -/
theorem finite_setOf_exists_mem_and_mem (G : SimpleGraph V) [G.LocallyFinite]
    (F : Finset G.edgeSet) :
    {e : G.edgeSet | ∃ f ∈ F, ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)}.Finite := by
  classical
  have hv (v : V) : {e : G.edgeSet | v ∈ (e : Sym2 V)}.Finite :=
    Set.Finite.of_finite_image (f := fun e => (e : Sym2 V))
      ((G.incidenceSet v).toFinite.subset fun _ ⟨e, he, hee⟩ => hee ▸ ⟨e.property, he⟩)
      Subtype.val_injective.injOn
  refine ((F.finite_toSet.biUnion fun f _ => (f : Sym2 V).toFinset.finite_toSet.biUnion
    fun v _ => hv v)).subset ?_
  rintro e ⟨f, hf, v, hve, hvf⟩
  simp only [Set.mem_iUnion]
  exact ⟨f, hf, v, by simpa using hvf, hve⟩

/-- A set of pairs contained in the edges of a graph `G` carries no diagonal pair, so it is the
edge set of the graph it generates. -/
theorem edgeSet_fromEdgeSet_of_subset {G : SimpleGraph V} {s : Set (Sym2 V)}
    (hs : s ⊆ G.edgeSet) : (fromEdgeSet s).edgeSet = s := by
  rw [edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
  exact fun e he ↦ not_isDiag_of_mem_edgeSet G (hs he)

/-- The edge finset of `G₁ ∆ G₂` is the symmetric difference of their edge finsets. -/
@[simp]
theorem edgeFinset_symmDiff {G₁ G₂ : SimpleGraph V} [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    [Fintype (edgeSet (G₁ ∆ G₂))] [DecidableEq V] :
    (G₁ ∆ G₂).edgeFinset = G₁.edgeFinset ∆ G₂.edgeFinset := by
  ext e
  simp only [mem_edgeFinset, edgeSet_symmDiff, Finset.mem_symmDiff, Set.mem_symmDiff]

variable [Fintype V] [DecidableEq V] [CommMonoid M]

/-- Multiplying a function of the edge finset over the graphs between `F` and `H` is multiplying
it over the edge finsets between theirs. -/
@[to_additive /-- Summing a function of the edge finset over the graphs between `F` and `H` is
summing it over the edge finsets between theirs. -/]
theorem prod_filter_le_le_eq_prod_Icc_edgeFinset (F H : SimpleGraph V)
    [DecidablePred fun G : SimpleGraph V ↦ F ≤ G ∧ G ≤ H]
    [∀ G : SimpleGraph V, Fintype G.edgeSet] (f : Finset (Sym2 V) → M) :
    ∏ G with F ≤ G ∧ G ≤ H, f G.edgeFinset = ∏ s ∈ Icc F.edgeFinset H.edgeFinset, f s := by
  -- An edge set below `H.edgeFinset` carries no diagonal pair, so it is the edge set of a graph.
  have hset : ∀ s ∈ Icc F.edgeFinset H.edgeFinset,
      (fromEdgeSet (s : Set (Sym2 V))).edgeFinset = s := fun s hs ↦ coe_injective <| by
    rw [coe_edgeFinset, edgeSet_fromEdgeSet_of_subset fun e he ↦
      mem_edgeFinset.1 ((mem_Icc.1 hs).2 (mem_coe.1 he))]
  refine prod_nbij' (fun G ↦ G.edgeFinset) (fun s ↦ fromEdgeSet (s : Set (Sym2 V)))
    (fun G hG ↦ ?_) (fun s hs ↦ ?_) (fun G _ ↦ ?_) hset (fun G _ ↦ rfl)
  · simpa [edgeFinset_subset_edgeFinset] using hG
  · refine mem_coe.2 ((mem_filter_univ _).2 ?_)
    rw [← edgeFinset_subset_edgeFinset, ← edgeFinset_subset_edgeFinset, hset s hs]
    exact mem_Icc.1 hs
  · rw [coe_edgeFinset, fromEdgeSet_edgeSet]

end SimpleGraph
