/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Interval

/-!
# Finite simple graphs

A nonempty graph with finitely many edges has an edge minimizing any linearly ordered weight.

On a finite vertex set, `G ↦ G.edgeFinset` maps the graphs between `F` and `H` bijectively onto
the finsets of pairs between `F.edgeFinset` and `H.edgeFinset`. Consequently a sum over an interval
of graphs, of a summand that depends on the graph only through its edge set, is a sum over an
interval of the Boolean lattice `Finset (Sym2 V)`, where the finset interval API applies.

## Main results

* `SimpleGraph.exists_minimum_weight_edge` — a finite nonempty edge set has a minimum-weight edge.
* `SimpleGraph.sum_filter_le_le_eq_sum_Icc_edgeFinset` — a sum over the graphs between `F` and `H`
  of a function of their edge finsets is the sum of that function over
  `Finset.Icc F.edgeFinset H.edgeFinset`.
-/

public section

open Finset

namespace SimpleGraph

variable {V K : Type*}

/-- A graph with a finite nonempty edge set has an edge of minimum weight. -/
theorem exists_minimum_weight_edge (G : SimpleGraph V) [Finite G.edgeSet] (hG : G ≠ ⊥)
    [LinearOrder K] (w : Sym2 V → K) :
    ∃ u v, G.Adj u v ∧ ∀ e ∈ G.edgeSet, w s(u, v) ≤ w e := by
  classical
  let _ := Fintype.ofFinite G.edgeSet
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image G.edgeFinset w
    (SimpleGraph.edgeFinset_nonempty.mpr hG)
  induction e using Sym2.inductionOn with
  | _ u v =>
      refine ⟨u, v, ?_, fun e he' ↦ hmin e ?_⟩
      · rw [← SimpleGraph.mem_edgeSet]
        simpa only [SimpleGraph.mem_edgeFinset] using he
      · simpa only [SimpleGraph.mem_edgeFinset] using he'

variable {V M : Type*} [Fintype V] [DecidableEq V] [AddCommMonoid M]

/-- Summing a function of the edge finset over the graphs between `F` and `H` is summing it over
the edge finsets between theirs. -/
theorem sum_filter_le_le_eq_sum_Icc_edgeFinset (F H : SimpleGraph V)
    [DecidablePred fun G : SimpleGraph V => F ≤ G ∧ G ≤ H]
    [∀ G : SimpleGraph V, Fintype G.edgeSet] (f : Finset (Sym2 V) → M) :
    ∑ G with F ≤ G ∧ G ≤ H, f G.edgeFinset = ∑ s ∈ Icc F.edgeFinset H.edgeFinset, f s := by
  -- An edge set below `H.edgeFinset` carries no diagonal pair, so it is the edge set of a graph.
  have hset : ∀ s ∈ Icc F.edgeFinset H.edgeFinset,
      (fromEdgeSet (s : Set (Sym2 V))).edgeFinset = s := fun s hs => coe_injective <| by
    rw [coe_edgeFinset, edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
    exact fun e he => not_isDiag_of_mem_edgeSet H (mem_edgeFinset.1 ((mem_Icc.1 hs).2 he))
  refine sum_nbij' (fun G => G.edgeFinset) (fun s => fromEdgeSet (s : Set (Sym2 V)))
    (fun G hG => ?_) (fun s hs => ?_) (fun G _ => ?_) hset (fun G _ => rfl)
  · simpa [edgeFinset_subset_edgeFinset] using hG
  · refine mem_coe.2 ((mem_filter_univ _).2 ?_)
    rw [← edgeFinset_subset_edgeFinset, ← edgeFinset_subset_edgeFinset, hset s hs]
    exact mem_Icc.1 hs
  · rw [coe_edgeFinset, fromEdgeSet_edgeSet]

end SimpleGraph
