/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Darts of a simple graph

The darts of a simple graph with tail `u` correspond to the neighbours of `u`: a dart is sent to
its head, and a neighbour `w` to the dart `u → w` (`SimpleGraph.dartOfNeighborSet`).

Each edge `s(x, y)` of a finite graph carries exactly the two darts `x → y` and `y → x`, so a sum
over the darts, or over the ordered adjacent pairs, is a sum over the edges of the symmetrized
summand. This turns quadratic forms of graph matrices into sums over edges.

## Main definitions

* `SimpleGraph.dartFstEquivNeighborSet`: the equivalence between the darts with tail `u` and the
  neighbour set of `u`.

## Main results

* `SimpleGraph.sum_dart_snd_eq_sum_neighborSet`: a sum over the darts with head `v` is a sum over
  the neighbours of `v`.
* `SimpleGraph.sum_dart_eq_sum_edgeFinset`: a sum of `f d.fst d.snd` over the darts is the sum of
  `f x y + f y x` over the edges `s(x, y)`.
* `SimpleGraph.sum_sum_ite_adj_eq_sum_edgeFinset`: the same for the double sum of `f i j` over the
  ordered adjacent pairs.
* `SimpleGraph.Dart.ne_symm`: no dart is its own reversal.
* `SimpleGraph.Dart.eq_symm_comm`: `a` is the reversal of `b` exactly when `b` is the reversal
  of `a`.
* `SimpleGraph.DartAdj.edge_ne_iff`: two consecutive darts have different edges exactly when the
  second is not the reverse of the first.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The darts with tail `u` are the neighbours of `u`: a dart is sent to its head. -/
def dartFstEquivNeighborSet (u : V) :
    {d : G.Dart // d.fst = u} ≃ G.neighborSet u where
  toFun d := ⟨d.val.snd, (G.mem_neighborSet _ _).2 (Eq.mp (congrArg (G.Adj · d.val.snd) d.property)
      d.val.adj)⟩
  invFun w := ⟨G.dartOfNeighborSet u w, rfl⟩
  left_inv d := by
    obtain ⟨⟨⟨a, b⟩, h⟩, rfl⟩ := d
    rfl
  right_inv _ := rfl

/-- The neighbour attached to a dart with tail `u` is its head. -/
@[simp]
theorem coe_dartFstEquivNeighborSet_apply (u : V)
    (d : {d : G.Dart // d.fst = u}) :
    (G.dartFstEquivNeighborSet u d : V) = d.val.snd :=
  rfl

/-- The dart attached to a neighbour `w` of `u` is the dart `u → w`. -/
@[simp]
theorem coe_dartFstEquivNeighborSet_symm_apply (u : V) (w : G.neighborSet u) :
    ((G.dartFstEquivNeighborSet u).symm w : G.Dart) = G.dartOfNeighborSet u w :=
  rfl

/-- A sum over the darts with head `v` is a sum over the neighbours `w` of `v`, through the
reverse `w → v` of the dart `v → w`. -/
theorem sum_dart_snd_eq_sum_neighborSet {M : Type*} [AddCommMonoid M] [Fintype G.Dart]
    [DecidableEq V] (v : V) [Fintype (G.neighborSet v)] (f : G.Dart → M) :
    ∑ d : G.Dart with d.snd = v, f d = ∑ w : G.neighborSet v, f (G.dartOfNeighborSet v w).symm :=
  Finset.sum_bij'
    (fun d hd ↦ ⟨d.fst, (G.mem_neighborSet _ _).2 ((Finset.mem_filter.1 hd).2 ▸ d.adj.symm)⟩)
    (fun w _ ↦ (G.dartOfNeighborSet v w).symm) (fun _ _ ↦ Finset.mem_univ _) (fun _ _ ↦ by simp)
    (fun d hd ↦ Dart.ext _ _ (Prod.ext rfl (Finset.mem_filter.1 hd).2.symm)) (fun _ _ ↦ rfl)
    (fun d hd ↦ congrArg f (Dart.ext _ _ (Prod.ext rfl (Finset.mem_filter.1 hd).2)))

/-- No dart is its own reversal. -/
@[simp]
theorem Dart.ne_symm (a : G.Dart) : a ≠ a.symm :=
  (Dart.symm_ne a).symm

/-- A dart is the reversal of another exactly when the other is the reversal of the first. -/
theorem Dart.eq_symm_comm {a b : G.Dart} : a = b.symm ↔ b = a.symm :=
  Dart.symm_involutive.eq_iff.symm.trans eq_comm

/-- Two consecutive darts have different edges exactly when the second is not the reverse of the
first. -/
theorem DartAdj.edge_ne_iff {d d' : G.Dart} (h : G.DartAdj d d') :
    d.edge ≠ d'.edge ↔ d' ≠ d.symm := by
  have := d.adj.ne
  rw [Ne, dart_edge_eq_iff]
  unfold DartAdj at h
  grind [Dart.symm_symm]

section Fintype

variable [Fintype V] [DecidableRel G.Adj]

variable (G) in
/-- A sum of `f d.fst d.snd` over the darts of `G` is the sum of `f x y + f y x` over the edges
`s(x, y)` of `G`: the darts over an edge are its two orientations. -/
theorem sum_dart_eq_sum_edgeFinset {M : Type*} [AddCommMonoid M] (f : V → V → M) :
    ∑ d : G.Dart, f d.fst d.snd =
      ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun x y ↦ f x y + f y x, fun _ _ ↦ add_comm _ _⟩ e := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := Dart.edge) (t := G.edgeFinset)
    fun d _ ↦ mem_edgeFinset.2 d.edge_mem]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  induction e using Sym2.ind with | _ x y =>
  let d : G.Dart := ⟨(x, y), mem_edgeFinset.1 he⟩
  rw [show s(x, y) = d.edge from rfl, d.edge_fiber, Finset.sum_pair d.ne_symm]
  rfl

variable (G) in
/-- The double sum of `f i j` over the ordered pairs of adjacent vertices is the sum of
`f x y + f y x` over the edges `s(x, y)` of `G`. -/
theorem sum_sum_ite_adj_eq_sum_edgeFinset {M : Type*} [AddCommMonoid M] (f : V → V → M) :
    ∑ i, ∑ j, (if G.Adj i j then f i j else 0) =
      ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun x y ↦ f x y + f y x, fun _ _ ↦ add_comm _ _⟩ e := by
  rw [← G.sum_dart_eq_sum_edgeFinset, ← Fintype.sum_prod_type', ← Finset.sum_filter]
  exact Finset.sum_bij' (fun p hp ↦ ⟨p, (Finset.mem_filter.1 hp).2⟩) (fun d _ ↦ d.toProd)
    (fun _ _ ↦ Finset.mem_univ _) (fun d _ ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, d.adj⟩)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end Fintype

end SimpleGraph
