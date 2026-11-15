/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Combinatorics.SimpleGraph.Dart

/-!
# Walks without backtracking in a simple graph

A walk in a simple graph backtracks when it traverses a dart and then immediately the reverse
dart. Since consecutive darts of a walk share a vertex, this happens exactly when two consecutive
edges of the walk coincide. A trail (a walk without repeated edges) never backtracks, and in an
acyclic graph the walks without backtracking are exactly the paths.

## Main results

* `SimpleGraph.Walk.isChain_ne_edges_iff`: no two consecutive edges of a walk coincide exactly
  when no dart of the walk is followed by its reverse.
* `SimpleGraph.Walk.IsTrail.isChain_ne_symm_darts`: a trail does not backtrack.
* `SimpleGraph.Walk.IsTrail.darts_nodup` and `SimpleGraph.Walk.IsTrail.symm_notMem_darts`: a trail
  repeats no dart and never traverses both a dart and its reverse.
* `SimpleGraph.IsAcyclic.isPath_iff_isChain_darts`: in an acyclic graph a walk is a path exactly
  when it does not backtrack.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace Walk

/-- No two consecutive edges of a walk coincide exactly when no dart of the walk is followed by
its reverse. -/
theorem isChain_ne_edges_iff {u v : V} (p : G.Walk u v) :
    p.edges.IsChain (· ≠ ·) ↔ p.darts.IsChain fun d d' => d' ≠ d.symm := by
  induction p with
  | nil => simp
  | cons h p ih =>
    cases p with
    | nil => simp
    | cons h' q =>
      simp only [edges_cons, darts_cons, List.isChain_cons_cons] at ih ⊢
      exact and_congr (DartAdj.edge_ne_iff (d := ⟨(_, _), h⟩) (d' := ⟨(_, _), h'⟩) rfl) ih

/-- A trail does not backtrack: none of its darts is followed by its reverse. -/
theorem IsTrail.isChain_ne_symm_darts {u v : V} {p : G.Walk u v} (hp : p.IsTrail) :
    p.darts.IsChain fun d d' => d' ≠ d.symm :=
  p.isChain_ne_edges_iff.mp hp.edges_nodup.isChain

/-- A trail traverses no dart more than once. -/
theorem IsTrail.darts_nodup {u v : V} {p : G.Walk u v} (hp : p.IsTrail) : p.darts.Nodup :=
  hp.edges_nodup.of_map Dart.edge

/-- A trail never traverses both a dart and its reverse. -/
theorem IsTrail.symm_notMem_darts {u v : V} {p : G.Walk u v} (hp : p.IsTrail) {d : G.Dart}
    (hd : d ∈ p.darts) : d.symm ∉ p.darts := fun hds =>
  d.symm_ne ((List.nodup_map_iff_inj_on hp.darts_nodup).mp hp.edges_nodup
    d.symm hds d hd (Dart.edge_symm d))

end Walk

/-- In an acyclic graph, a walk is a path exactly when none of its darts is followed by its
reverse. -/
theorem IsAcyclic.isPath_iff_isChain_darts (hG : G.IsAcyclic) {u v : V} (p : G.Walk u v) :
    p.IsPath ↔ p.darts.IsChain fun d d' => d' ≠ d.symm :=
  (hG.isPath_iff_isChain p).trans p.isChain_ne_edges_iff

end SimpleGraph
