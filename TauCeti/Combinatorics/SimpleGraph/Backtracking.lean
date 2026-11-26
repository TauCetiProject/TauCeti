/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Combinatorics.SimpleGraph.Dart.Basic
import TauCeti.Data.List.Chain

/-!
# Walks without backtracking in a simple graph

A walk in a simple graph backtracks when it traverses a dart and then immediately the reverse
dart. Since consecutive darts of a walk share a vertex, this happens exactly when two consecutive
edges of the walk coincide. A trail (a walk without repeated edges) never backtracks, and in an
acyclic graph the walks without backtracking are exactly the paths.

A closed walk is a non-backtracking cycle when it does not backtrack even across its closing step,
from its last dart back to its first. These are the closed walks counted by the Ihara zeta function
of a graph and by the traces of the powers of its Hashimoto matrix.

## Main definitions

* `SimpleGraph.NonBacktrackingDartAdj`: two darts can be consecutive in a walk that does not
  backtrack.
* `SimpleGraph.Walk.IsNonBacktrackingCycle`: a closed walk none of whose darts is followed by its
  reverse, the last dart being followed by the first.

## Main results

* `SimpleGraph.Walk.isChain_ne_edges_iff`: no two consecutive edges of a walk coincide exactly
  when no dart of the walk is followed by its reverse.
* `SimpleGraph.Walk.IsTrail.isChain_ne_symm_darts`: a trail does not backtrack.
* `SimpleGraph.IsAcyclic.isPath_iff_isChain_darts`: in an acyclic graph a walk is a path exactly
  when it does not backtrack.
* `SimpleGraph.Walk.isNonBacktrackingCycle_iff`: a closed walk is a non-backtracking cycle exactly
  when it does not backtrack and its first dart is not the reverse of its last one.
* `SimpleGraph.Walk.isNonBacktrackingCycle_iff_chain`: equivalently, its darts form a chain as a
  cycle (`Cycle.Chain`).

## References

* A. Terras, *Zeta Functions of Graphs: A Stroll through the Garden*, Cambridge Studies in Advanced
  Mathematics 128, Cambridge University Press, 2011.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

variable (G) in
/-- Two darts are *non-backtracking adjacent* when they can be consecutive darts of a walk that
does not backtrack: the first ends where the second starts, and the second is not the reverse of
the first. -/
abbrev NonBacktrackingDartAdj (d d' : G.Dart) : Prop :=
  d.snd = d'.fst ∧ d' ≠ d.symm

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

/-- A closed walk is a *non-backtracking cycle* when none of its darts is followed by its reverse,
including across the closing step: no dart of `p.darts ++ p.darts.take 1` is followed by its
reverse. In Terras's terms it is a closed path without backtracking and without tail. The walk of
length zero is one vacuously. -/
def IsNonBacktrackingCycle {u : V} (p : G.Walk u u) : Prop :=
  (p.darts ++ p.darts.take 1).IsChain fun d d' => d' ≠ d.symm

@[simp]
theorem isNonBacktrackingCycle_nil {u : V} : (nil : G.Walk u u).IsNonBacktrackingCycle := by
  simp [IsNonBacktrackingCycle]

/-- A closed walk is a non-backtracking cycle exactly when it does not backtrack and, unless it is
the walk of length zero, its first dart is not the reverse of its last one (it has no tail). -/
theorem isNonBacktrackingCycle_iff {u : V} (p : G.Walk u u) :
    p.IsNonBacktrackingCycle ↔ p.darts.IsChain (fun d d' => d' ≠ d.symm) ∧
      ∀ hp : ¬p.Nil, p.firstDart hp ≠ (p.lastDart hp).symm := by
  rw [IsNonBacktrackingCycle, List.isChain_append_take_one_iff]
  simp

/-- A closed walk is a non-backtracking cycle exactly when its darts form a chain as a cycle for
the relation of not being followed by the reverse. -/
theorem isNonBacktrackingCycle_iff_chain {u : V} (p : G.Walk u u) :
    p.IsNonBacktrackingCycle ↔ Cycle.Chain (fun d d' => d' ≠ d.symm) (p.darts : Cycle G.Dart) := by
  rw [IsNonBacktrackingCycle]
  cases p.darts with
  | nil => simp
  | cons d l => simp [Cycle.chain_coe_cons]

/-- A closed walk is a non-backtracking cycle exactly when its darts, followed by its first dart
again, form a chain of non-backtracking adjacent darts. -/
theorem isNonBacktrackingCycle_iff_isChain {u : V} (p : G.Walk u u) :
    p.IsNonBacktrackingCycle ↔
      (p.darts ++ p.darts.take 1).IsChain G.NonBacktrackingDartAdj := by
  refine ⟨fun h => ?_, fun h => h.imp fun _ _ h => h.2⟩
  have hadj : (p.darts ++ p.darts.take 1).IsChain G.DartAdj :=
    List.isChain_append_take_one_iff.mpr ⟨p.isChain_dartAdj_darts, fun _ => by simp [DartAdj]⟩
  rw [IsNonBacktrackingCycle, List.isChain_iff_forall_rel_of_append_cons_cons] at h
  rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hadj ⊢
  exact fun _ _ _ _ hl => ⟨hadj hl, h hl⟩

end Walk

/-- In an acyclic graph, a walk is a path exactly when none of its darts is followed by its
reverse. -/
theorem IsAcyclic.isPath_iff_isChain_darts (hG : G.IsAcyclic) {u v : V} (p : G.Walk u v) :
    p.IsPath ↔ p.darts.IsChain fun d d' => d' ≠ d.symm :=
  (hG.isPath_iff_isChain p).trans p.isChain_ne_edges_iff

end SimpleGraph
