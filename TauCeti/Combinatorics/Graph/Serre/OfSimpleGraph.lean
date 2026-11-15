/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Tree
public import TauCeti.Combinatorics.SimpleGraph.Backtracking

/-!
# Connectivity and trees of the Serre graph of a simple graph

The Serre graph `G.toSerreGraph` of a simple graph `G` has the darts of `G` as its directed
edges. A walk of `G` and a path of `G.toSerreGraph` are both a composable sequence of darts, and
this file identifies them: `SimpleGraph.Walk.toSerrePath` and `SimpleGraph.serrePathToWalk` are
mutually inverse and preserve the dart sequence, concatenation and reversal.

Under this identification a Serre path is reduced exactly when the walk never traverses a dart
and then its reverse. Every trail of `G` (a walk without repeated edges), in particular every
path, is such a walk, and in an acyclic graph the paths are the only ones. Hence connectedness,
acyclicity and the tree property of `G.toSerreGraph` in the sense of Serre agree with the
corresponding notions for `G`; for connectedness and trees both sides require a vertex.

## Main declarations

* `SimpleGraph.Walk.serrePathEquiv`: walks of `G` are the paths of `G.toSerreGraph`.
* `SimpleGraph.Walk.isReduced_toSerrePath_iff`: the Serre path of a walk is reduced exactly when
  the walk does not backtrack.
* `SimpleGraph.IsAcyclic.isReduced_toSerrePath_iff`: in an acyclic graph, the Serre path of a walk
  is reduced exactly when the walk is a path.
* `SimpleGraph.preconnected_toSerreGraph_iff`, `SimpleGraph.connected_toSerreGraph_iff`:
  `G.toSerreGraph` is (pre)connected exactly when `G` is.
* `SimpleGraph.isAcyclic_toSerreGraph_iff`, `SimpleGraph.isTree_toSerreGraph_iff`:
  `G.toSerreGraph` is acyclic, respectively a tree, exactly when `G` is.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1 (Definition 1) and §2.2.
* I. Kapovich, R. Weidmann and A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, §2, Convention 2.1 (reduced edge-paths).
-/

public section

universe u

namespace SimpleGraph

open TauCeti TauCeti.SerreGraph

variable {V : Type u} (G : SimpleGraph V)

/-- The arrow of the Serre graph of `G` from `u` to `v` given by an adjacency of `u` and `v`:
the dart `(u, v)`. -/
def toSerreGraphArrow {u v : V} (h : G.Adj u v) :
    @Quiver.Hom G.toSerreGraph.V G.toSerreGraph.toQuiver u v :=
  ⟨⟨(u, v), h⟩, rfl, G.toSerreGraph_tgt _⟩

@[simp] theorem toSerreGraphArrow_val {u v : V} (h : G.Adj u v) :
    (G.toSerreGraphArrow h).1 = ⟨(u, v), h⟩ := (rfl)

/-- The ends of an arrow of the Serre graph of `G` are adjacent. -/
theorem adj_of_toSerreGraph_hom {u v : V}
    (e : @Quiver.Hom G.toSerreGraph.V G.toSerreGraph.toQuiver u v) : G.Adj u v := by
  obtain ⟨d, rfl, rfl⟩ := e
  exact d.adj

/-- An arrow of the Serre graph of `G` is the arrow of the adjacency of its ends. -/
theorem toSerreGraphArrow_adj_of_toSerreGraph_hom {u v : V}
    (e : @Quiver.Hom G.toSerreGraph.V G.toSerreGraph.toQuiver u v) :
    G.toSerreGraphArrow (G.adj_of_toSerreGraph_hom e) = e := by
  obtain ⟨d, rfl, rfl⟩ := e
  rfl

/-- Reversing the arrow of an adjacency gives the arrow of the symmetric adjacency. -/
@[simp] theorem reverse_toSerreGraphArrow {u v : V} (h : G.Adj u v) :
    Quiver.reverse (G.toSerreGraphArrow h) = G.toSerreGraphArrow h.symm :=
  Subtype.ext ((G.toSerreGraph.reverse_val _).trans rfl)

namespace Walk

variable {G}

/-- A walk of a simple graph as a path of its Serre graph, traversing the same darts. -/
def toSerrePath {u : V} : ∀ {v : V}, G.Walk u v → G.toSerreGraph.Path u v
  | _, .nil => .nil
  | _, .cons h p => (G.toSerreGraphArrow h).toPath.comp p.toSerrePath

@[simp] theorem toSerrePath_nil (u : V) :
    (Walk.nil : G.Walk u u).toSerrePath = Quiver.Path.nil := (rfl)

@[simp] theorem toSerrePath_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (Walk.cons h p).toSerrePath = (G.toSerreGraphArrow h).toPath.comp p.toSerrePath := (rfl)

/-- The Serre path of a walk traverses the darts of the walk. -/
@[simp] theorem darts_toSerrePath {u v : V} (p : G.Walk u v) :
    Path.darts G.toSerreGraph p.toSerrePath = p.darts := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih]

/-- The Serre path of a walk has the length of the walk. -/
@[simp] theorem length_toSerrePath {u v : V} (p : G.Walk u v) :
    p.toSerrePath.length = p.length := by
  rw [← Path.length_darts G.toSerreGraph, darts_toSerrePath, length_darts]

/-- Concatenation of walks corresponds to path composition. -/
@[simp] theorem toSerrePath_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).toSerrePath = p.toSerrePath.comp q.toSerrePath := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, Quiver.Path.comp_assoc]

/-- Appending an edge to a walk appends its arrow to the Serre path. -/
@[simp] theorem toSerrePath_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).toSerrePath = p.toSerrePath.cons (G.toSerreGraphArrow h) := by
  simp [concat_eq_append, Quiver.Hom.toPath]

/-- Reversal of walks corresponds to path reversal. -/
@[simp] theorem toSerrePath_reverse {u v : V} (p : G.Walk u v) :
    p.reverse.toSerrePath = p.toSerrePath.reverse := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih]

/-- The Serre path of a walk is reduced exactly when no dart of the walk is followed by its
reverse. -/
theorem isReduced_toSerrePath_iff {u v : V} (p : G.Walk u v) :
    Path.IsReduced G.toSerreGraph p.toSerrePath ↔ p.darts.IsChain fun d d' => d' ≠ d.symm := by
  rw [Path.isReduced_iff_isChain, darts_toSerrePath]
  -- The reversal of the Serre graph is `Dart.symm` by definition.
  rfl

/-- The Serre path of a trail of a simple graph is reduced. -/
theorem IsTrail.isReduced_toSerrePath {u v : V} {p : G.Walk u v} (hp : p.IsTrail) :
    Path.IsReduced G.toSerreGraph p.toSerrePath :=
  (isReduced_toSerrePath_iff p).mpr hp.isChain_ne_symm_darts

end Walk

/-- In an acyclic simple graph, the Serre path of a walk is reduced exactly when the walk is a
path. -/
theorem IsAcyclic.isReduced_toSerrePath_iff {G : SimpleGraph V} (hG : G.IsAcyclic) {u v : V}
    (p : G.Walk u v) : Path.IsReduced G.toSerreGraph p.toSerrePath ↔ p.IsPath :=
  (Walk.isReduced_toSerrePath_iff p).trans (hG.isPath_iff_isChain_darts p).symm

/-- A path of the Serre graph of a simple graph as a walk, traversing the same darts. -/
def serrePathToWalk {u : V} : ∀ {v : V}, G.toSerreGraph.Path u v → G.Walk u v
  | _, .nil => .nil
  | _, .cons p e => (serrePathToWalk p).concat (G.adj_of_toSerreGraph_hom e)

@[simp] theorem serrePathToWalk_nil (u : V) :
    G.serrePathToWalk (Quiver.Path.nil : G.toSerreGraph.Path u u) = .nil := (rfl)

@[simp] theorem serrePathToWalk_cons {u v w : V} (p : G.toSerreGraph.Path u v)
    (e : @Quiver.Hom G.toSerreGraph.V G.toSerreGraph.toQuiver v w) :
    G.serrePathToWalk (p.cons e) =
      (G.serrePathToWalk p).concat (G.adj_of_toSerreGraph_hom e) := (rfl)

/-- The walk of a Serre path has that path as its Serre path. -/
@[simp] theorem toSerrePath_serrePathToWalk {u v : V} (p : G.toSerreGraph.Path u v) :
    (G.serrePathToWalk p).toSerrePath = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [serrePathToWalk_cons, Walk.toSerrePath_concat, ih,
      toSerreGraphArrow_adj_of_toSerreGraph_hom]

/-- The walk of a Serre path traverses the darts of the path. -/
@[simp] theorem darts_serrePathToWalk {u v : V} (p : G.toSerreGraph.Path u v) :
    (G.serrePathToWalk p).darts = Path.darts G.toSerreGraph p := by
  rw [← Walk.darts_toSerrePath, toSerrePath_serrePathToWalk]

/-- The Serre path of a walk has that walk as its walk. -/
@[simp] theorem serrePathToWalk_toSerrePath {u v : V} (p : G.Walk u v) :
    G.serrePathToWalk p.toSerrePath = p :=
  Walk.darts_injective (by simp)

/-- The walks of a simple graph between two vertices are the paths of its Serre graph between
them. -/
def Walk.serrePathEquiv (u v : V) : G.Walk u v ≃ G.toSerreGraph.Path u v where
  toFun := Walk.toSerrePath
  invFun := G.serrePathToWalk
  left_inv := G.serrePathToWalk_toSerrePath
  right_inv := G.toSerrePath_serrePathToWalk

@[simp] theorem Walk.serrePathEquiv_apply {u v : V} (p : G.Walk u v) :
    Walk.serrePathEquiv G u v p = p.toSerrePath := (rfl)

@[simp] theorem Walk.serrePathEquiv_symm_apply {u v : V} (p : G.toSerreGraph.Path u v) :
    (Walk.serrePathEquiv G u v).symm p = G.serrePathToWalk p := (rfl)

/-- Path composition corresponds to concatenation of walks. -/
@[simp] theorem serrePathToWalk_comp {u v w : V} (p : G.toSerreGraph.Path u v)
    (q : G.toSerreGraph.Path v w) :
    G.serrePathToWalk (p.comp q) = (G.serrePathToWalk p).append (G.serrePathToWalk q) :=
  (Walk.serrePathEquiv G u w).injective (by simp)

/-- Path reversal corresponds to reversal of walks. -/
@[simp] theorem serrePathToWalk_reverse {u v : V} (p : G.toSerreGraph.Path u v) :
    G.serrePathToWalk p.reverse = (G.serrePathToWalk p).reverse :=
  (Walk.serrePathEquiv G v u).injective (by simp)

/-- The walk of a Serre path has the length of the path. -/
@[simp] theorem length_serrePathToWalk {u v : V} (p : G.toSerreGraph.Path u v) :
    (G.serrePathToWalk p).length = p.length := by
  rw [← Walk.length_toSerrePath, toSerrePath_serrePathToWalk]

/-- The Serre graph of a simple graph is preconnected exactly when the simple graph is. -/
theorem preconnected_toSerreGraph_iff : G.toSerreGraph.Preconnected ↔ G.Preconnected := by
  rw [preconnected_iff]
  exact forall₂_congr fun u v => (Walk.serrePathEquiv G u v).nonempty_congr.symm

/-- The Serre graph of a simple graph is connected exactly when the simple graph is. -/
theorem connected_toSerreGraph_iff : G.toSerreGraph.Connected ↔ G.Connected := by
  rw [SerreGraph.connected_iff, preconnected_toSerreGraph_iff, SimpleGraph.connected_iff,
    and_comm]
  -- The vertex type of the Serre graph is `V` by definition.
  rfl

/-- The Serre graph of a simple graph is acyclic exactly when the simple graph is. -/
theorem isAcyclic_toSerreGraph_iff : G.toSerreGraph.IsAcyclic ↔ G.IsAcyclic := by
  refine ⟨fun h => isAcyclic_iff_subsingleton_path.mpr fun v w => ⟨fun p q => Subtype.ext ?_⟩,
    fun h => (isAcyclic_iff _).mpr fun u p hp => ?_⟩
  · exact (Walk.serrePathEquiv G v w).injective
      (h.eq_of_isReduced p.2.isTrail.isReduced_toSerrePath q.2.isTrail.isReduced_toSerrePath)
  · rw [← G.toSerrePath_serrePathToWalk p, h.isReduced_toSerrePath_iff, Walk.isPath_iff_nil,
      ← Walk.eq_nil_iff_nil] at hp
    rw [← G.toSerrePath_serrePathToWalk p, hp, Walk.toSerrePath_nil]

/-- The Serre graph of a simple graph is a tree exactly when the simple graph is. -/
theorem isTree_toSerreGraph_iff : G.toSerreGraph.IsTree ↔ G.IsTree := by
  rw [SerreGraph.isTree_iff, connected_toSerreGraph_iff, isAcyclic_toSerreGraph_iff,
    SimpleGraph.isTree_iff]

end SimpleGraph
