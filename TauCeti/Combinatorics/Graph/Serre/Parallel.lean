/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Multigraph
public import TauCeti.Combinatorics.Graph.Serre.Tree

/-!
# Two vertices joined by parallel edges

The Serre graph `SerreGraph.parallelGraph α` has the two vertices `false` and `true` and, for
each `a : α`, a pair of mutually reverse darts joining them: the dart `(a, b)` runs from the
vertex `b` to the vertex `!b`. Distinct elements of `α` give distinct geometric edges with the
same ends, so this is the basic example of a graph with multiple edges; for a one-element type it
is the segment, and for an empty type it consists of two isolated vertices.

The graph is connected exactly when `α` is nonempty, and then its underlying multigraph has one
component. For `a ≠ b` the closed path `parallelLoop a b`, which crosses the edge `a` and comes
back along the edge `b`, is reduced and nonempty. Hence the graph is acyclic exactly when `α` has
at most one element, and a tree exactly when `α` has exactly one element: multiple edges are
detected by the tree predicate.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.1–2.2.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, §2, Convention 2.1.
-/

public section

universe w

namespace TauCeti
namespace SerreGraph

/-- Two vertices joined by a family of parallel edges indexed by `α`. The dart `(a, b)` runs
along the edge `a` from the vertex `b` to the vertex `!b`. -/
@[expose] def parallelGraph (α : Type w) : SerreGraph.{0, w} where
  V := Bool
  E := α × Bool
  src := Prod.snd
  rev e := (e.1, !e.2)
  rev_rev := by simp
  rev_ne := by simp [Prod.ext_iff]

variable {α : Type w}

@[simp] theorem parallelGraph_src (e : (parallelGraph α).E) : (parallelGraph α).src e = e.2 :=
  rfl

@[simp] theorem parallelGraph_rev (e : (parallelGraph α).E) :
    (parallelGraph α).rev e = (e.1, !e.2) := rfl

/-- Each dart of a graph of parallel edges ends at the vertex other than its source. -/
@[simp] theorem parallelGraph_tgt (e : (parallelGraph α).E) :
    (parallelGraph α).tgt e = !e.2 := rfl

/-- The darts of a graph of parallel edges, being pairs of an edge and a direction, have
decidable equality when the edges do. -/
instance [DecidableEq α] : DecidableEq (parallelGraph α).E :=
  inferInstanceAs (DecidableEq (α × Bool))

/-- The darts leaving the vertex `true` form an orientation of a graph of parallel edges. -/
theorem parallelGraph_isOrientation : (parallelGraph α).IsOrientation {e | e.2 = true} :=
  -- Membership is unfolded first: once `parallelGraph_rev` turns a dart into a pair `α × Bool`,
  -- `Set.mem_ofPred_eq` no longer matches a set of darts.
  (isOrientation_iff _ _).mpr fun e => by simp only [Set.mem_ofPred_eq]; simp

/-- Two darts of a graph of parallel edges lie on the same undirected edge exactly when they
have the same index: parallel edges remain distinct. -/
@[simp] theorem parallelGraph_edge_eq_iff (e f : (parallelGraph α).E) :
    (parallelGraph α).edge e = (parallelGraph α).edge f ↔ e.1 = f.1 := by
  have key : ∀ e f : α × Bool, e = f ∨ e = (f.1, !f.2) ↔ e.1 = f.1 := by
    rintro ⟨a, x⟩ ⟨b, y⟩
    cases x <;> cases y <;> simp
  -- The darts of `parallelGraph α` are, by definition, the pairs in `α × Bool`.
  rw [edge_eq_iff, parallelGraph_rev]
  exact key e f

/-- Every undirected edge of a graph of parallel edges joins the two vertices. -/
@[simp] theorem parallelGraph_edgeEnds (q : (parallelGraph α).Edge) :
    (parallelGraph α).edgeEnds q = s(false, true) := by
  have key : ∀ x : Bool, s(x, !x) = s(false, true) := by decide
  induction q using Edge.ind with
  | h e => rw [edgeEnds_edge, parallelGraph_src, parallelGraph_tgt]; exact key e.2

/-- A graph of parallel edges is preconnected exactly when it has an edge. -/
@[simp] theorem parallelGraph_preconnected_iff : (parallelGraph α).Preconnected ↔ Nonempty α := by
  refine ⟨fun h => ?_, fun ⟨a⟩ => ?_⟩
  · by_contra hα
    rw [not_nonempty_iff] at hα
    obtain ⟨p⟩ := (parallelGraph α).preconnected_iff.mp h false true
    exact Bool.false_ne_true
      ((parallelGraph α).eq_of_path_of_forall_src_eq_tgt (fun e => isEmptyElim e.1) p)
  · refine (parallelGraph α).preconnected_of_forall_nonempty_path false fun b => ?_
    cases b
    · exact ⟨.nil⟩
    · -- The dart `(a, false)` runs from `false` to `true` by `parallelGraph_src` and
      -- `parallelGraph_tgt`, used through `rfl`: they cannot rewrite a literal pair, whose type
      -- is `α × Bool` rather than `(parallelGraph α).E`.
      exact ⟨((parallelGraph α).dart (a, false)).toPath⟩

/-- A graph of parallel edges is connected exactly when it has an edge. -/
@[simp] theorem parallelGraph_connected_iff : (parallelGraph α).Connected ↔ Nonempty α := by
  rw [connected_iff, parallelGraph_preconnected_iff]
  exact and_iff_right ⟨false⟩

/-- The closed path at the vertex `false` that crosses the edge `a` and returns along the
edge `b`. -/
def parallelLoop (a b : α) : (parallelGraph α).Path false false :=
  (Quiver.Hom.toPath
    (⟨(a, false), rfl, rfl⟩ : Quiver.Hom (V := (parallelGraph α).V) false true)).cons
    ⟨(b, true), rfl, rfl⟩

@[simp] theorem darts_parallelLoop (a b : α) :
    Path.darts (parallelGraph α) (parallelLoop a b) = [(a, false), (b, true)] :=
  (Path.darts_cons _ _ _).trans (congrArg (· ++ _) (Path.darts_toPath _ _))

@[simp] theorem length_parallelLoop (a b : α) : (parallelLoop a b).length = 2 :=
  (Path.length_darts _ _).symm.trans (congrArg List.length (darts_parallelLoop a b))

/-- Crossing one edge and returning along another is reduced exactly when the two edges are
distinct. -/
@[simp] theorem parallelLoop_isReduced_iff {a b : α} :
    Path.IsReduced (parallelGraph α) (parallelLoop a b) ↔ a ≠ b := by
  refine (Path.isReduced_iff_isChain _ _).trans ?_
  rw [darts_parallelLoop]
  -- The reverse of the dart `(a, false)` is `(a, true)` by `parallelGraph_rev`, used through
  -- `rfl`: the darts listed here are literal pairs, of type `α × Bool`.
  exact List.isChain_pair.trans (not_congr ⟨fun h => (congrArg Prod.fst h).symm, fun h => h ▸ rfl⟩)

/-- A graph with two distinct parallel edges is not acyclic. -/
theorem parallelGraph_not_isAcyclic {a b : α} (hab : a ≠ b) : ¬(parallelGraph α).IsAcyclic :=
  fun h => two_ne_zero <| (length_parallelLoop a b).symm.trans <| congrArg Quiver.Path.length <|
    (isAcyclic_iff _).mp h false (parallelLoop a b) (parallelLoop_isReduced_iff.mpr hab)

/-- A graph of parallel edges is acyclic exactly when it has at most one edge. -/
@[simp] theorem parallelGraph_isAcyclic_iff : (parallelGraph α).IsAcyclic ↔ Subsingleton α := by
  refine ⟨fun h => ⟨fun a b => by_contra fun hab => parallelGraph_not_isAcyclic hab h⟩,
    fun _ => (isAcyclic_iff _).mpr fun u p hp => ?_⟩
  cases p with
  | nil => rfl
  | cons p f =>
    cases p with
    | nil =>
      -- A single dart is not closed: its ends `f.1.2` and `!f.1.2` differ.
      have h := f.2.2.trans f.2.1.symm
      rw [parallelGraph_tgt, parallelGraph_src] at h
      exact absurd h (Bool.not_ne_self _)
    | cons p e =>
      -- With a single edge, a dart following `e` can only be its reverse.
      have h := f.2.1.trans e.2.2.symm
      rw [parallelGraph_src, parallelGraph_tgt] at h
      have hf : f.1 = (parallelGraph α).rev e.1 := by
        rw [parallelGraph_rev]
        exact Prod.ext (Subsingleton.elim _ _) h
      exact absurd hf ((Path.isReduced_cons_cons _ p e f).mp hp).2

/-- A graph of parallel edges is a tree exactly when it has exactly one edge. -/
@[simp] theorem parallelGraph_isTree_iff :
    (parallelGraph α).IsTree ↔ Nonempty α ∧ Subsingleton α := by
  rw [isTree_iff, parallelGraph_connected_iff, parallelGraph_isAcyclic_iff]

/-- Two vertices joined by two edges do not form a tree. -/
theorem double_edge_not_tree : ¬(parallelGraph Bool).IsTree :=
  fun h => Bool.false_ne_true ((parallelGraph_isTree_iff.mp h).2.elim _ _)

/-- The multigraph underlying a graph of parallel edges with at least one edge has one
component. -/
@[simp] theorem componentCount_toGraph_parallelGraph [Nonempty α] :
    (parallelGraph α).toGraph.componentCount = 1 := by
  rw [Graph.componentCount_eq_one_iff, connected_toGraph_iff, parallelGraph_connected_iff]
  infer_instance

end SerreGraph
end TauCeti
