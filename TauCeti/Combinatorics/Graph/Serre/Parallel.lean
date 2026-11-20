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
is the segment, and for an empty type it consists of two isolated vertices. Its geometric edges
correspond to the elements of `α` (`parallelGraphGeomEdgeEquiv`).

The graph is connected exactly when `α` is nonempty, and then its underlying multigraph has one
component; when `α` is empty it has two. For `a ≠ b` the closed path `parallelLoop a b`, which
crosses the edge `a` and comes back along the edge `b`, is reduced and nonempty; for `a = b` it
backtracks and reduces to the empty path. Hence the graph is acyclic exactly when `α` has at
most one element, and a tree exactly when `α` has exactly one element: multiple edges are
detected by the tree predicate. Traversed backwards, `parallelLoop a b` is `parallelLoop b a`.

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
along the edge `a` from the vertex `b` to the vertex `!b`. The definition unfolds at instance
transparency, so that a pair in `α × Bool` is accepted as a dart by rewriting and
simplification. -/
@[expose, instance_reducible] def parallelGraph (α : Type w) : SerreGraph.{0, w} where
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

/-- A graph of parallel edges has two vertices. -/
instance : Fintype (parallelGraph α).V := inferInstanceAs (Fintype Bool)

/-- The two vertices of a graph of parallel edges have decidable equality. -/
instance : DecidableEq (parallelGraph α).V := inferInstanceAs (DecidableEq Bool)

/-- The vertex `false` of a graph of parallel edges. -/
instance : Inhabited (parallelGraph α).V := inferInstanceAs (Inhabited Bool)

/-- The two vertices of a graph of parallel edges are distinct. -/
instance : Nontrivial (parallelGraph α).V := inferInstanceAs (Nontrivial Bool)

/-- A graph of parallel edges indexed by a nonempty type has a dart. -/
instance [Nonempty α] : Nonempty (parallelGraph α).E := inferInstanceAs (Nonempty (α × Bool))

/-- The dart along the default edge leaving the vertex `false`. -/
instance [Inhabited α] : Inhabited (parallelGraph α).E := inferInstanceAs (Inhabited (α × Bool))

/-- A graph of finitely many parallel edges has finitely many darts. -/
instance [Finite α] : Finite (parallelGraph α).E := inferInstanceAs (Finite (α × Bool))

/-- The darts of a graph of finitely many parallel edges, enumerated with the edges. -/
instance [Fintype α] : Fintype (parallelGraph α).E := inferInstanceAs (Fintype (α × Bool))

/-- The darts of a graph of parallel edges, being pairs of an edge and a direction, have
decidable equality when the edges do. -/
instance [DecidableEq α] : DecidableEq (parallelGraph α).E :=
  inferInstanceAs (DecidableEq (α × Bool))

/-- A graph of parallel edges indexed by an empty type has no dart. -/
instance [IsEmpty α] : IsEmpty (parallelGraph α).E := inferInstanceAs (IsEmpty (α × Bool))

/-- The darts leaving the vertex `true` form an orientation of a graph of parallel edges. -/
theorem parallelGraph_isOrientation : (parallelGraph α).IsOrientation {e | e.2 = true} :=
  (isOrientation_iff _ _).mpr fun e => by simp

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

/-- Two darts of a graph of parallel edges have the same geometric edge exactly when they have
the same index. -/
@[simp] theorem parallelGraph_toGeomEdge_eq_iff (e f : (parallelGraph α).E) :
    (parallelGraph α).toGeomEdge e = (parallelGraph α).toGeomEdge f ↔ e.1 = f.1 := by
  rw [toGeomEdge_eq_toGeomEdge_iff, ← edge_eq_iff, parallelGraph_edge_eq_iff, eq_comm]

/-- The geometric edges of a graph of parallel edges are its edge indices. -/
def parallelGraphGeomEdgeEquiv (α : Type w) : (parallelGraph α).GeomEdge ≃ α where
  toFun := GeomEdge.lift (parallelGraph α) Prod.fst fun _ => rfl
  invFun a := (parallelGraph α).toGeomEdge (a, true)
  left_inv x := by
    obtain ⟨e, rfl⟩ := (parallelGraph α).toGeomEdge_surjective x
    exact (parallelGraph_toGeomEdge_eq_iff _ _).mpr (GeomEdge.lift_toGeomEdge _ _ _ _)
  right_inv _ := GeomEdge.lift_toGeomEdge _ _ _ _

@[simp] theorem parallelGraphGeomEdgeEquiv_toGeomEdge (e : (parallelGraph α).E) :
    parallelGraphGeomEdgeEquiv α ((parallelGraph α).toGeomEdge e) = e.1 :=
  GeomEdge.lift_toGeomEdge _ _ _ _

@[simp] theorem parallelGraphGeomEdgeEquiv_symm_apply (a : α) :
    (parallelGraphGeomEdgeEquiv α).symm a = (parallelGraph α).toGeomEdge (a, true) :=
  (rfl)

/-- Every undirected edge of a graph of parallel edges joins the two vertices. -/
@[simp] theorem parallelGraph_edgeEnds (q : (parallelGraph α).Edge) :
    (parallelGraph α).edgeEnds q = s(false, true) := by
  have key : ∀ x : Bool, s(x, !x) = s(false, true) := by decide
  induction q using Edge.ind with
  | h e => rw [edgeEnds_edge, parallelGraph_src, parallelGraph_tgt]; exact key e.2

/-- The dart `(a, false)`, which runs along the edge `a` from the vertex `false` to the vertex
`true`, as an arrow of the quiver of the graph. -/
def parallelDart (a : α) : Quiver.Hom (V := (parallelGraph α).V) false true :=
  (parallelGraph α).dart (a, false)

@[simp] theorem parallelDart_val (a : α) : (parallelDart a).1 = (a, false) :=
  dart_val _ _

/-- A graph of parallel edges is preconnected exactly when it has an edge. -/
@[simp] theorem parallelGraph_preconnected_iff : (parallelGraph α).Preconnected ↔ Nonempty α := by
  refine ⟨fun h => ?_, fun ⟨a⟩ => ?_⟩
  · by_contra hα
    rw [not_nonempty_iff] at hα
    exact not_subsingleton Bool
      (((parallelGraph α).preconnected_iff_of_forall_src_eq_tgt isEmptyElim).mp h)
  · refine (parallelGraph α).preconnected_of_forall_nonempty_path false fun b => ?_
    cases b
    · exact ⟨.nil⟩
    · exact ⟨(parallelDart a).toPath⟩

/-- A graph of parallel edges is connected exactly when it has an edge. -/
@[simp] theorem parallelGraph_connected_iff : (parallelGraph α).Connected ↔ Nonempty α := by
  rw [connected_iff, parallelGraph_preconnected_iff]
  exact and_iff_right ⟨false⟩

/-- The closed path at the vertex `false` that crosses the edge `a` and returns along the
edge `b`. -/
def parallelLoop (a b : α) : (parallelGraph α).Path false false :=
  (parallelDart a).toPath.cons (Quiver.reverse (parallelDart b))

/-- The closed path `parallelLoop a b` is the arrow `parallelDart a` followed by the reverse of
the arrow `parallelDart b`. -/
theorem parallelLoop_def (a b : α) :
    parallelLoop a b = (parallelDart a).toPath.cons (Quiver.reverse (parallelDart b)) :=
  (rfl)

/-- Traversing the closed path `parallelLoop a b` backwards crosses the edge `b` and returns
along the edge `a`. -/
@[simp] theorem reverse_parallelLoop (a b : α) :
    (parallelLoop a b).reverse = parallelLoop b a := by
  simp [parallelLoop_def]

@[simp] theorem darts_parallelLoop (a b : α) :
    Path.darts (parallelGraph α) (parallelLoop a b) = [(a, false), (b, true)] := by
  simp [parallelLoop_def, reverse_val (parallelGraph α)]

@[simp] theorem length_parallelLoop (a b : α) : (parallelLoop a b).length = 2 :=
  (Path.length_darts _ _).symm.trans (congrArg List.length (darts_parallelLoop a b))

/-- Crossing one edge and returning along another is reduced exactly when the two edges are
distinct. -/
@[simp] theorem isReduced_parallelLoop_iff {a b : α} :
    Path.IsReduced (parallelGraph α) (parallelLoop a b) ↔ a ≠ b := by
  rw [Path.isReduced_iff_isChain, darts_parallelLoop, List.isChain_pair, parallelGraph_rev]
  exact not_congr ⟨fun h => (congrArg Prod.fst h).symm, fun h => h ▸ rfl⟩

/-- Crossing an edge and returning along it reduces to the empty path. -/
@[simp] theorem reduce_parallelLoop_self (a : α) :
    Path.reduce (parallelGraph α) (parallelLoop a a) = Quiver.Path.nil := by
  simp [parallelLoop_def, Quiver.Hom.toPath]

/-- A graph with two distinct parallel edges is not acyclic. -/
theorem parallelGraph_not_isAcyclic {a b : α} (hab : a ≠ b) : ¬(parallelGraph α).IsAcyclic :=
  fun h => two_ne_zero <| (length_parallelLoop a b).symm.trans <| congrArg Quiver.Path.length <|
    (isAcyclic_iff _).mp h false (parallelLoop a b) (isReduced_parallelLoop_iff.mpr hab)

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

/-- The multigraph underlying a graph of parallel edges without an edge has two components,
the two isolated vertices. -/
@[simp] theorem componentCount_toGraph_parallelGraph_of_isEmpty [IsEmpty α] :
    (parallelGraph α).toGraph.componentCount = 2 := by
  rw [componentCount_toGraph_of_forall_src_eq_tgt _ isEmptyElim]
  exact Nat.card_eq_fintype_card.trans Fintype.card_bool

/-- The multigraph underlying a graph of parallel edges with at least one edge has one
component. -/
@[simp] theorem componentCount_toGraph_parallelGraph [Nonempty α] :
    (parallelGraph α).toGraph.componentCount = 1 := by
  rw [Graph.componentCount_eq_one_iff, connected_toGraph_iff, parallelGraph_connected_iff]
  infer_instance

end SerreGraph
end TauCeti
