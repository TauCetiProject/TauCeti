/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Path.SpanningTree
public import TauCeti.GroupTheory.GraphOfGroups.Presentation

/-!
# Tree-loop presentations of reduced path groups

A spanning tree identifies the reduced closed paths of a Serre graph with the tree
presentation of any graph of groups on it having trivial vertex groups. The inverse sends
a dart to the based loop that follows the tree to its source, crosses the dart, and returns
through the tree. Consequently the reduced path group is free on the positive non-tree darts.
This comparison retains signed loop directions and distinct parallel edges and applies to
infinite graphs as well as finite ones.

The presentation-side free-group equivalence is
`GraphOfGroups.π₁Tree.equivFreeGroup`; the new comparison supplies its path interpretation.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.3–3.1.
* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2.
-/

public section

namespace TauCeti.SerreGraph.SpanningTree

universe u w x y

variable {Γ : SerreGraph.{u, w}} (T : Γ.SpanningTree) (v : Γ.V)

noncomputable section

variable (𝔸 : GraphOfGroups.{u, w, x, y} Γ)

/-- Read a reduced loop as a product of dart generators in the tree presentation. -/
private def toTreePresentation : PathGroup Γ v →* GraphOfGroups.π₁Tree 𝔸 T.darts :=
  PathGroup.lift (GraphOfGroups.π₁Tree.edge T.darts)
    (GraphOfGroups.π₁Tree.edge_rev)

/-- Send a presentation dart to its based tree loop. Trivial vertex groups map trivially. -/
private def fromTreePresentation : GraphOfGroups.π₁Tree 𝔸 T.darts →* PathGroup Γ v :=
  GraphOfGroups.π₁Tree.lift (fun _ => 1) (T.loop v)
    (fun _ => T.loop_eq_one v) (T.loop_rev v) (by intros; simp)

@[simp] private theorem fromTreePresentation_edge (e : Γ.E) :
    T.fromTreePresentation v 𝔸 (GraphOfGroups.π₁Tree.edge T.darts e) = T.loop v e := by
  simp [fromTreePresentation]

@[simp] private theorem toTreePresentation_ofPath (p : Γ.Path v v) :
    T.toTreePresentation v 𝔸 (PathGroup.ofPath p) =
      p.weight (fun {a b : Γ.V} (e : a ⟶ b) =>
        GraphOfGroups.π₁Tree.edge T.darts e.1) := by
  simp only [toTreePresentation, PathGroup.lift_ofPath]

private theorem weight_tree_path (a b : Γ.V) :
    (T.path a b).weight
      (fun {a b : Γ.V} (e : a ⟶ b) =>
        (GraphOfGroups.π₁Tree.edge T.darts e.1 : GraphOfGroups.π₁Tree 𝔸 T.darts)) = 1 := by
  have hw {a b : Γ.V} (p : Γ.Path a b)
      (hp : ∀ e ∈ Path.darts Γ p, e ∈ T.darts) :
      p.weight (fun {a b : Γ.V} (e : a ⟶ b) => (GraphOfGroups.π₁Tree.edge T.darts e.1 :
        GraphOfGroups.π₁Tree 𝔸 T.darts)) = 1 := by
    induction p with
    | nil => simp
    | cons p e ih =>
      simp only [Quiver.Path.weight_cons]
      rw [ih (fun d hd => hp d (by simp [hd])),
        GraphOfGroups.π₁Tree.edge_eq_one (hp e.1 (by simp))]
      simp
  exact hw _ (fun _ => T.mem_of_mem_darts_path)

@[simp] private theorem toTreePresentation_loop (e : Γ.E) :
    T.toTreePresentation v 𝔸 (T.loop v e) = GraphOfGroups.π₁Tree.edge T.darts e := by
  simp [loop_def, Quiver.Path.weight_comp, weight_tree_path]

private theorem fromTreePresentation_weight {a b : Γ.V} (p : Γ.Path a b) :
    T.fromTreePresentation v 𝔸
      (p.weight (fun {a b : Γ.V} (e : a ⟶ b) =>
        GraphOfGroups.π₁Tree.edge T.darts e.1)) = T.basedPath v p := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Quiver.Path.weight_cons, map_mul, ih, fromTreePresentation_edge,
      ← Quiver.Path.comp_toPath_eq_cons, basedPath_comp, basedPath_toPath]

variable [∀ a, Subsingleton (𝔸.vertexGroup a)]

/-- Reduced closed paths are canonically isomorphic to the spanning-tree presentation with
trivial vertex groups. Each dart generator is represented by its based tree loop. -/
def pathGroupEquivTreePresentation : PathGroup Γ v ≃* GraphOfGroups.π₁Tree 𝔸 T.darts :=
  MonoidHom.toMulEquiv (T.toTreePresentation v 𝔸) (T.fromTreePresentation v 𝔸)
    (by
      ext p
      induction p using PathGroup.induction_on with
      | h p => simp [fromTreePresentation_weight])
    (GraphOfGroups.π₁Tree.hom_ext
      (fun a => by ext z; simp [Subsingleton.elim z 1]) (by intro e; simp))

@[simp] theorem pathGroupEquivTreePresentation_ofPath (p : Γ.Path v v) :
    T.pathGroupEquivTreePresentation v 𝔸 (PathGroup.ofPath p) =
      p.weight (fun {a b : Γ.V} (e : a ⟶ b) =>
        GraphOfGroups.π₁Tree.edge T.darts e.1) :=
  T.toTreePresentation_ofPath v 𝔸 p

/-- The tree loop through a dart maps to its presentation generator. -/
@[simp] theorem pathGroupEquivTreePresentation_loop (e : Γ.E) :
    T.pathGroupEquivTreePresentation v 𝔸 (T.loop v e) =
      GraphOfGroups.π₁Tree.edge T.darts e :=
  T.toTreePresentation_loop v 𝔸 e

@[simp] theorem pathGroupEquivTreePresentation_symm_edge (e : Γ.E) :
    (T.pathGroupEquivTreePresentation v 𝔸).symm
      (GraphOfGroups.π₁Tree.edge T.darts e) = T.loop v e :=
  T.fromTreePresentation_edge v 𝔸 e

omit [∀ a, Subsingleton (𝔸.vertexGroup a)]

/-- The reduced path group is free on the positive non-tree darts. -/
def pathGroupEquivFreeGroup {O : Set Γ.E} (hO : Γ.IsOrientation O) :
    PathGroup Γ v ≃* FreeGroup ↥(O \ T.darts) :=
  let 𝔸 : GraphOfGroups.{u, w, 0, 0} Γ :=
    { vertexGroup _ := PUnit
      edgeGroup _ := PUnit
      ω _ := 1
      ω_injective _ := Function.injective_of_subsingleton _ }
  (T.pathGroupEquivTreePresentation v 𝔸).trans
    (GraphOfGroups.π₁Tree.equivFreeGroup 𝔸 hO T.rev_mem)

/-- A free generator corresponds to its based tree loop. -/
@[simp] theorem pathGroupEquivFreeGroup_symm_of {O : Set Γ.E} (hO : Γ.IsOrientation O)
    (e : ↥(O \ T.darts)) :
    (T.pathGroupEquivFreeGroup v hO).symm (FreeGroup.of e) = T.loop v e.1 := by
  simp [pathGroupEquivFreeGroup]

/-- Positive non-tree loops are the free generators in tree coordinates. -/
@[simp] theorem pathGroupEquivFreeGroup_loop {O : Set Γ.E} (hO : Γ.IsOrientation O)
    (e : ↥(O \ T.darts)) :
    T.pathGroupEquivFreeGroup v hO (T.loop v e.1) = FreeGroup.of e := by
  apply (T.pathGroupEquivFreeGroup v hO).symm.injective
  simp

end
end TauCeti.SerreGraph.SpanningTree
