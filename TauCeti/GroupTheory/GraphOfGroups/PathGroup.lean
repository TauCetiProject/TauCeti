/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Path.Functoriality
public import TauCeti.Combinatorics.Quiver.PathWeight
public import TauCeti.GroupTheory.GraphOfGroups.Presentation

/-!
# Tree-loop presentations of reduced path groups

A spanning tree identifies the reduced closed paths of a Serre graph with the tree
presentation of any graph of groups on it having trivial vertex groups. The inverse sends
a dart to the based loop that follows the tree to its source, crosses the dart, and returns
through the tree. Consequently the reduced path group is free on the positive non-tree darts,
and the free coordinates of a closed path are computed dart by dart: a positive non-tree dart
contributes its generator, its reverse the inverse generator, and a tree dart nothing.
This comparison retains signed loop directions and distinct parallel edges and applies to
infinite graphs as well as finite ones.

The presentation-side free-group equivalence is
`GraphOfGroups.π₁Tree.equivFreeGroup`; the new comparison supplies its path interpretation.

These free coordinates are compatible with the functoriality of the reduced path group:

* they do not depend on the base vertex, once base vertices are compared along tree paths;
* a morphism of Serre graphs carrying a spanning tree into a spanning tree and positive non-tree
  darts to positive non-tree darts acts on free coordinates by the induced map of generators;
* in particular the inclusion of a subgraph containing the spanning tree is, in free
  coordinates, the inclusion of the free group on the positive non-tree darts of the subgraph.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.3–3.1.
* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2.
* I. Kapovich, A. Myasnikov, *Stallings foldings and subgroups of free groups*, §6, Lemma 6.1.
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

@[simp] private theorem toTreePresentation_loop (e : Γ.E) :
    T.toTreePresentation v 𝔸 (T.loop v e) = GraphOfGroups.π₁Tree.edge T.darts e := by
  simp [loop_def, Quiver.Path.weight_comp,
    T.weight_path_eq_one (fun _ => GraphOfGroups.π₁Tree.edge_eq_one (𝔸 := 𝔸))]

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
  (T.pathGroupEquivTreePresentation v (GraphOfGroups.trivial Γ)).trans
    (GraphOfGroups.π₁Tree.equivFreeGroup _ hO T.rev_mem)

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

/-- In tree coordinates a closed path is the product of the signed coordinates of its darts:
each positive non-tree dart contributes its generator, its reverse contributes the inverse
generator, and tree darts contribute nothing. The path need not be reduced. -/
theorem pathGroupEquivFreeGroup_ofPath {O : Set Γ.E} (hO : Γ.IsOrientation O) (p : Γ.Path v v) :
    T.pathGroupEquivFreeGroup v hO (PathGroup.ofPath p) =
      p.weight (fun {a b : Γ.V} (e : a ⟶ b) =>
        GraphOfGroups.π₁Tree.dartWord O T.darts e.1) := by
  simp [pathGroupEquivFreeGroup, Quiver.Path.map_weight,
    GraphOfGroups.π₁Tree.equivFreeGroup_edge_eq_dartWord]

/-- The tree coordinates of a reduced closed path are the product of the signed coordinates
of its darts. -/
theorem pathGroupEquivFreeGroup_apply {O : Set Γ.E} (hO : Γ.IsOrientation O) (g : PathGroup Γ v) :
    T.pathGroupEquivFreeGroup v hO g =
      g.toPath.weight (fun {a b : Γ.V} (e : a ⟶ b) =>
        GraphOfGroups.π₁Tree.dartWord O T.darts e.1) := by
  rw [← T.pathGroupEquivFreeGroup_ofPath v hO, PathGroup.ofPath_toPath]

end

/-! ### Naturality of the free coordinates -/

section Naturality

universe u' w'

variable {Δ : SerreGraph.{u', w'}} {O : Set Γ.E} (hO : Γ.IsOrientation O)

/-- The free coordinates of a reduced loop relative to a spanning tree are unchanged by moving
the base vertex along a tree path. -/
@[simp] theorem pathGroupEquivFreeGroup_mulEquivOfPath_path (w : Γ.V) (g : PathGroup Γ v) :
    T.pathGroupEquivFreeGroup w hO (PathGroup.mulEquivOfPath (T.path v w) g) =
      T.pathGroupEquivFreeGroup v hO g := by
  have key : ((T.pathGroupEquivFreeGroup w hO).toMonoidHom.comp
      (PathGroup.mulEquivOfPath (T.path v w)).toMonoidHom).comp
        (T.pathGroupEquivFreeGroup v hO).symm.toMonoidHom = MonoidHom.id _ := by
    ext e
    simp
  simpa using DFunLike.congr_fun key (T.pathGroupEquivFreeGroup v hO g)

/-- A morphism of Serre graphs carrying a spanning tree `T` into a spanning tree `T'`, and the
positive darts outside `T` to positive darts outside `T'`, acts on free coordinates by the
induced map of free generators. -/
theorem pathGroupEquivFreeGroup_map (f : Γ.Hom Δ) (T' : Δ.SpanningTree) {O' : Set Δ.E}
    (hO' : Δ.IsOrientation O') (hT : ∀ e ∈ T.darts, f.mapE e ∈ T'.darts)
    (hf : Set.MapsTo f.mapE (O \ T.darts) (O' \ T'.darts)) {w : Δ.V} (h : f.mapV v = w)
    (g : PathGroup Γ v) :
    T'.pathGroupEquivFreeGroup w hO' (PathGroup.map f h g) =
      FreeGroup.map (Set.MapsTo.restrict f.mapE _ _ hf) (T.pathGroupEquivFreeGroup v hO g) := by
  have key : ((T'.pathGroupEquivFreeGroup w hO').toMonoidHom.comp (PathGroup.map f h)).comp
      (T.pathGroupEquivFreeGroup v hO).symm.toMonoidHom =
        FreeGroup.map (Set.MapsTo.restrict f.mapE _ _ hf) := by
    ext e
    simpa [T.map_loop v f T' hT h] using
      T'.pathGroupEquivFreeGroup_loop w hO' (Set.MapsTo.restrict f.mapE _ _ hf e)
  simpa using DFunLike.congr_fun key (T.pathGroupEquivFreeGroup v hO g)

/-- In free coordinates, the inclusion of a subgraph containing a spanning tree is the inclusion
of the free group on the positive non-tree darts of the subgraph. -/
theorem pathGroupEquivFreeGroup_map_restrictInclusion (S : Set Γ.E)
    (hS : ∀ e ∈ S, Γ.rev e ∈ S) (hTS : T.darts ⊆ S) {O' : Set (Γ.restrict S hS).E}
    (hO' : (Γ.restrict S hS).IsOrientation O') (hOO' : ∀ e ∈ O', e.1 ∈ O) {w : Γ.V}
    (h : (Γ.restrictInclusion S hS).mapV v = w) (g : PathGroup (Γ.restrict S hS) v) :
    T.pathGroupEquivFreeGroup w hO (PathGroup.map (Γ.restrictInclusion S hS) h g) =
      FreeGroup.map (fun e : ↥(O' \ (T.restrict S hS hTS).darts) =>
          (⟨e.1.1, hOO' e.1 e.2.1, fun he => e.2.2 ((T.mem_restrict_darts S hS hTS).mpr he)⟩ :
            ↥(O \ T.darts)))
        ((T.restrict S hS hTS).pathGroupEquivFreeGroup v hO' g) :=
  (T.restrict S hS hTS).pathGroupEquivFreeGroup_map v hO' (Γ.restrictInclusion S hS) T hO
    (fun _ he => (T.mem_restrict_darts S hS hTS).mp he)
    (fun e he => ⟨hOO' e he.1, fun he' => he.2 ((T.mem_restrict_darts S hS hTS).mpr he')⟩) h g

end Naturality

end TauCeti.SerreGraph.SpanningTree
