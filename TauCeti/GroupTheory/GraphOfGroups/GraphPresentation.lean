/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.Rank
public import TauCeti.GroupTheory.PresentedGroup

/-!
# The fundamental group of a graph as a presented group

For a Serre graph `Γ` and a set `T` of darts, `SerreGraph.GraphPresentation Γ T` is the group
presented by the darts of `Γ` subject to the relations

* `e * rev e = 1` for every dart `e`;
* `e = 1` for every dart `e ∈ T`.

When `Γ` is connected and `T` is the set of darts of a spanning tree, this is the fundamental
group of the graph: sending a reduced closed path at a base vertex to the product of its darts
is an isomorphism from the reduced path group, whose inverse sends a dart to the loop that
follows the tree to its source, crosses the dart, and returns through the tree. For an
orientation `O`, the group is free on the darts of `O` outside the tree.

The construction makes sense for every set of darts; only the comparison with reduced closed
paths uses a spanning tree, and the free basis only needs `T` to be closed under reversal. A
loop and its reverse are distinct, mutually inverse generators, and parallel edges give distinct
generators.

## Main definitions

* `TauCeti.SerreGraph.graphRelators`: the relators `e * rev e` and `e` for `e ∈ T`.
* `TauCeti.SerreGraph.GraphPresentation`: the presented group.
* `TauCeti.SerreGraph.GraphPresentation.lift`: its universal property.
* `TauCeti.SerreGraph.GraphPresentation.equivTreePresentation`: the isomorphism with the tree
  presentation `GraphOfGroups.π₁Tree` of a graph of groups with trivial vertex groups.
* `TauCeti.SerreGraph.GraphPresentation.equivFreeGroup`: the isomorphism with the free group on
  the positive darts outside `T`.
* `TauCeti.SerreGraph.SpanningTree.pathGroupEquivGraphPresentation`: the isomorphism from the
  reduced path group.

## Main results

* `TauCeti.SerreGraph.SpanningTree.graphPresentation_reducedLoop_bijective`: every element of
  the presentation relative to a spanning tree is the dart word of exactly one reduced closed
  path.
* `TauCeti.SerreGraph.GraphPresentation.fg_iff_finite`,
  `TauCeti.SerreGraph.GraphPresentation.rank_eq_nat_card`: finite generation and rank in terms
  of the positive darts outside `T`.
* `TauCeti.SerreGraph.roseGraphPresentationEquivFreeGroup`: the rose has free fundamental group
  on its petals, the two darts of a petal giving a generator and its inverse.
* `TauCeti.SerreGraph.IsAcyclic.subsingleton_graphPresentation`: an acyclic graph has trivial
  fundamental group.

## References

* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2.
* J.-P. Serre, *Trees*, Chapter I, §2.3 and §3.1.
* I. Kapovich, A. Myasnikov, *Stallings foldings and subgroups of free groups*, §6, Lemma 6.1.
-/

public section

namespace TauCeti.SerreGraph

universe u w x y

variable (Γ : SerreGraph.{u, w})

/-- The relators of the fundamental group of a graph relative to a set `T` of darts:
`e * rev e` for every dart `e`, and `e` for every dart `e ∈ T`. -/
def graphRelators (T : Set Γ.E) : Set (FreeGroup Γ.E) :=
  Set.range (fun e => FreeGroup.of e * FreeGroup.of (Γ.rev e)) ∪ FreeGroup.of '' T

variable {Γ} in
theorem mem_graphRelators_iff {T : Set Γ.E} {r : FreeGroup Γ.E} :
    r ∈ Γ.graphRelators T ↔
      (∃ e, FreeGroup.of e * FreeGroup.of (Γ.rev e) = r) ∨ ∃ e ∈ T, FreeGroup.of e = r :=
  Iff.rfl

/-- The fundamental group of a Serre graph relative to a set `T` of darts, as a presented group:
the generators are the darts, a dart and its reverse are mutually inverse, and the darts of `T`
are trivial. For the darts of a spanning tree of a connected graph this is the group of reduced
closed paths at a vertex. -/
abbrev GraphPresentation (T : Set Γ.E) : Type w :=
  PresentedGroup (Γ.graphRelators T)

namespace GraphPresentation

variable {Γ} {T : Set Γ.E}

/-- Reversing a dart inverts its generator. -/
@[simp] theorem of_rev (e : Γ.E) :
    (PresentedGroup.of (Γ.rev e) : Γ.GraphPresentation T) = (PresentedGroup.of e)⁻¹ :=
  eq_inv_of_mul_eq_one_right <|
    (map_mul (PresentedGroup.mk _) _ _).symm.trans (PresentedGroup.one_of_mem (Or.inl ⟨e, rfl⟩))

/-- The darts of `T` are trivial. -/
@[simp] theorem of_eq_one {e : Γ.E} (he : e ∈ T) :
    (PresentedGroup.of e : Γ.GraphPresentation T) = 1 :=
  PresentedGroup.one_of_mem (Or.inr ⟨e, he, rfl⟩)

section lift

variable {H : Type*} [Group H] (h : Γ.E → H) (hT : ∀ e ∈ T, h e = 1)
  (hrev : ∀ e, h (Γ.rev e) = (h e)⁻¹)

/-- The universal property of the presentation: elements `h e` of a group with `h e = 1` for
`e ∈ T` and `h (rev e) = (h e)⁻¹` define a homomorphism sending the dart `e` to `h e`. -/
def lift : Γ.GraphPresentation T →* H :=
  PresentedGroup.toGroup (f := h) <| by
    rintro _ (⟨e, rfl⟩ | ⟨e, he, rfl⟩)
    · simp [hrev]
    · simp [hT e he]

@[simp] theorem lift_of (e : Γ.E) : lift h hT hrev (PresentedGroup.of e) = h e :=
  PresentedGroup.toGroup.of _

@[simp] theorem lift_mk (r : FreeGroup Γ.E) :
    lift h hT hrev (PresentedGroup.mk _ r) = FreeGroup.lift h r :=
  PresentedGroup.toGroup_mk _ r

end lift

section treePresentation

variable (𝔸 : GraphOfGroups.{u, w, x, y} Γ) [∀ a, Subsingleton (𝔸.vertexGroup a)]

variable (T) in
/-- The presentation by darts is the tree presentation of any graph of groups with trivial
vertex groups; dart generators correspond. -/
def equivTreePresentation : Γ.GraphPresentation T ≃* GraphOfGroups.π₁Tree 𝔸 T :=
  MonoidHom.toMulEquiv
    (lift (GraphOfGroups.π₁Tree.edge T) (fun _ => GraphOfGroups.π₁Tree.edge_eq_one)
      GraphOfGroups.π₁Tree.edge_rev)
    (GraphOfGroups.π₁Tree.lift (fun _ => 1) PresentedGroup.of (fun _ => of_eq_one) of_rev
      (by simp))
    (PresentedGroup.ext fun e => by simp)
    (GraphOfGroups.π₁Tree.hom_ext (fun a => by ext z; simp [Subsingleton.elim z 1])
      (by intro e; simp))

@[simp] theorem equivTreePresentation_of (e : Γ.E) :
    equivTreePresentation T 𝔸 (PresentedGroup.of e) = GraphOfGroups.π₁Tree.edge T e := by
  simp [equivTreePresentation]

@[simp] theorem equivTreePresentation_symm_edge (e : Γ.E) :
    (equivTreePresentation T 𝔸).symm (GraphOfGroups.π₁Tree.edge T e) = PresentedGroup.of e := by
  simp [equivTreePresentation]

end treePresentation

end GraphPresentation

/-- The graph of groups on `Γ` all of whose vertex and edge groups are trivial. -/
private def trivialGraphOfGroups (Γ : SerreGraph.{u, w}) : GraphOfGroups.{u, w, 0, 0} Γ where
  vertexGroup _ := PUnit
  edgeGroup _ := PUnit
  ω _ := 1
  ω_injective _ := Function.injective_of_subsingleton _

private instance (a : Γ.V) : Subsingleton ((trivialGraphOfGroups Γ).vertexGroup a) :=
  inferInstanceAs (Subsingleton PUnit)

namespace GraphPresentation

variable {Γ} {T : Set Γ.E} {O : Set Γ.E}

section free

variable (hO : Γ.IsOrientation O) (hT : ∀ e ∈ T, Γ.rev e ∈ T)

/-- Relative to a set `T` of darts closed under reversal, the fundamental group of a graph is
free on the darts of `O \ T` for any orientation `O`; the generator of a dart of `O \ T`
corresponds to the free generator. For the darts of a spanning tree these are the positive
edges outside the tree. -/
noncomputable def equivFreeGroup : Γ.GraphPresentation T ≃* FreeGroup ↥(O \ T) :=
  (equivTreePresentation T (trivialGraphOfGroups Γ)).trans
    (GraphOfGroups.π₁Tree.equivFreeGroup _ hO hT)

@[simp] theorem equivFreeGroup_of {e : Γ.E} (he : e ∈ O \ T) :
    equivFreeGroup hO hT (PresentedGroup.of e) = FreeGroup.of ⟨e, he⟩ := by
  simp [equivFreeGroup, he]

@[simp] theorem equivFreeGroup_symm_of (e : ↥(O \ T)) :
    (equivFreeGroup hO hT).symm (FreeGroup.of e) = PresentedGroup.of e.1 := by
  simp [equivFreeGroup]

include hO hT

/-- Relative to a reversal-closed set `T` of darts, the fundamental group of a graph is
finitely generated exactly when finitely many positive darts lie outside `T`. In particular a
graph with finitely many darts has finitely generated fundamental group, which also follows
from the presentation having finitely many generators. -/
theorem fg_iff_finite : Group.FG (Γ.GraphPresentation T) ↔ Finite ↥(O \ T) :=
  (FreeGroupBasis.ofRepr (equivFreeGroup hO hT)).fg_iff_finite

/-- Relative to a reversal-closed set `T` of darts, the rank of the fundamental group of a
graph is the number of positive darts outside `T`. -/
theorem rank_eq_nat_card [Group.FG (Γ.GraphPresentation T)] :
    Group.rank (Γ.GraphPresentation T) = Nat.card ↥(O \ T) :=
  (FreeGroupBasis.ofRepr (equivFreeGroup hO hT)).rank_eq_nat_card

end free

end GraphPresentation

namespace SpanningTree

variable {Γ} (T : Γ.SpanningTree) (v : Γ.V)

/-- Reduced closed paths at a vertex are canonically isomorphic to the presentation of the
fundamental group relative to a spanning tree: a path is sent to the product of its darts, and
a dart generator corresponds to its based tree loop. -/
noncomputable def pathGroupEquivGraphPresentation :
    PathGroup Γ v ≃* Γ.GraphPresentation T.darts :=
  (T.pathGroupEquivTreePresentation v (trivialGraphOfGroups Γ)).trans
    (GraphPresentation.equivTreePresentation T.darts (trivialGraphOfGroups Γ)).symm

@[simp] theorem pathGroupEquivGraphPresentation_ofPath (p : Γ.Path v v) :
    T.pathGroupEquivGraphPresentation v (PathGroup.ofPath p) =
      ((Path.darts Γ p).map PresentedGroup.of).prod := by
  simp [pathGroupEquivGraphPresentation, Path.weight_eq_prod_map_darts, map_list_prod,
    Function.comp_def]

theorem pathGroupEquivGraphPresentation_apply (g : PathGroup Γ v) :
    T.pathGroupEquivGraphPresentation v g =
      ((Path.darts Γ g.toPath).map PresentedGroup.of).prod := by
  rw [← pathGroupEquivGraphPresentation_ofPath, PathGroup.ofPath_toPath]

/-- The tree loop through a dart maps to its generator. -/
@[simp] theorem pathGroupEquivGraphPresentation_loop (e : Γ.E) :
    T.pathGroupEquivGraphPresentation v (T.loop v e) = PresentedGroup.of e := by
  simp [pathGroupEquivGraphPresentation]

/-- A dart generator corresponds to its based tree loop. -/
@[simp] theorem pathGroupEquivGraphPresentation_symm_of (e : Γ.E) :
    (T.pathGroupEquivGraphPresentation v).symm (PresentedGroup.of e) = T.loop v e := by
  simp [pathGroupEquivGraphPresentation]

/-- Relative to a spanning tree, every element of the presentation of the fundamental group is
the class of the dart word of exactly one reduced closed path at `v`. -/
theorem graphPresentation_reducedLoop_bijective :
    Function.Bijective fun g : PathGroup Γ v =>
      PresentedGroup.mk (Γ.graphRelators T.darts)
        ((Path.darts Γ g.toPath).map FreeGroup.of).prod := by
  convert (T.pathGroupEquivGraphPresentation v).bijective using 2 with g
  simp [pathGroupEquivGraphPresentation_apply, ← PresentedGroup.lift_of_eq_mk, map_list_prod,
    Function.comp_def]

/-- The free coordinates of the path group and of the presentation agree. -/
@[simp] theorem equivFreeGroup_pathGroupEquivGraphPresentation {O : Set Γ.E}
    (hO : Γ.IsOrientation O) (g : PathGroup Γ v) :
    GraphPresentation.equivFreeGroup hO T.rev_mem (T.pathGroupEquivGraphPresentation v g) =
      T.pathGroupEquivFreeGroup v hO g := by
  obtain ⟨z, rfl⟩ := (T.pathGroupEquivFreeGroup v hO).symm.surjective g
  induction z using FreeGroup.induction_on with
  | one => simp
  | of e => simp
  | inv_of e _ => simp
  | mul a b ha hb => simp [ha, hb]

end SpanningTree

/-- An acyclic graph has trivial fundamental group, relative to any spanning tree. -/
theorem IsAcyclic.subsingleton_graphPresentation {Γ : SerreGraph.{u, w}} (h : Γ.IsAcyclic)
    (T : Γ.SpanningTree) : Subsingleton (Γ.GraphPresentation T.darts) := by
  obtain ⟨v⟩ := (Γ.connected_iff.mp (Γ.nonempty_spanningTree_iff.mp ⟨T⟩)).1
  have := h.subsingleton_pathGroup v
  exact (T.pathGroupEquivGraphPresentation v).symm.injective.subsingleton

/-- The image of a dart of a rose in the free group on the petals: the generator for the
dart `(a, true)` and its inverse for `(a, false)`. -/
private def rosePetalWord (α : Type w) (e : (rose α).E) : FreeGroup α :=
  cond e.2 (FreeGroup.of e.1) (FreeGroup.of e.1)⁻¹

private theorem rosePetalWord_true {α : Type w} (a : α) :
    rosePetalWord α (a, true) = FreeGroup.of a := rfl

private theorem rosePetalWord_false {α : Type w} (a : α) :
    rosePetalWord α (a, false) = (FreeGroup.of a)⁻¹ := rfl

private theorem rosePetalWord_rev {α : Type w} (e : (rose α).E) :
    rosePetalWord α ((rose α).rev e) = (rosePetalWord α e)⁻¹ := by
  obtain ⟨a, _ | _⟩ := e
  · simp [rosePetalWord_true, rosePetalWord_false]
  · simp [rosePetalWord_true, rosePetalWord_false]

/-- The homomorphism from the fundamental group of a rose to the free group on its petals. -/
private def rosePetalHom (α : Type w) : (rose α).GraphPresentation ∅ →* FreeGroup α :=
  GraphPresentation.lift (rosePetalWord α) (fun _ h => (Set.notMem_empty _ h).elim)
    rosePetalWord_rev

private theorem rosePetalHom_of_true {α : Type w} (a : α) :
    rosePetalHom α (PresentedGroup.of (a, true)) = FreeGroup.of a :=
  (GraphPresentation.lift_of (rosePetalWord α) _ _ (a, true)).trans (rosePetalWord_true a)

private theorem rosePetalHom_of_false {α : Type w} (a : α) :
    rosePetalHom α (PresentedGroup.of (a, false)) = (FreeGroup.of a)⁻¹ :=
  (GraphPresentation.lift_of (rosePetalWord α) _ _ (a, false)).trans (rosePetalWord_false a)

/-- The fundamental group of a rose is free on its petals: the dart `(a, true)` of the petal
`a` is the free generator `a` and the reverse dart `(a, false)` is its inverse. The spanning
tree of a rose has no darts. -/
def roseGraphPresentationEquivFreeGroup (α : Type w) :
    (rose α).GraphPresentation ∅ ≃* FreeGroup α :=
  MonoidHom.toMulEquiv (rosePetalHom α)
    (FreeGroup.lift fun a => PresentedGroup.of (rels := (rose α).graphRelators ∅) (a, true))
    (PresentedGroup.ext fun e => by
      obtain ⟨a, _ | _⟩ := e
      · rw [MonoidHom.comp_apply, rosePetalHom_of_false, map_inv, FreeGroup.lift_apply_of]
        exact (GraphPresentation.of_rev (Γ := rose α) (a, true)).symm
      · rw [MonoidHom.comp_apply, rosePetalHom_of_true, FreeGroup.lift_apply_of,
          MonoidHom.id_apply])
    (FreeGroup.ext_hom _ _ fun a => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, rosePetalHom_of_true,
        MonoidHom.id_apply])

@[simp] theorem roseGraphPresentationEquivFreeGroup_of_true {α : Type w} (a : α) :
    roseGraphPresentationEquivFreeGroup α
      (PresentedGroup.of (rels := (rose α).graphRelators ∅) (a, true)) = FreeGroup.of a :=
  rosePetalHom_of_true a

@[simp] theorem roseGraphPresentationEquivFreeGroup_of_false {α : Type w} (a : α) :
    roseGraphPresentationEquivFreeGroup α
      (PresentedGroup.of (rels := (rose α).graphRelators ∅) (a, false)) = (FreeGroup.of a)⁻¹ :=
  rosePetalHom_of_false a

@[simp] theorem roseGraphPresentationEquivFreeGroup_symm_of {α : Type w} (a : α) :
    (roseGraphPresentationEquivFreeGroup α).symm (FreeGroup.of a) =
      PresentedGroup.of (rels := (rose α).graphRelators ∅) (a, true) := by
  rw [roseGraphPresentationEquivFreeGroup, MonoidHom.toMulEquiv_symm_apply,
    FreeGroup.lift_apply_of]

end TauCeti.SerreGraph
