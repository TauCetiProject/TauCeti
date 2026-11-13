/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.PathGroup
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
  the positive darts outside `T`, sending a dart generator to its signed coordinate
  `GraphOfGroups.π₁Tree.dartWord`.
* `TauCeti.SerreGraph.SpanningTree.pathGroupEquivGraphPresentation`: the isomorphism from the
  reduced path group.

## Main results

* `TauCeti.SerreGraph.SpanningTree.graphPresentation_reducedLoop_bijective`: every element of
  the presentation relative to a spanning tree is the dart word of exactly one reduced closed
  path.
* `TauCeti.SerreGraph.roseGraphPresentationEquivFreeGroup`: the rose has free fundamental group
  on its petals, the two darts of a petal giving a generator and its inverse.
* `TauCeti.GraphOfGroups.π₁Tree.roseEquivFreeGroup`: so does a graph of groups with trivial
  vertex groups over a rose, relative to its maximal tree.
* `TauCeti.SerreGraph.IsAcyclic.subsingleton_graphPresentation`: relative to any spanning tree,
  the presentation of an acyclic graph is trivial.

## References

* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2.
* J.-P. Serre, *Trees*, Chapter I, §2.3 and §3.1.
* I. Kapovich, A. Myasnikov, *Stallings foldings and subgroups of free groups*, §6, Lemma 6.1.
-/

public section

namespace TauCeti.SerreGraph

universe u w x y

variable (Γ : SerreGraph.{u, w})

/-- The relators of the presentation of a Serre graph by its darts killing a set `T` of darts:
`e * rev e` for every dart `e`, and `e` for every dart `e ∈ T`. For the darts of a spanning tree
they present the fundamental group of the graph. -/
def graphRelators (T : Set Γ.E) : Set (FreeGroup Γ.E) :=
  Set.range (fun e => FreeGroup.of e * FreeGroup.of (Γ.rev e)) ∪ FreeGroup.of '' T

variable {Γ} in
theorem mem_graphRelators_iff {T : Set Γ.E} {r : FreeGroup Γ.E} :
    r ∈ Γ.graphRelators T ↔
      (∃ e, FreeGroup.of e * FreeGroup.of (Γ.rev e) = r) ∨ ∃ e ∈ T, FreeGroup.of e = r :=
  Iff.rfl

/-- The group presented by the darts of a Serre graph killing a set `T` of darts: the
generators are the darts, a dart and its reverse are mutually inverse, and the darts of `T` are
trivial. For the darts of a spanning tree this is the fundamental group of the graph, the group
of reduced closed paths at a vertex. -/
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

section free

variable {O : Set Γ.E} (hO : Γ.IsOrientation O) (hT : ∀ e ∈ T, Γ.rev e ∈ T)

/-- For a set `T` of darts closed under reversal and an orientation `O`, the presentation by
darts killing `T` is free on the darts of `O \ T`; the generator of a dart of `O \ T`
corresponds to the free generator. For the darts of a spanning tree this is the fundamental
group of the graph, free on the positive edges outside the tree. -/
noncomputable def equivFreeGroup : Γ.GraphPresentation T ≃* FreeGroup ↥(O \ T) :=
  (equivTreePresentation T (GraphOfGroups.trivial Γ)).trans
    (GraphOfGroups.π₁Tree.equivFreeGroup _ hO hT)

/-- The free coordinate of a dart generator is the signed coordinate of the dart. -/
theorem equivFreeGroup_of_eq_dartWord (e : Γ.E) :
    equivFreeGroup hO hT (PresentedGroup.of e) = GraphOfGroups.π₁Tree.dartWord O T e := by
  simp [equivFreeGroup, GraphOfGroups.π₁Tree.equivFreeGroup_edge_eq_dartWord]

@[simp] theorem equivFreeGroup_of {e : Γ.E} (he : e ∈ O \ T) :
    equivFreeGroup hO hT (PresentedGroup.of e) = FreeGroup.of ⟨e, he⟩ := by
  rw [equivFreeGroup_of_eq_dartWord, GraphOfGroups.π₁Tree.dartWord_of_mem he]

@[simp] theorem equivFreeGroup_symm_of (e : ↥(O \ T)) :
    (equivFreeGroup hO hT).symm (FreeGroup.of e) = PresentedGroup.of e.1 := by
  simp [equivFreeGroup]

end free

end GraphPresentation

namespace SpanningTree

variable {Γ} (T : Γ.SpanningTree) (v : Γ.V)

/-- Reduced closed paths at a vertex are canonically isomorphic to the presentation of the
fundamental group relative to a spanning tree: a path is sent to the product of its darts, and
a dart generator corresponds to its based tree loop. -/
noncomputable def pathGroupEquivGraphPresentation :
    PathGroup Γ v ≃* Γ.GraphPresentation T.darts :=
  (T.pathGroupEquivTreePresentation v (GraphOfGroups.trivial Γ)).trans
    (GraphPresentation.equivTreePresentation T.darts (GraphOfGroups.trivial Γ)).symm

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

/-- The positive darts of a rose are its petals. -/
private def rosePositiveDartEquiv (α : Type w) :
    ↥({e : (rose α).E | e.2 = true} \ (∅ : Set (rose α).E)) ≃ α where
  toFun e := e.1.1
  invFun a := ⟨(a, true), rfl, Set.notMem_empty _⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, hb, -⟩
    obtain rfl : b = true := hb
    rfl
  right_inv _ := rfl

/-- The fundamental group of a rose is free on its petals: the dart `(a, true)` of the petal
`a` is the free generator `a` and the reverse dart `(a, false)` is its inverse. The spanning
tree of a rose has no darts. -/
noncomputable def roseGraphPresentationEquivFreeGroup (α : Type w) :
    (rose α).GraphPresentation ∅ ≃* FreeGroup α :=
  (GraphPresentation.equivFreeGroup (rose_isOrientation α) (by simp)).trans
    (FreeGroup.freeGroupCongr (rosePositiveDartEquiv α))

@[simp] theorem roseGraphPresentationEquivFreeGroup_of_true {α : Type w} (a : α) :
    roseGraphPresentationEquivFreeGroup α
      (PresentedGroup.of (rels := (rose α).graphRelators ∅) (a, true)) = FreeGroup.of a := by
  have ha : ((a, true) : (rose α).E) ∈ {e : (rose α).E | e.2 = true} \ ∅ :=
    ⟨rfl, Set.notMem_empty _⟩
  simp [roseGraphPresentationEquivFreeGroup, GraphPresentation.equivFreeGroup_of _ _ ha,
    rosePositiveDartEquiv]

@[simp] theorem roseGraphPresentationEquivFreeGroup_of_false {α : Type w} (a : α) :
    roseGraphPresentationEquivFreeGroup α
      (PresentedGroup.of (rels := (rose α).graphRelators ∅) (a, false)) = (FreeGroup.of a)⁻¹ := by
  rw [← roseGraphPresentationEquivFreeGroup_of_true, ← map_inv]
  exact congrArg _ (GraphPresentation.of_rev (Γ := rose α) (a, true))

@[simp] theorem roseGraphPresentationEquivFreeGroup_symm_of {α : Type w} (a : α) :
    (roseGraphPresentationEquivFreeGroup α).symm (FreeGroup.of a) =
      PresentedGroup.of (rels := (rose α).graphRelators ∅) (a, true) := by
  rw [MulEquiv.symm_apply_eq, roseGraphPresentationEquivFreeGroup_of_true]

end TauCeti.SerreGraph

namespace TauCeti.GraphOfGroups.π₁Tree

universe v w x

variable {α : Type v} (𝔸 : GraphOfGroups.{0, v, w, x} (SerreGraph.rose α))
  [∀ a, Subsingleton (𝔸.vertexGroup a)] (T : (SerreGraph.rose α).SpanningTree)

/-- A graph of groups with trivial vertex groups over the rose with petals `α` has fundamental
group, relative to its maximal tree, free on the petals: the positive dart `(a, true)` of the
petal `a` corresponds to the generator `a`. For the rose with `n` petals this is the free group
of rank `n`. Under the tree presentation it agrees with the free basis of the fundamental group
of the rose itself, `SerreGraph.roseGraphPresentationEquivFreeGroup`. -/
noncomputable def roseEquivFreeGroup : π₁Tree 𝔸 T.darts ≃* FreeGroup α :=
  -- The maximal tree of a rose has no darts, so it kills the same darts as the empty set.
  ((SerreGraph.GraphPresentation.equivTreePresentation T.darts 𝔸).symm.trans
    (PresentedGroup.equivOfNormalClosureEq (by
      rw [Subsingleton.elim T (SerreGraph.roseTree α), SerreGraph.roseTree_darts]))).trans
    (SerreGraph.roseGraphPresentationEquivFreeGroup α)

/-- A dart of the rose goes to the image of its generator in the presentation of the rose by its
darts. -/
private theorem roseEquivFreeGroup_edge (e : (SerreGraph.rose α).E) :
    roseEquivFreeGroup 𝔸 T (edge T.darts e) =
      SerreGraph.roseGraphPresentationEquivFreeGroup α (PresentedGroup.of e) := by
  simp only [roseEquivFreeGroup, MulEquiv.trans_apply,
    SerreGraph.GraphPresentation.equivTreePresentation_symm_edge]
  exact congrArg _ (PresentedGroup.equivOfNormalClosureEq_mk _ _)

@[simp] theorem roseEquivFreeGroup_edge_true (a : α) :
    roseEquivFreeGroup 𝔸 T (edge T.darts (a, true)) = FreeGroup.of a :=
  (roseEquivFreeGroup_edge 𝔸 T _).trans (SerreGraph.roseGraphPresentationEquivFreeGroup_of_true a)

@[simp] theorem roseEquivFreeGroup_edge_false (a : α) :
    roseEquivFreeGroup 𝔸 T (edge T.darts (a, false)) = (FreeGroup.of a)⁻¹ :=
  (roseEquivFreeGroup_edge 𝔸 T _).trans (SerreGraph.roseGraphPresentationEquivFreeGroup_of_false a)

@[simp] theorem roseEquivFreeGroup_symm_of (a : α) :
    (roseEquivFreeGroup 𝔸 T).symm (FreeGroup.of a) = edge T.darts (a, true) := by
  rw [MulEquiv.symm_apply_eq, roseEquivFreeGroup_edge_true]

end TauCeti.GraphOfGroups.π₁Tree
