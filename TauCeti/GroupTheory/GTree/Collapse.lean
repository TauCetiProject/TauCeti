/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Collapse
public import TauCeti.GroupTheory.GTree.Basic

/-!
# Collapses of group actions on trees

Let `T` be a `G`-tree and `S` a `G`-invariant set of edges, given as a reversal-closed set of
darts. The collapse `T.collapse S hS hG` is the `G`-tree obtained by contracting every edge of
`S` to a point, with the induced action. The collapse map `T.collapseHom S hS hG` on vertices is
equivariant and surjective, and an equivariant map agreeing at the endpoints of every edge of `S`
factors through it. Its fibres are the vertex sets of the connected components of the spanning
forest `T.restrict S hS`, which keeps every vertex of `T`; they are subtrees of `T`, and more
generally the preimage of a convex set of vertices of the collapse is convex. Hence a collapse of a
minimal tree is minimal. The stabilizer of a vertex of the collapse is the stabilizer of the
subtree collapsed to it, so `T` dominates its collapse. The remaining darts keep their
stabilizers, so a collapse of a tree relative to families of subgroups is relative to the same
families.

The collapse map is injective exactly when no edge is collapsed, and a collapse identifying no
vertices lies in the deformation space of `T`. A collapse has a single vertex, and no dart,
exactly when every edge is collapsed; such a collapse is dominated by every `G`-tree. This is what
happens to a tree with one orbit of edges, such as the tree of an amalgam or of an HNN extension,
when its edge is collapsed.

## Main declarations

* `TauCeti.GTree.collapse`: the collapse of a `G`-tree along an invariant set of edges.
* `TauCeti.GTree.collapseHom`: the collapse map, an equivariant map of vertices, with the
  factorisation `TauCeti.GTree.collapseLift`.
* `TauCeti.GTree.isConvex_collapseHom_preimage`: preimages of convex sets under the collapse map
  are convex.
* `TauCeti.GTree.stabilizer_collapse_vertex`: vertex stabilizers of the collapse.
* `TauCeti.GTree.dominates_collapse`: a tree dominates its collapses.
* `TauCeti.GTree.IsMinimal.collapse`: a collapse of a minimal tree is minimal.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.4.1
  (collapse maps) and the proof of Lemma 2.11.
-/

public section

universe u v u' v' w

namespace TauCeti

open SerreGraph _root_.MulAction

open scoped Pointwise

namespace GTree

variable {G : Type w} [Group G] (T : GTree.{u, v} G) (S : Set T.E)
  (hS : ∀ e ∈ S, T.rev e ∈ S) (hG : ∀ g : G, ∀ e ∈ S, g • e ∈ S)

/-- The action of `G` on the collapse of a `G`-tree along a `G`-invariant set of edges. -/
def collapseAction : G →* (T.toSerreGraph.collapse S hS).Aut where
  toFun g := (T.action g).collapse hS fun e =>
    ⟨fun h => by simpa [← smul_dart_def] using hG g⁻¹ _ h, hG g e⟩
  map_one' := by
    simp only [map_one]
    exact Aut.collapse_one hS _
  map_mul' g h := by
    simp only [map_mul]
    exact Aut.collapse_mul hS _ _ _ _ _

@[simp] theorem collapseAction_smul_collapseVertex (g : G) (a : T.V) :
    T.collapseAction S hS hG g • T.toSerreGraph.collapseVertex S hS a =
      T.toSerreGraph.collapseVertex S hS (g • a) :=
  Aut.collapse_smul_collapseVertex hS (T.action g) _ a

@[simp] theorem collapseAction_smul_val (g : G) (e : (T.toSerreGraph.collapse S hS).E) :
    (T.collapseAction S hS hG g • e).1 = g • e.1 :=
  Aut.collapse_smul_val hS (T.action g) _ e

/-- The collapse of a `G`-tree along a `G`-invariant set of edges, given as a reversal-closed set
`S` of darts: every edge of `S` is contracted to a point, and `G` acts on the resulting tree. -/
@[expose] def collapse : GTree.{u, v} G where
  toSerreGraph := T.toSerreGraph.collapse S hS
  isTree := T.isTree.collapse S hS
  action := T.collapseAction S hS hG
  action_smul_ne_rev g e h :=
    T.smul_ne_rev g e.1 ((T.collapseAction_smul_val S hS hG g e).symm.trans (congrArg (·.1) h))

/-- The collapse map of a `G`-tree: the equivariant map sending a vertex to its image in the
collapse. -/
def collapseHom : T.V →[G] (T.collapse S hS hG).V where
  toFun := T.toSerreGraph.collapseVertex S hS
  map_smul' g v := (T.collapseAction_smul_collapseVertex S hS hG g v).symm

theorem coe_collapseHom :
    ⇑(T.collapseHom S hS hG) = T.toSerreGraph.collapseVertex S hS := (rfl)

theorem collapseHom_surjective : Function.Surjective (T.collapseHom S hS hG) :=
  T.toSerreGraph.collapseVertex_surjective S hS

variable {T S} in
/-- Two vertices have the same image in the collapse exactly when they are joined by a path of
collapsed darts. -/
theorem collapseHom_eq_iff {a b : T.V} :
    T.collapseHom S hS hG a = T.collapseHom S hS hG b ↔
      ∃ p : T.Path a b, ∀ e ∈ Path.darts T.toSerreGraph p, e ∈ S :=
  collapseVertex_eq_iff hS

@[simp] theorem collapse_src (e : (T.collapse S hS hG).E) :
    (T.collapse S hS hG).src e = T.collapseHom S hS hG (T.src e.1) :=
  SerreGraph.collapse_src _ S hS e

@[simp] theorem collapse_tgt (e : (T.collapse S hS hG).E) :
    (T.collapse S hS hG).tgt e = T.collapseHom S hS hG (T.tgt e.1) :=
  SerreGraph.collapse_tgt _ S hS e

@[simp] theorem collapse_rev_val (e : (T.collapse S hS hG).E) :
    ((T.collapse S hS hG).rev e).1 = T.rev e.1 := (rfl)

/-- The action on the darts of the collapse is the action on the darts of the tree. -/
@[simp] theorem collapse_smul_val (g : G) (e : (T.collapse S hS hG).E) :
    (g • e).1 = g • e.1 :=
  T.collapseAction_smul_val S hS hG g e

/-- A tree dominates each of its collapses. -/
theorem dominates_collapse : T.Dominates (T.collapse S hS hG) :=
  dominates_iff_nonempty.mpr ⟨T.collapseHom S hS hG⟩

variable {T S} in
/-- The endpoints of a collapsed dart have the same image in the collapse. -/
theorem collapseHom_src_eq_tgt {e : T.E} (he : e ∈ S) :
    T.collapseHom S hS hG (T.src e) = T.collapseHom S hS hG (T.tgt e) :=
  collapseVertex_src_eq_tgt hS he

variable {T S} in
/-- An equivariant map on vertices taking the same value at the endpoints of every collapsed dart
factors through the collapse map. -/
def collapseLift {X : Type*} [MulAction G X] (f : T.V →[G] X)
    (hf : ∀ e ∈ S, f (T.src e) = f (T.tgt e)) : (T.collapse S hS hG).V →[G] X where
  toFun := SerreGraph.collapseLift hS f hf
  map_smul' g x := by
    obtain ⟨a, rfl⟩ := T.collapseHom_surjective S hS hG x
    rw [← map_smul, coe_collapseHom, SerreGraph.collapseLift_collapseVertex,
      SerreGraph.collapseLift_collapseVertex, map_smul, id_eq]

variable {T S} in
@[simp] theorem collapseLift_collapseHom {X : Type*} [MulAction G X] (f : T.V →[G] X)
    (hf : ∀ e ∈ S, f (T.src e) = f (T.tgt e)) (a : T.V) :
    collapseLift hS hG f hf (T.collapseHom S hS hG a) = f a :=
  SerreGraph.collapseLift_collapseVertex hS f hf a

variable {T S} in
@[simp] theorem collapseLift_comp_collapseHom {X : Type*} [MulAction G X] (f : T.V →[G] X)
    (hf : ∀ e ∈ S, f (T.src e) = f (T.tgt e)) :
    (collapseLift hS hG f hf).comp (T.collapseHom S hS hG) = f :=
  MulActionHom.ext (collapseLift_collapseHom hS hG f hf)

variable {T S} in
/-- The preimage of a convex set of vertices of a collapse is a convex set of vertices of the
tree. -/
theorem isConvex_collapseHom_preimage {C : Set (T.collapse S hS hG).V}
    (hC : (T.collapse S hS hG).IsConvex C) : T.IsConvex (T.collapseHom S hS hG ⁻¹' C) :=
  (IsTree.isAcyclic _ T.isTree).isConvex_collapseVertex_preimage hS hC

/-- The vertices of a tree over a vertex of a collapse form a convex set: the fibres of the
collapse map are subtrees. -/
theorem isConvex_collapseHom_preimage_singleton (x : (T.collapse S hS hG).V) :
    T.IsConvex (T.collapseHom S hS hG ⁻¹' {x}) :=
  (IsTree.isAcyclic _ T.isTree).isConvex_collapseVertex_preimage_singleton S hS x

variable {T} in
/-- A collapse of a minimal tree is minimal. -/
theorem IsMinimal.collapse (h : T.IsMinimal) : (T.collapse S hS hG).IsMinimal := by
  refine isMinimal_iff.mpr fun C hC hCconv hCG => ?_
  have hpre := isMinimal_iff.mp h (T.collapseHom S hS hG ⁻¹' C)
    (hC.preimage (T.collapseHom_surjective S hS hG)) (isConvex_collapseHom_preimage hS hG hCconv)
    fun g v hv => by
      rw [Set.mem_preimage, map_smul]
      exact hCG g _ hv
  exact (T.collapseHom_surjective S hS hG).preimage_injective (hpre.trans Set.preimage_univ.symm)

/-- The stabilizer of a vertex of a collapse is the stabilizer of the subtree collapsed to it. -/
theorem stabilizer_collapse_vertex (x : (T.collapse S hS hG).V) :
    stabilizer G x = stabilizer G (T.collapseHom S hS hG ⁻¹' {x}) := by
  rw [MulAction.stabilizer_preimage_of_surjective (T.collapseHom_surjective S hS hG),
    stabilizer_singleton]

/-- A dart of a collapse has the same stabilizer as in the tree. -/
@[simp] theorem stabilizer_collapse_dart (e : (T.collapse S hS hG).E) :
    stabilizer G e = stabilizer G e.1 := by
  refine Subgroup.ext fun g => ?_
  rw [mem_stabilizer_iff, mem_stabilizer_iff]
  exact ⟨fun h => (T.collapse_smul_val S hS hG g e).symm.trans (congrArg (·.1) h),
    fun h => Subtype.ext ((T.collapse_smul_val S hS hG g e).trans h)⟩

variable {T} in
/-- A collapse of a tree relative to families of subgroups is relative to the same families. -/
theorem IsRelative.collapse {𝒜 ℋ : Set (Subgroup G)} (h : T.IsRelative 𝒜 ℋ) :
    (T.collapse S hS hG).IsRelative 𝒜 ℋ :=
  isRelative_iff.mpr ⟨fun e => by rw [stabilizer_collapse_dart]; exact h.stabilizer_mem e.1,
    fun _ hH => (T.dominates_collapse S hS hG).isEllipticSubgroup (h.isEllipticSubgroup hH)⟩

/-! ### The extreme collapses -/

/-- The collapse map of a tree is injective exactly when no edge is collapsed. -/
theorem collapseHom_injective_iff : Function.Injective (T.collapseHom S hS hG) ↔ S = ∅ :=
  (IsTree.isAcyclic _ T.isTree).collapseVertex_injective_iff S hS

/-- Collapsing no edge identifies no vertices. -/
theorem collapseHom_empty_injective (hS : ∀ e ∈ (∅ : Set T.E), T.rev e ∈ (∅ : Set T.E))
    (hG : ∀ g : G, ∀ e ∈ (∅ : Set T.E), g • e ∈ (∅ : Set T.E)) :
    Function.Injective (T.collapseHom ∅ hS hG) :=
  (T.collapseHom_injective_iff ∅ hS hG).mpr rfl

variable {T S} in
/-- A collapse identifying no vertices dominates the original tree. -/
theorem collapse_dominates_of_injective (h : Function.Injective (T.collapseHom S hS hG)) :
    (T.collapse S hS hG).Dominates T :=
  dominates_iff_nonempty.mpr
    ⟨collapseLift hS hG (.id G) fun _ he => h (collapseHom_src_eq_tgt hS hG he)⟩

/-- Collapsing no edge gives a tree dominating the original tree. -/
theorem collapse_empty_dominates (hS : ∀ e ∈ (∅ : Set T.E), T.rev e ∈ (∅ : Set T.E))
    (hG : ∀ g : G, ∀ e ∈ (∅ : Set T.E), g • e ∈ (∅ : Set T.E)) :
    (T.collapse ∅ hS hG).Dominates T :=
  collapse_dominates_of_injective hS hG (T.collapseHom_empty_injective hS hG)

variable {T S} in
/-- A collapse identifying no vertices lies in the deformation space of the original tree. -/
theorem collapse_sameDeformationSpace_of_injective
    (h : Function.Injective (T.collapseHom S hS hG)) :
    (T.collapse S hS hG).SameDeformationSpace T :=
  sameDeformationSpace_iff.mpr ⟨collapse_dominates_of_injective hS hG h,
    T.dominates_collapse S hS hG⟩

/-- Collapsing no edge gives a tree in the same deformation space. -/
theorem collapse_empty_sameDeformationSpace
    (hS : ∀ e ∈ (∅ : Set T.E), T.rev e ∈ (∅ : Set T.E))
    (hG : ∀ g : G, ∀ e ∈ (∅ : Set T.E), g • e ∈ (∅ : Set T.E)) :
    (T.collapse ∅ hS hG).SameDeformationSpace T :=
  collapse_sameDeformationSpace_of_injective hS hG (T.collapseHom_empty_injective hS hG)

/-- A collapse of a tree has a single vertex exactly when every edge is collapsed. -/
theorem subsingleton_collapse_iff : Subsingleton (T.collapse S hS hG).V ↔ S = Set.univ :=
  IsTree.subsingleton_collapse_iff S hS T.isTree

/-- Collapsing every edge of a tree leaves a single vertex. -/
instance subsingleton_collapse_univ
    (hS : ∀ e ∈ (Set.univ : Set T.E), T.rev e ∈ (Set.univ : Set T.E))
    (hG : ∀ g : G, ∀ e ∈ (Set.univ : Set T.E), g • e ∈ (Set.univ : Set T.E)) :
    Subsingleton (T.collapse Set.univ hS hG).V :=
  (T.subsingleton_collapse_iff _ hS hG).mpr rfl

/-- A collapse of a tree has no dart exactly when every edge is collapsed. -/
theorem isEmpty_collapse_dart_iff : IsEmpty (T.collapse S hS hG).E ↔ S = Set.univ :=
  T.toSerreGraph.isEmpty_collapse_dart_iff S hS

/-- Collapsing every edge of a tree leaves no dart. -/
instance isEmpty_collapse_univ_dart
    (hS : ∀ e ∈ (Set.univ : Set T.E), T.rev e ∈ (Set.univ : Set T.E))
    (hG : ∀ g : G, ∀ e ∈ (Set.univ : Set T.E), g • e ∈ (Set.univ : Set T.E)) :
    IsEmpty (T.collapse Set.univ hS hG).E :=
  (T.isEmpty_collapse_dart_iff _ hS hG).mpr rfl

variable {T S} in
/-- A collapse of every edge is dominated by every `G`-tree. -/
theorem dominates_collapse_of_eq_univ (T' : GTree.{u', v'} G) (h : S = Set.univ) :
    T'.Dominates (T.collapse S hS hG) :=
  have := (T.subsingleton_collapse_iff S hS hG).mpr h
  T'.dominates_of_subsingleton

/-- The tree obtained by collapsing every edge is dominated by every `G`-tree. -/
theorem dominates_collapse_univ (T' : GTree.{u', v'} G)
    (hS : ∀ e ∈ (Set.univ : Set T.E), T.rev e ∈ (Set.univ : Set T.E))
    (hG : ∀ g : G, ∀ e ∈ (Set.univ : Set T.E), g • e ∈ (Set.univ : Set T.E)) :
    T'.Dominates (T.collapse Set.univ hS hG) :=
  dominates_collapse_of_eq_univ hS hG T' rfl

end GTree

end TauCeti
