/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Lattice.Bounded
public import TauCeti.Combinatorics.Network.Basic
public import TauCeti.Combinatorics.Network.Walk
public import TauCeti.Combinatorics.Quiver.Reachable

/-!
# Subnetworks

A subnetwork of a bounded directed network selects vertices and original arrow identities, with
every selected arrow required to have selected endpoints. Its own vertex type is the selected
vertex subtype, and its bounds are inherited from the ambient network.

This file supplies the elementary set operations used to build subnetworks: induced subnetworks,
restriction and deletion of vertices or arrows, singleton and empty subnetworks, and unions inside
a fixed ambient network. It defines reachability through selected arrows, proves its equivalence
with walks in the subnetwork's own arrow family, and characterizes strong connectivity in those
terms. It also defines the subnetwork traced by a directed walk. In particular, isolated selected
vertices remain visible under every operation that does not delete them.
-/

public section

universe u v w

namespace TauCeti.Network

variable {K : Type w} {V : Type u} [LE K] (N : Network K V)

/-- A subnetwork selects ambient vertices and ambient arrows whose endpoints are both selected. -/
structure Subnetwork where
  /-- The selected ambient vertices. -/
  vertexSet : Set V
  /-- The selected ambient arrows, retaining their endpoints and identities. -/
  arrowSet : Set (Σ x y, N.Hom x y)
  /-- The source of every selected arrow is selected. -/
  source_mem : ∀ a ∈ arrowSet, a.1 ∈ vertexSet
  /-- The target of every selected arrow is selected. -/
  target_mem : ∀ a ∈ arrowSet, a.2.1 ∈ vertexSet

namespace Subnetwork

variable {N}

/-- Two subnetworks are equal when they select the same vertices and arrows. -/
@[ext]
theorem ext {S T : N.Subnetwork} (hV : S.vertexSet = T.vertexSet)
    (hA : S.arrowSet = T.arrowSet) : S = T := by
  cases S
  cases T
  cases hV
  cases hA
  rfl

/-- The arrow family of a subnetwork, indexed by its selected vertex subtype. -/
abbrev Hom (S : N.Subnetwork) (x y : ↥S.vertexSet) :=
  {e : N.Hom x.1 y.1 // (⟨x.1, y.1, e⟩ : Σ x y, N.Hom x y) ∈ S.arrowSet}

/-! ### Reachability -/

/-- Ambient vertices `y` are reachable from `x` inside a subnetwork when a directed walk avoiding
the complement of its selected arrows joins them. The endpoints need not be selected for this
definition; `isStronglyConnected_iff` below restricts them to the subnetwork's vertex set. -/
abbrev Reachable (S : N.Subnetwork) (x y : V) : Prop :=
  ReachableWithout S.arrowSetᶜ x y

/-- Reachability inside a subnetwork is reachability avoiding the complement of its selected
arrows. -/
theorem reachable_def (S : N.Subnetwork) (x y : V) :
    S.Reachable x y ↔ ReachableWithout S.arrowSetᶜ x y :=
  Iff.rfl

/-- A directed walk in a subnetwork gives reachability between its ambient endpoints. -/
theorem reachable_of_nonempty_arrowWalk (S : N.Subnetwork) {x y : ↥S.vertexSet}
    (h : Nonempty (ArrowWalk S.Hom x y)) : S.Reachable x.1 y.1 := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ReachableWithout.refl S.arrowSetᶜ _
  | cons p e ih => exact ih.tail e.1 (by simpa using e.2)

/-- Reachability between selected ambient vertices lifts to a directed walk in the subnetwork. -/
theorem nonempty_arrowWalk_of_reachable (S : N.Subnetwork) {x y : V}
    (hx : x ∈ S.vertexSet) (hy : y ∈ S.vertexSet) (h : S.Reachable x y) :
    Nonempty (ArrowWalk S.Hom ⟨x, hx⟩ ⟨y, hy⟩) := by
  rw [S.reachable_def] at h
  rw [reachableWithout_def] at h
  obtain ⟨p, hp⟩ := h
  replace hp : ∀ a ∈ p.arrows, a ∈ S.arrowSet := by
    intro a ha
    simpa using hp a ha
  induction p generalizing hx with
  | nil => exact ⟨ArrowWalk.nil _⟩
  | @cons y z p e ih =>
    have he : (⟨y, z, e⟩ : Σ x y, N.Hom x y) ∈ S.arrowSet := hp _ (by simp)
    have hy' : y ∈ S.vertexSet := S.source_mem ⟨y, z, e⟩ he
    obtain ⟨q⟩ := ih hx hy' (fun a ha ↦ hp a (by simp [ha]))
    exact ⟨q.cons ⟨e, he⟩⟩

/-- Reachability between selected ambient vertices is exactly the existence of a walk in the
subnetwork's own arrow family. -/
theorem reachable_iff_nonempty_arrowWalk (S : N.Subnetwork) (x y : ↥S.vertexSet) :
    S.Reachable x.1 y.1 ↔ Nonempty (ArrowWalk S.Hom x y) :=
  ⟨nonempty_arrowWalk_of_reachable S x.2 y.2,
    reachable_of_nonempty_arrowWalk S⟩

/-- A subnetwork is strongly connected exactly when every ordered pair of its selected ambient
vertices is reachable using selected arrows. -/
theorem isStronglyConnected_iff (S : N.Subnetwork) :
    @Quiver.IsStronglyConnected ↥S.vertexSet ⟨S.Hom⟩ ↔
      ∀ x ∈ S.vertexSet, ∀ y ∈ S.vertexSet, S.Reachable x y := by
  constructor
  · intro h x hx y hy
    exact (S.reachable_iff_nonempty_arrowWalk ⟨x, hx⟩ ⟨y, hy⟩).2 (h _ _)
  · intro h x y
    exact (S.reachable_iff_nonempty_arrowWalk x y).1 (h x.1 x.2 y.1 y.2)

/-- A subnetwork as a bounded network on its selected vertex subtype, with inherited bounds.

This definition is exposed because its dependent arrow family must reduce when subnetwork
assignments and walks are elaborated. -/
@[expose]
def toNetwork (S : N.Subnetwork) : Network K ↥S.vertexSet where
  Hom := S.Hom
  lower := fun {_ _} (e : S.Hom _ _) ↦ N.lower e.val
  upper := fun {_ _} (e : S.Hom _ _) ↦ N.upper e.val
  lower_le_upper := fun e ↦ N.lower_le_upper e.val

@[simp]
theorem toNetwork_Hom (S : N.Subnetwork) (x y : ↥S.vertexSet) :
    S.toNetwork.Hom x y = S.Hom x y := rfl

@[simp]
theorem toNetwork_lower (S : N.Subnetwork) {x y : ↥S.vertexSet} (e : S.Hom x y) :
    S.toNetwork.lower e = N.lower e.val := rfl

@[simp]
theorem toNetwork_upper (S : N.Subnetwork) {x y : ↥S.vertexSet} (e : S.Hom x y) :
    S.toNetwork.upper e = N.upper e.val := rfl

/-- The inclusion of a subnetwork's vertices into its ambient vertex type. -/
def vertexEmbedding (S : N.Subnetwork) : ↥S.vertexSet ↪ V :=
  Function.Embedding.subtype _

@[simp]
theorem vertexEmbedding_apply (S : N.Subnetwork) (x : ↥S.vertexSet) :
    S.vertexEmbedding x = x.1 := (rfl)

/-- The inclusion of a subnetwork arrow into the corresponding ambient arrow type. -/
def arrowEmbedding (S : N.Subnetwork) (x y : ↥S.vertexSet) : S.Hom x y ↪ N.Hom x.1 y.1 :=
  Function.Embedding.subtype _

@[simp]
theorem arrowEmbedding_apply (S : N.Subnetwork) {x y : ↥S.vertexSet} (e : S.Hom x y) :
    S.arrowEmbedding x y e = e.1 := (rfl)

/-! ### Order and union -/

instance : LE N.Subnetwork where
  le S T := S.vertexSet ⊆ T.vertexSet ∧ S.arrowSet ⊆ T.arrowSet

theorem le_def {S T : N.Subnetwork} :
    S ≤ T ↔ S.vertexSet ⊆ T.vertexSet ∧ S.arrowSet ⊆ T.arrowSet :=
  Iff.rfl

instance : PartialOrder N.Subnetwork where
  le_refl S := ⟨Set.Subset.rfl, Set.Subset.rfl⟩
  le_trans _ _ _ hST hTU := ⟨hST.1.trans hTU.1, hST.2.trans hTU.2⟩
  le_antisymm S T hST hTS :=
    ext (Set.Subset.antisymm hST.1 hTS.1) (Set.Subset.antisymm hST.2 hTS.2)

/-- Reachability is preserved when the selected vertices and arrows are enlarged. -/
theorem Reachable.mono {S T : N.Subnetwork} (hST : S ≤ T) {x y : V}
    (h : S.Reachable x y) : T.Reachable x y :=
  ReachableWithout.mono (Set.compl_subset_compl.2 hST.2) h

/-- Inclusion of the vertex type of a smaller subnetwork into that of a larger one.

This definition is exposed because its values index the codomain of `arrowEmbeddingOfLE`. -/
@[expose]
def vertexEmbeddingOfLE {S T : N.Subnetwork} (h : S ≤ T) : ↥S.vertexSet ↪ ↥T.vertexSet where
  toFun x := ⟨x.1, h.1 x.2⟩
  inj' x y hxy := by
    apply Subtype.ext
    exact congrArg (fun z : ↥T.vertexSet ↦ z.1) hxy

@[simp]
theorem vertexEmbeddingOfLE_apply {S T : N.Subnetwork} (h : S ≤ T) (x : ↥S.vertexSet) :
    (vertexEmbeddingOfLE h x).1 = x.1 := rfl

/-- Inclusion of an arrow type of a smaller subnetwork into the corresponding arrow type of a
larger one. -/
def arrowEmbeddingOfLE {S T : N.Subnetwork} (h : S ≤ T) (x y : ↥S.vertexSet) :
    S.Hom x y ↪ T.Hom (vertexEmbeddingOfLE h x) (vertexEmbeddingOfLE h y) where
  toFun e := ⟨e.1, h.2 e.2⟩
  inj' e f hef := by
    apply Subtype.ext
    exact congrArg
      (fun z : T.Hom (vertexEmbeddingOfLE h x) (vertexEmbeddingOfLE h y) ↦ z.1) hef

@[simp]
theorem arrowEmbeddingOfLE_apply {S T : N.Subnetwork} (h : S ≤ T) {x y : ↥S.vertexSet}
    (e : S.Hom x y) : (arrowEmbeddingOfLE h x y e).1 = e.1 := (rfl)

/-- The union of two subnetworks inside the same ambient network. -/
def union (S T : N.Subnetwork) : N.Subnetwork where
  vertexSet := S.vertexSet ∪ T.vertexSet
  arrowSet := S.arrowSet ∪ T.arrowSet
  source_mem a ha := ha.elim (fun h ↦ Or.inl (S.source_mem a h))
    (fun h ↦ Or.inr (T.source_mem a h))
  target_mem a ha := ha.elim (fun h ↦ Or.inl (S.target_mem a h))
    (fun h ↦ Or.inr (T.target_mem a h))

@[simp]
theorem vertexSet_union (S T : N.Subnetwork) :
    (S.union T).vertexSet = S.vertexSet ∪ T.vertexSet := (rfl)

@[simp]
theorem arrowSet_union (S T : N.Subnetwork) :
    (S.union T).arrowSet = S.arrowSet ∪ T.arrowSet := (rfl)

theorem le_union_left (S T : N.Subnetwork) : S ≤ S.union T :=
  ⟨Set.subset_union_left, Set.subset_union_left⟩

theorem le_union_right (S T : N.Subnetwork) : T ≤ S.union T :=
  ⟨Set.subset_union_right, Set.subset_union_right⟩

theorem union_le {S T U : N.Subnetwork} (hS : S ≤ U) (hT : T ≤ U) : S.union T ≤ U :=
  ⟨Set.union_subset hS.1 hT.1, Set.union_subset hS.2 hT.2⟩

instance : SemilatticeSup N.Subnetwork where
  sup := union
  le_sup_left := le_union_left
  le_sup_right := le_union_right
  sup_le := fun _ _ _ ↦ union_le

@[simp]
theorem sup_vertexSet (S T : N.Subnetwork) : (S ⊔ T).vertexSet = S.vertexSet ∪ T.vertexSet :=
  vertexSet_union S T

@[simp]
theorem sup_arrowSet (S T : N.Subnetwork) : (S ⊔ T).arrowSet = S.arrowSet ∪ T.arrowSet :=
  arrowSet_union S T

/-- The intersection of two subnetworks inside the same ambient network. -/
def inter (S T : N.Subnetwork) : N.Subnetwork where
  vertexSet := S.vertexSet ∩ T.vertexSet
  arrowSet := S.arrowSet ∩ T.arrowSet
  source_mem a ha := ⟨S.source_mem a ha.1, T.source_mem a ha.2⟩
  target_mem a ha := ⟨S.target_mem a ha.1, T.target_mem a ha.2⟩

@[simp]
theorem vertexSet_inter (S T : N.Subnetwork) :
    (S.inter T).vertexSet = S.vertexSet ∩ T.vertexSet := (rfl)

@[simp]
theorem arrowSet_inter (S T : N.Subnetwork) :
    (S.inter T).arrowSet = S.arrowSet ∩ T.arrowSet := (rfl)

theorem inter_le_left (S T : N.Subnetwork) : S.inter T ≤ S :=
  ⟨Set.inter_subset_left, Set.inter_subset_left⟩

theorem inter_le_right (S T : N.Subnetwork) : S.inter T ≤ T :=
  ⟨Set.inter_subset_right, Set.inter_subset_right⟩

theorem le_inter {S T U : N.Subnetwork} (hST : S ≤ T) (hSU : S ≤ U) : S ≤ T.inter U :=
  ⟨fun _ h ↦ ⟨hST.1 h, hSU.1 h⟩, fun _ h ↦ ⟨hST.2 h, hSU.2 h⟩⟩

instance : SemilatticeInf N.Subnetwork where
  inf := inter
  inf_le_left := inter_le_left
  inf_le_right := inter_le_right
  le_inf := fun _ _ _ ↦ le_inter

@[simp]
theorem inf_vertexSet (S T : N.Subnetwork) : (S ⊓ T).vertexSet = S.vertexSet ∩ T.vertexSet :=
  vertexSet_inter S T

@[simp]
theorem inf_arrowSet (S T : N.Subnetwork) : (S ⊓ T).arrowSet = S.arrowSet ∩ T.arrowSet :=
  arrowSet_inter S T

/-! ### Basic constructions -/

/-- The empty subnetwork. -/
def _root_.TauCeti.Network.emptySubnetwork (N : Network K V) : N.Subnetwork where
  vertexSet := ∅
  arrowSet := ∅
  source_mem _ := False.elim
  target_mem _ := False.elim

@[simp]
theorem vertexSet_empty : N.emptySubnetwork.vertexSet = ∅ := (rfl)

@[simp]
theorem arrowSet_empty : N.emptySubnetwork.arrowSet = ∅ := (rfl)

instance : OrderBot N.Subnetwork where
  bot := N.emptySubnetwork
  bot_le S := by
    rw [le_def, vertexSet_empty, arrowSet_empty]
    exact ⟨Set.empty_subset _, Set.empty_subset _⟩

@[simp]
theorem vertexSet_bot : (⊥ : N.Subnetwork).vertexSet = ∅ :=
  vertexSet_empty

@[simp]
theorem arrowSet_bot : (⊥ : N.Subnetwork).arrowSet = ∅ :=
  arrowSet_empty

/-- The full ambient network as a subnetwork of itself. -/
def _root_.TauCeti.Network.fullSubnetwork (N : Network K V) : N.Subnetwork where
  vertexSet := Set.univ
  arrowSet := Set.univ
  source_mem _ _ := Set.mem_univ _
  target_mem _ _ := Set.mem_univ _

@[simp]
theorem vertexSet_full : N.fullSubnetwork.vertexSet = Set.univ := (rfl)

@[simp]
theorem arrowSet_full : N.fullSubnetwork.arrowSet = Set.univ := (rfl)

instance : OrderTop N.Subnetwork where
  top := N.fullSubnetwork
  le_top S := by
    rw [le_def, vertexSet_full, arrowSet_full]
    exact ⟨Set.subset_univ _, Set.subset_univ _⟩

@[simp]
theorem vertexSet_top : (⊤ : N.Subnetwork).vertexSet = Set.univ :=
  vertexSet_full

@[simp]
theorem arrowSet_top : (⊤ : N.Subnetwork).arrowSet = Set.univ :=
  arrowSet_full

/-- Reachability in the full subnetwork is ordinary reachability in the ambient arrow family. -/
@[simp]
theorem reachable_top_iff {x y : V} :
    (⊤ : N.Subnetwork).Reachable x y ↔ Nonempty (ArrowWalk N.Hom x y) := by
  rw [reachable_def, arrowSet_top, Set.compl_univ]
  exact reachableWithout_empty_iff

/-- The subnetwork induced by a set of ambient vertices. It retains every ambient arrow whose
two endpoints belong to the set. -/
def _root_.TauCeti.Network.inducedSubnetwork (N : Network K V) (W : Set V) : N.Subnetwork where
  vertexSet := W
  arrowSet := {a | a.1 ∈ W ∧ a.2.1 ∈ W}
  source_mem _ ha := ha.1
  target_mem _ ha := ha.2

@[simp]
theorem vertexSet_induced (W : Set V) : (N.inducedSubnetwork W).vertexSet = W := (rfl)

@[simp]
theorem mem_arrowSet_induced {W : Set V} {a : Σ x y, N.Hom x y} :
    a ∈ (N.inducedSubnetwork W).arrowSet ↔ a.1 ∈ W ∧ a.2.1 ∈ W :=
  Iff.rfl

/-- A subnetwork lies in the subnetwork induced by `W` exactly when its vertices lie in `W`. -/
@[simp]
theorem le_induced_iff {S : N.Subnetwork} {W : Set V} :
    S ≤ N.inducedSubnetwork W ↔ S.vertexSet ⊆ W := by
  constructor
  · exact fun h ↦ h.1
  · intro h
    refine ⟨h, ?_⟩
    intro a ha
    exact ⟨h (S.source_mem a ha), h (S.target_mem a ha)⟩

/-- The singleton subnetwork at `x`, with no arrows (including no ambient loops). -/
def _root_.TauCeti.Network.singletonSubnetwork (N : Network K V) (x : V) : N.Subnetwork where
  vertexSet := {x}
  arrowSet := ∅
  source_mem _ := False.elim
  target_mem _ := False.elim

@[simp]
theorem vertexSet_singleton (x : V) : (N.singletonSubnetwork x).vertexSet = {x} := (rfl)

@[simp]
theorem arrowSet_singleton (x : V) : (N.singletonSubnetwork x).arrowSet = ∅ := (rfl)

/-- A singleton subnetwork with no arrows is strongly connected. -/
theorem isStronglyConnected_singleton (x : V) :
    @Quiver.IsStronglyConnected ↥(N.singletonSubnetwork x).vertexSet
      ⟨(N.singletonSubnetwork x).Hom⟩ := by
  rw [isStronglyConnected_iff]
  intro a ha b hb
  simp only [vertexSet_singleton, Set.mem_singleton_iff] at ha hb
  subst a b
  exact .refl _ _

/-- Restrict a subnetwork to vertices belonging to `W`, deleting every arrow incident to a
discarded vertex. -/
def restrictVertices (S : N.Subnetwork) (W : Set V) : N.Subnetwork where
  vertexSet := S.vertexSet ∩ W
  arrowSet := {a | a ∈ S.arrowSet ∧ a.1 ∈ W ∧ a.2.1 ∈ W}
  source_mem a ha := ⟨S.source_mem a ha.1, ha.2.1⟩
  target_mem a ha := ⟨S.target_mem a ha.1, ha.2.2⟩

@[simp]
theorem vertexSet_restrictVertices (S : N.Subnetwork) (W : Set V) :
    (S.restrictVertices W).vertexSet = S.vertexSet ∩ W := (rfl)

@[simp]
theorem mem_arrowSet_restrictVertices {S : N.Subnetwork} {W : Set V}
    {a : Σ x y, N.Hom x y} :
    a ∈ (S.restrictVertices W).arrowSet ↔
      a ∈ S.arrowSet ∧ a.1 ∈ W ∧ a.2.1 ∈ W :=
  Iff.rfl

/-- Delete a set of ambient vertices and every arrow incident to one of them. -/
def deleteVerts (S : N.Subnetwork) (X : Set V) : N.Subnetwork :=
  S.restrictVertices Xᶜ

/-- Vertex deletion is restriction to the complementary vertex set. -/
theorem deleteVerts_eq_restrictVertices (S : N.Subnetwork) (X : Set V) :
    S.deleteVerts X = S.restrictVertices Xᶜ := (rfl)

@[simp]
theorem vertexSet_deleteVerts (S : N.Subnetwork) (X : Set V) :
    (S.deleteVerts X).vertexSet = S.vertexSet \ X := by
  ext x
  simp [deleteVerts]

@[simp]
theorem mem_arrowSet_deleteVerts {S : N.Subnetwork} {X : Set V}
    {a : Σ x y, N.Hom x y} :
    a ∈ (S.deleteVerts X).arrowSet ↔
      a ∈ S.arrowSet ∧ a.1 ∉ X ∧ a.2.1 ∉ X := by
  simp [deleteVerts]

/-- Restrict a subnetwork to arrows belonging to `A`, without discarding isolated vertices. -/
def restrictArrows (S : N.Subnetwork) (A : Set (Σ x y, N.Hom x y)) : N.Subnetwork where
  vertexSet := S.vertexSet
  arrowSet := S.arrowSet ∩ A
  source_mem a ha := S.source_mem a ha.1
  target_mem a ha := S.target_mem a ha.1

@[simp]
theorem vertexSet_restrictArrows (S : N.Subnetwork) (A : Set (Σ x y, N.Hom x y)) :
    (S.restrictArrows A).vertexSet = S.vertexSet := (rfl)

@[simp]
theorem arrowSet_restrictArrows (S : N.Subnetwork) (A : Set (Σ x y, N.Hom x y)) :
    (S.restrictArrows A).arrowSet = S.arrowSet ∩ A := (rfl)

/-- Delete selected ambient arrows without discarding any vertices. -/
def deleteArrows (S : N.Subnetwork) (A : Set (Σ x y, N.Hom x y)) : N.Subnetwork :=
  S.restrictArrows Aᶜ

@[simp]
theorem vertexSet_deleteArrows (S : N.Subnetwork) (A : Set (Σ x y, N.Hom x y)) :
    (S.deleteArrows A).vertexSet = S.vertexSet := (rfl)

@[simp]
theorem arrowSet_deleteArrows (S : N.Subnetwork) (A : Set (Σ x y, N.Hom x y)) :
    (S.deleteArrows A).arrowSet = S.arrowSet \ A := by
  ext a
  simp [deleteArrows]

/-! ### Interaction of the constructions -/

@[simp]
theorem induced_univ : N.inducedSubnetwork Set.univ = ⊤ := by
  ext <;> simp

@[simp]
theorem induced_empty : N.inducedSubnetwork ∅ = ⊥ := by
  ext <;> simp

theorem induced_mono {W X : Set V} (h : W ⊆ X) :
    N.inducedSubnetwork W ≤ N.inducedSubnetwork X := by
  refine ⟨h, ?_⟩
  rintro ⟨x, y, e⟩ ⟨hx, hy⟩
  exact ⟨h hx, h hy⟩

@[simp]
theorem restrictVertices_univ (S : N.Subnetwork) : S.restrictVertices Set.univ = S := by
  ext <;> simp

@[simp]
theorem restrictVertices_empty (S : N.Subnetwork) : S.restrictVertices ∅ = ⊥ := by
  ext <;> simp

@[simp]
theorem restrictArrows_univ (S : N.Subnetwork) :
    S.restrictArrows Set.univ = S := by
  ext <;> simp

@[simp]
theorem deleteVerts_empty (S : N.Subnetwork) : S.deleteVerts ∅ = S := by
  simp [deleteVerts]

@[simp]
theorem deleteArrows_empty (S : N.Subnetwork) : S.deleteArrows ∅ = S := by
  simp [deleteArrows]

theorem restrictVertices_le (S : N.Subnetwork) (W : Set V) : S.restrictVertices W ≤ S :=
  ⟨Set.inter_subset_left, fun _ ha ↦ ha.1⟩

theorem restrictArrows_le (S : N.Subnetwork) (A : Set (Σ x y, N.Hom x y)) :
    S.restrictArrows A ≤ S :=
  ⟨Set.Subset.rfl, Set.inter_subset_left⟩

theorem singleton_le_induced {x : V} {W : Set V} (hx : x ∈ W) :
    N.singletonSubnetwork x ≤ N.inducedSubnetwork W := by
  refine ⟨?_, Set.empty_subset _⟩
  simpa using hx

end Subnetwork

end TauCeti.Network

namespace TauCeti.ArrowWalk

variable {K : Type w} {V : Type u} [LE K] {N : Network K V}

/-- The subnetwork traced by a directed walk: exactly its visited vertices and traversed arrows. -/
def toSubnetwork {s t : V} (p : ArrowWalk N.Hom s t) : N.Subnetwork where
  vertexSet := {x | x ∈ p.vertices}
  arrowSet := {a | a ∈ p.arrows}
  source_mem := by
    rintro ⟨x, y, e⟩ he
    exact p.source_mem_vertices_of_mem_arrows he
  target_mem := by
    rintro ⟨x, y, e⟩ he
    rw [vertices_eq_cons_map_target_arrows]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (f := fun a ↦ a.2.1) he)

@[simp]
theorem toSubnetwork_vertexSet {s t : V} (p : ArrowWalk N.Hom s t) :
    p.toSubnetwork.vertexSet = {x | x ∈ p.vertices} :=
  (rfl)

@[simp]
theorem toSubnetwork_arrowSet {s t : V} (p : ArrowWalk N.Hom s t) :
    p.toSubnetwork.arrowSet = {a | a ∈ p.arrows} :=
  (rfl)

theorem source_mem_toSubnetwork {s t : V} (p : ArrowWalk N.Hom s t) :
    s ∈ p.toSubnetwork.vertexSet :=
  @Quiver.Path.start_mem_vertices V ⟨N.Hom⟩ s t p

theorem target_mem_toSubnetwork {s t : V} (p : ArrowWalk N.Hom s t) :
    t ∈ p.toSubnetwork.vertexSet :=
  @Quiver.Path.end_mem_vertices V ⟨N.Hom⟩ s t p

/-- The subnetwork traced by the first factor of a composite walk lies in the subnetwork traced
by the composite. -/
theorem toSubnetwork_comp_left_le {s t x : V} (p : ArrowWalk N.Hom s t)
    (q : ArrowWalk N.Hom t x) : p.toSubnetwork ≤ (p.comp q).toSubnetwork := by
  refine ⟨?_, ?_⟩
  · intro v hv
    -- Expose the set-comprehension representation of the traced vertex sets.
    change v ∈ p.vertices at hv
    change v ∈ (p.comp q).vertices
    exact (p.comp q).vertices_subset_of_arrows_subset (by simp) hv
  · intro a ha
    simpa using List.mem_append_left q.arrows ha

/-- The subnetwork traced by the second factor of a composite walk lies in the subnetwork traced
by the composite. -/
theorem toSubnetwork_comp_right_le {s t x : V} (p : ArrowWalk N.Hom s t)
    (q : ArrowWalk N.Hom t x) : q.toSubnetwork ≤ (p.comp q).toSubnetwork := by
  refine ⟨?_, ?_⟩
  · intro v hv
    -- Expose the set-comprehension representation of the traced vertex sets.
    change v ∈ q.vertices at hv
    change v ∈ (p.comp q).vertices
    rw [show (p.comp q).vertices = p.vertices.dropLast ++ q.vertices from
      @Quiver.Path.vertices_comp V ⟨N.Hom⟩ _ _ _ p q]
    exact List.mem_append_right _ hv
  · intro a ha
    simpa using List.mem_append_right p.arrows ha

/-- A walk gives reachability between its endpoints in the subnetwork that it traces. -/
theorem reachable_toSubnetwork {s t : V} (p : ArrowWalk N.Hom s t) :
    p.toSubnetwork.Reachable s t := by
  rw [p.toSubnetwork.reachable_def, reachableWithout_def]
  exact ⟨p, fun _ ha h ↦ h ha⟩

/-- Every vertex on a walk is reachable from its source and can reach its target inside the
subnetwork traced by that walk. -/
theorem reachable_of_mem_vertices {s t x : V} (p : ArrowWalk N.Hom s t)
    (hx : x ∈ p.vertices) :
    p.toSubnetwork.Reachable s x ∧ p.toSubnetwork.Reachable x t := by
  obtain ⟨q, r, hqr⟩ :=
    @Quiver.Path.exists_eq_comp_of_mem_vertices V ⟨N.Hom⟩ _ _ p x hx
  -- The Mathlib splitter exposes both pieces under its local quiver instance.
  change ArrowWalk N.Hom s x at q
  change ArrowWalk N.Hom x t at r
  have hq : q.toSubnetwork ≤ p.toSubnetwork := by
    rw [hqr]
    exact q.toSubnetwork_comp_left_le r
  have hr : r.toSubnetwork ≤ p.toSubnetwork := by
    rw [hqr]
    exact q.toSubnetwork_comp_right_le r
  exact ⟨q.reachable_toSubnetwork.mono hq, r.reachable_toSubnetwork.mono hr⟩

end TauCeti.ArrowWalk
