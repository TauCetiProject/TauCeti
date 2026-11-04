/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.Data.Set.Lattice.Bounded
public import TauCeti.Combinatorics.Network.Basic
public import TauCeti.Combinatorics.Network.Walk
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sigma
import Mathlib.Data.Fintype.Powerset

/-!
# Subnetworks

A subnetwork of a bounded directed network selects vertices and original arrow identities, with
every selected arrow required to have selected endpoints. Its own vertex type is the selected
vertex subtype, and its bounds are inherited from the ambient network.

This file supplies the elementary set operations used to build subnetworks: induced subnetworks,
restriction and deletion of vertices or arrows, singleton and empty subnetworks, and unions inside
a fixed ambient network. It also defines the subnetwork traced by a directed walk, supplies walk
inclusion and restriction between subnetworks and their ambient network, and evaluates strong
connectivity on a subnetwork's selected vertices. In particular, isolated selected vertices remain
visible under every operation that does not delete them.
-/

public section

universe u v w

namespace TauCeti.Network

variable {K : Type w} {V : Type u} [LE K] (N : Network K V)

/-- A bounded network is strongly connected when every vertex can reach every other vertex along
its directed arrows. -/
def IsStronglyConnected : Prop :=
  @Quiver.IsStronglyConnected V ⟨N.Hom⟩

theorem isStronglyConnected_iff :
    N.IsStronglyConnected ↔ ∀ x y : V, Nonempty (ArrowWalk N.Hom x y) :=
  (Iff.rfl)

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

/-- A network with finite vertex and arrow types has finitely many subnetworks. -/
instance [Finite V] [∀ x y, Finite (N.Hom x y)] : Finite N.Subnetwork :=
  Finite.of_injective (fun S ↦ (S.vertexSet, S.arrowSet)) fun _ _ h ↦
    ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-! ### Walk inclusion and restriction -/

/-- The inclusion of a subnetwork's arrow family into the ambient arrow family, as a prefunctor. -/
def inclPrefunctor (S : N.Subnetwork) : @Prefunctor ↥S.vertexSet ⟨S.Hom⟩ V ⟨N.Hom⟩ :=
  @Prefunctor.mk ↥S.vertexSet ⟨S.Hom⟩ V ⟨N.Hom⟩ Subtype.val fun e ↦ e.1

/-- Push a walk in a subnetwork forward to the ambient network. -/
def mapWalk (S : N.Subnetwork) {x y : ↥S.vertexSet} (p : ArrowWalk S.Hom x y) :
    ArrowWalk N.Hom x.1 y.1 :=
  @Prefunctor.mapPath ↥S.vertexSet ⟨S.Hom⟩ V ⟨N.Hom⟩ S.inclPrefunctor x y p

@[simp]
theorem mapWalk_nil (S : N.Subnetwork) (x : ↥S.vertexSet) :
    S.mapWalk (ArrowWalk.nil x) = ArrowWalk.nil x.1 :=
  (rfl)

@[simp]
theorem mapWalk_cons (S : N.Subnetwork) {x y z : ↥S.vertexSet} (p : ArrowWalk S.Hom x y)
    (e : S.Hom y z) : S.mapWalk (p.cons e) = (S.mapWalk p).cons e.1 :=
  (rfl)

@[simp]
theorem mapWalk_comp (S : N.Subnetwork) {x y z : ↥S.vertexSet} (p : ArrowWalk S.Hom x y)
    (q : ArrowWalk S.Hom y z) : S.mapWalk (p.comp q) = (S.mapWalk p).comp (S.mapWalk q) :=
  @Prefunctor.mapPath_comp ↥S.vertexSet ⟨S.Hom⟩ V ⟨N.Hom⟩ S.inclPrefunctor x y p z q

@[simp]
theorem length_mapWalk (S : N.Subnetwork) {x y : ↥S.vertexSet} (p : ArrowWalk S.Hom x y) :
    (S.mapWalk p).length = p.length :=
  @Prefunctor.length_mapPath ↥S.vertexSet V ⟨S.Hom⟩ ⟨N.Hom⟩ S.inclPrefunctor x y p

@[simp]
theorem vertices_mapWalk (S : N.Subnetwork) {x y : ↥S.vertexSet} (p : ArrowWalk S.Hom x y) :
    (S.mapWalk p).vertices = p.vertices.map Subtype.val :=
  @Prefunctor.vertices_mapPath ↥S.vertexSet V ⟨S.Hom⟩ ⟨N.Hom⟩ S.inclPrefunctor x y p

@[simp]
theorem isPath_mapWalk (S : N.Subnetwork) {x y : ↥S.vertexSet} (p : ArrowWalk S.Hom x y) :
    (S.mapWalk p).IsPath ↔ p.IsPath := by
  rw [ArrowWalk.isPath_def, ArrowWalk.isPath_def, vertices_mapWalk,
    List.nodup_map_iff Subtype.val_injective]

@[simp]
theorem isCycle_mapWalk (S : N.Subnetwork) {x : ↥S.vertexSet} (p : ArrowWalk S.Hom x x) :
    (S.mapWalk p).IsCycle ↔ p.IsCycle := by
  rw [ArrowWalk.isCycle_def, ArrowWalk.isCycle_def, length_mapWalk, vertices_mapWalk,
    ← List.map_tail, List.nodup_map_iff Subtype.val_injective]

/-- Every arrow traversed by a pushed-forward subnetwork walk belongs to the subnetwork. -/
theorem arrows_mapWalk_mem (S : N.Subnetwork) {x y : ↥S.vertexSet} (p : ArrowWalk S.Hom x y)
    {a : Σ u w, N.Hom u w} (ha : a ∈ (S.mapWalk p).arrows) : a ∈ S.arrowSet := by
  induction p with
  | nil => simp at ha
  | cons p e ih =>
    rw [mapWalk_cons, ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact ih ha
    · exact e.2

/-- Walk inclusion from a subnetwork into the ambient network is injective. -/
theorem mapWalk_injective (S : N.Subnetwork) {x y : ↥S.vertexSet} :
    Function.Injective (S.mapWalk (x := x) (y := y)) := by
  intro p q hpq
  induction p with
  | nil =>
    cases q with
    | nil => rfl
    | cons q e =>
      have hlen := congrArg ArrowWalk.length hpq
      simp at hlen
  | @cons z₁ _ p e₁ ih =>
    cases q with
    | nil =>
      have hlen := congrArg ArrowWalk.length hpq
      simp at hlen
    | @cons z₂ _ q e₂ =>
      simp only [mapWalk_cons] at hpq
      injection hpq with hz _ hp he
      obtain rfl : z₁ = z₂ := Subtype.ext hz
      cases ih (eq_of_heq hp)
      obtain rfl : e₁ = e₂ := Subtype.ext (eq_of_heq he)
      rfl

/-- Inclusion of the arrow family of a smaller subnetwork into that of a larger one. -/
def inclPrefunctorOfLE {S T : N.Subnetwork} (h : S ≤ T) :
    @Prefunctor ↥S.vertexSet ⟨S.Hom⟩ ↥T.vertexSet ⟨T.Hom⟩ :=
  @Prefunctor.mk ↥S.vertexSet ⟨S.Hom⟩ ↥T.vertexSet ⟨T.Hom⟩ (vertexEmbeddingOfLE h)
    fun {x y} e ↦ arrowEmbeddingOfLE h x y e

/-- Push a walk forward from a smaller subnetwork to a larger one. -/
def mapWalkOfLE {S T : N.Subnetwork} (h : S ≤ T) {x y : ↥S.vertexSet} (p : ArrowWalk S.Hom x y) :
    ArrowWalk T.Hom (vertexEmbeddingOfLE h x) (vertexEmbeddingOfLE h y) :=
  @Prefunctor.mapPath ↥S.vertexSet ⟨S.Hom⟩ ↥T.vertexSet ⟨T.Hom⟩ (inclPrefunctorOfLE h) x y p

@[simp]
theorem mapWalkOfLE_nil {S T : N.Subnetwork} (h : S ≤ T) (x : ↥S.vertexSet) :
    mapWalkOfLE h (ArrowWalk.nil x) = ArrowWalk.nil (vertexEmbeddingOfLE h x) :=
  (rfl)

@[simp]
theorem mapWalkOfLE_cons {S T : N.Subnetwork} (h : S ≤ T) {x y z : ↥S.vertexSet}
    (p : ArrowWalk S.Hom x y) (e : S.Hom y z) :
    mapWalkOfLE h (p.cons e) = (mapWalkOfLE h p).cons (arrowEmbeddingOfLE h y z e) :=
  (rfl)

@[simp]
theorem mapWalkOfLE_comp {S T : N.Subnetwork} (h : S ≤ T) {x y z : ↥S.vertexSet}
    (p : ArrowWalk S.Hom x y) (q : ArrowWalk S.Hom y z) :
    mapWalkOfLE h (p.comp q) = (mapWalkOfLE h p).comp (mapWalkOfLE h q) :=
  @Prefunctor.mapPath_comp ↥S.vertexSet ⟨S.Hom⟩ ↥T.vertexSet ⟨T.Hom⟩
    (inclPrefunctorOfLE h) x y p z q

@[simp]
theorem length_mapWalkOfLE {S T : N.Subnetwork} (h : S ≤ T) {x y : ↥S.vertexSet}
    (p : ArrowWalk S.Hom x y) : (mapWalkOfLE h p).length = p.length :=
  @Prefunctor.length_mapPath ↥S.vertexSet ↥T.vertexSet ⟨S.Hom⟩ ⟨T.Hom⟩
    (inclPrefunctorOfLE h) x y p

@[simp]
theorem vertices_mapWalkOfLE {S T : N.Subnetwork} (h : S ≤ T) {x y : ↥S.vertexSet}
    (p : ArrowWalk S.Hom x y) :
    (mapWalkOfLE h p).vertices = p.vertices.map (vertexEmbeddingOfLE h) :=
  @Prefunctor.vertices_mapPath ↥S.vertexSet ↥T.vertexSet ⟨S.Hom⟩ ⟨T.Hom⟩
    (inclPrefunctorOfLE h) x y p

@[simp]
theorem mapWalk_mapWalkOfLE {S T : N.Subnetwork} (h : S ≤ T) {x y : ↥S.vertexSet}
    (p : ArrowWalk S.Hom x y) : T.mapWalk (mapWalkOfLE h p) = S.mapWalk p := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih]

@[simp]
theorem isPath_mapWalkOfLE {S T : N.Subnetwork} (h : S ≤ T) {x y : ↥S.vertexSet}
    (p : ArrowWalk S.Hom x y) : (mapWalkOfLE h p).IsPath ↔ p.IsPath := by
  rw [ArrowWalk.isPath_def, ArrowWalk.isPath_def, vertices_mapWalkOfLE,
    List.nodup_map_iff (vertexEmbeddingOfLE h).injective]

@[simp]
theorem isCycle_mapWalkOfLE {S T : N.Subnetwork} (h : S ≤ T) {x : ↥S.vertexSet}
    (p : ArrowWalk S.Hom x x) : (mapWalkOfLE h p).IsCycle ↔ p.IsCycle := by
  rw [ArrowWalk.isCycle_def, ArrowWalk.isCycle_def, length_mapWalkOfLE, vertices_mapWalkOfLE,
    ← List.map_tail, List.nodup_map_iff (vertexEmbeddingOfLE h).injective]

/-- Restrict an ambient walk whose endpoints and traversed arrows belong to `S` to a walk in `S`. -/
def liftWalk (S : N.Subnetwork) {s : V} :
    ∀ {t : V} (p : ArrowWalk N.Hom s t) (hs : s ∈ S.vertexSet) (ht : t ∈ S.vertexSet),
      (∀ a ∈ p.arrows, a ∈ S.arrowSet) → ArrowWalk S.Hom ⟨s, hs⟩ ⟨t, ht⟩
  | _, @Quiver.Path.nil _ .(_) _, hs, _, _ => ArrowWalk.nil (Q := S.Hom) ⟨s, hs⟩
  | _, @Quiver.Path.cons _ .(_) _ z w q e, hs, ht, ha =>
    let he : (⟨z, w, e⟩ : Σ x y, N.Hom x y) ∈ S.arrowSet :=
      ha ⟨z, w, e⟩
        (by rw [ArrowWalk.arrows_cons]; exact List.mem_append_right _ (List.mem_singleton_self _))
    (liftWalk S q hs (S.source_mem _ he) fun a h ↦
      ha a (by rw [ArrowWalk.arrows_cons]; exact List.mem_append_left _ h)).cons ⟨e, he⟩

@[simp]
theorem liftWalk_nil (S : N.Subnetwork) {s : V} (hs ht : s ∈ S.vertexSet)
    (ha : ∀ a ∈ (ArrowWalk.nil s : ArrowWalk N.Hom s s).arrows, a ∈ S.arrowSet) :
    S.liftWalk (ArrowWalk.nil s) hs ht ha = ArrowWalk.nil (Q := S.Hom) ⟨s, hs⟩ :=
  (rfl)

@[simp]
theorem mapWalk_liftWalk (S : N.Subnetwork) {s t : V} (p : ArrowWalk N.Hom s t)
    (hs : s ∈ S.vertexSet) (ht : t ∈ S.vertexSet) (ha : ∀ a ∈ p.arrows, a ∈ S.arrowSet) :
    S.mapWalk (S.liftWalk p hs ht ha) = p := by
  induction p with
  | nil => rfl
  | cons q e ih =>
    -- Unfold `liftWalk` on `cons` so `mapWalk_cons` and the induction hypothesis apply.
    unfold liftWalk
    simp [ih]

@[simp]
theorem liftWalk_mapWalk (S : N.Subnetwork) {x y : ↥S.vertexSet} (p : ArrowWalk S.Hom x y)
    (ha : ∀ a ∈ (S.mapWalk p).arrows, a ∈ S.arrowSet := fun _ h ↦ S.arrows_mapWalk_mem p h) :
    S.liftWalk (S.mapWalk p) x.2 y.2 ha = p :=
  S.mapWalk_injective (S.mapWalk_liftWalk (S.mapWalk p) x.2 y.2 ha)

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

@[simp]
theorem toSubnetwork_nil (s : V) :
    (nil s : ArrowWalk N.Hom s s).toSubnetwork = N.singletonSubnetwork s := by
  ext <;> simp

@[simp]
theorem toSubnetwork_comp {s t u : V} (p : ArrowWalk N.Hom s t) (q : ArrowWalk N.Hom t u) :
    (p.comp q).toSubnetwork = p.toSubnetwork ⊔ q.toSubnetwork := by
  refine Network.Subnetwork.ext (Set.ext fun x ↦ ?_) (Set.ext fun a ↦ ?_)
  · have hcomp : (p.comp q).vertices = p.vertices.dropLast ++ q.vertices :=
      @Quiver.Path.vertices_comp V ⟨N.Hom⟩ _ _ _ p q
    have hend : p.vertices.dropLast ++ [t] = p.vertices :=
      @Quiver.Path.dropLast_append_end_eq V ⟨N.Hom⟩ _ _ p
    have ht : t ∈ q.vertices := @Quiver.Path.start_mem_vertices V ⟨N.Hom⟩ _ _ q
    have hp : x ∈ p.vertices ↔ x ∈ p.vertices.dropLast ∨ x = t := by
      simpa only [List.mem_append, List.mem_singleton] using (congrArg (x ∈ ·) hend.symm).to_iff
    rw [toSubnetwork_vertexSet, Network.Subnetwork.sup_vertexSet, Set.mem_union,
      toSubnetwork_vertexSet, toSubnetwork_vertexSet, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      Set.mem_ofPred_eq, hcomp, List.mem_append, hp]
    exact ⟨fun h ↦ h.elim (fun h ↦ .inl (.inl h)) .inr,
      fun h ↦ h.elim (fun h ↦ h.elim .inl fun h ↦ .inr (h ▸ ht)) .inr⟩
  · rw [toSubnetwork_arrowSet, Network.Subnetwork.sup_arrowSet, Set.mem_union,
      toSubnetwork_arrowSet, toSubnetwork_arrowSet, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      Set.mem_ofPred_eq, arrows_comp, List.mem_append]

/-- The subnetwork traced by a walk lies in `S` precisely when its start vertex and every traversed
arrow belong to `S`. -/
theorem toSubnetwork_le_iff {s t : V} {p : ArrowWalk N.Hom s t} {S : N.Subnetwork} :
    p.toSubnetwork ≤ S ↔ s ∈ S.vertexSet ∧ ∀ a ∈ p.arrows, a ∈ S.arrowSet := by
  rw [Network.Subnetwork.le_def, toSubnetwork_vertexSet, toSubnetwork_arrowSet]
  refine ⟨fun ⟨hV, hA⟩ ↦ ⟨hV p.source_mem_toSubnetwork, fun a ha ↦ hA ha⟩, fun ⟨hs, hA⟩ ↦ ⟨?_, hA⟩⟩
  intro x hx
  rw [Set.mem_ofPred_eq, vertices_eq_cons_map_target_arrows, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact hs
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact S.target_mem a (hA a ha)

/-- Pushing a subnetwork walk into the ambient network traces a subnetwork of the original. -/
theorem toSubnetwork_mapWalk_le {S : N.Subnetwork} {x y : ↥S.vertexSet} (p : ArrowWalk S.Hom x y) :
    (S.mapWalk p).toSubnetwork ≤ S :=
  toSubnetwork_le_iff.2 ⟨x.2, fun _ ha ↦ S.arrows_mapWalk_mem p ha⟩

end TauCeti.ArrowWalk

namespace TauCeti.Network.Subnetwork

variable {K : Type w} {V : Type u} [LE K] {N : Network K V}

/-! ### Strong connectivity -/

/-- A subnetwork is strongly connected when its induced network on the selected vertices is
strongly connected. -/
def IsStronglyConnected (S : N.Subnetwork) : Prop :=
  S.toNetwork.IsStronglyConnected

theorem isStronglyConnected_iff (S : N.Subnetwork) :
    S.IsStronglyConnected ↔ ∀ x y : ↥S.vertexSet, Nonempty (ArrowWalk S.Hom x y) :=
  S.toNetwork.isStronglyConnected_iff

/-- A subnetwork is strongly connected precisely when any two selected vertices are joined by an
ambient walk traversing only selected arrows. -/
theorem isStronglyConnected_iff_exists_walk (S : N.Subnetwork) :
    S.IsStronglyConnected ↔
      ∀ ⦃x⦄, x ∈ S.vertexSet → ∀ ⦃y⦄, y ∈ S.vertexSet →
        ∃ p : ArrowWalk N.Hom x y, ∀ a ∈ p.arrows, a ∈ S.arrowSet := by
  rw [isStronglyConnected_iff]
  constructor
  · intro h x hx y hy
    obtain ⟨p⟩ := h ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨S.mapWalk p, fun _ ha ↦ S.arrows_mapWalk_mem p ha⟩
  · intro h ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨p, hp⟩ := h hx hy
    exact ⟨S.liftWalk p hx hy hp⟩

/-- Every subnetwork with at most one selected vertex is strongly connected. -/
theorem IsStronglyConnected.of_subsingleton {S : N.Subnetwork} (h : S.vertexSet.Subsingleton) :
    S.IsStronglyConnected :=
  S.isStronglyConnected_iff.2 fun x y ↦ by
    obtain rfl : x = y := Subtype.ext (h x.2 y.2)
    exact ⟨ArrowWalk.nil x⟩

@[simp]
theorem isStronglyConnected_empty : N.emptySubnetwork.IsStronglyConnected :=
  .of_subsingleton Set.subsingleton_empty

@[simp]
theorem isStronglyConnected_bot : (⊥ : N.Subnetwork).IsStronglyConnected :=
  isStronglyConnected_empty

@[simp]
theorem isStronglyConnected_singleton (x : V) : (N.singletonSubnetwork x).IsStronglyConnected :=
  .of_subsingleton Set.subsingleton_singleton

@[simp]
theorem isStronglyConnected_full_iff :
    N.fullSubnetwork.IsStronglyConnected ↔ N.IsStronglyConnected := by
  rw [isStronglyConnected_iff_exists_walk, Network.isStronglyConnected_iff]
  exact ⟨fun h x y ↦ let ⟨p, _⟩ := h (Set.mem_univ x) (Set.mem_univ y); ⟨p⟩,
    fun h x _ y _ ↦ let ⟨p⟩ := h x y; ⟨p, fun _ _ ↦ Set.mem_univ _⟩⟩

@[simp]
theorem isStronglyConnected_top_iff :
    (⊤ : N.Subnetwork).IsStronglyConnected ↔ N.IsStronglyConnected :=
  isStronglyConnected_full_iff

/-- Adjoining any directed walk whose endpoints already belong to a strongly connected subnetwork
preserves strong connectivity. -/
theorem IsStronglyConnected.sup_toSubnetwork {S : N.Subnetwork} (hS : S.IsStronglyConnected)
    {u w : V} (p : ArrowWalk N.Hom u w) (hu : u ∈ S.vertexSet) (hw : w ∈ S.vertexSet) :
    (S ⊔ p.toSubnetwork).IsStronglyConnected := by
  rw [isStronglyConnected_iff_exists_walk] at hS ⊢
  have to_S : ∀ ⦃z⦄, z ∈ (S ⊔ p.toSubnetwork).vertexSet →
      ∃ z' ∈ S.vertexSet, ∃ q : ArrowWalk N.Hom z z',
        ∀ a ∈ q.arrows, a ∈ (S ⊔ p.toSubnetwork).arrowSet := by
    intro z hz
    rcases hz with hzS | hzp
    · exact ⟨z, hzS, ArrowWalk.nil z, by simp⟩
    · obtain ⟨p₁, p₂, rfl⟩ : ∃ (p₁ : ArrowWalk N.Hom u z) (p₂ : ArrowWalk N.Hom z w),
          p = p₁.comp p₂ :=
        @Quiver.Path.exists_eq_comp_of_mem_vertices V ⟨N.Hom⟩ _ _ p _ hzp
      refine ⟨w, hw, p₂, fun a ha ↦ .inr ?_⟩
      rw [ArrowWalk.toSubnetwork_arrowSet, Set.mem_ofPred_eq, ArrowWalk.arrows_comp]
      exact List.mem_append_right _ ha
  have from_S : ∀ ⦃z⦄, z ∈ (S ⊔ p.toSubnetwork).vertexSet →
      ∃ z₀ ∈ S.vertexSet, ∃ q : ArrowWalk N.Hom z₀ z,
        ∀ a ∈ q.arrows, a ∈ (S ⊔ p.toSubnetwork).arrowSet := by
    intro z hz
    rcases hz with hzS | hzp
    · exact ⟨z, hzS, ArrowWalk.nil z, by simp⟩
    · obtain ⟨p₁, p₂, rfl⟩ : ∃ (p₁ : ArrowWalk N.Hom u z) (p₂ : ArrowWalk N.Hom z w),
          p = p₁.comp p₂ :=
        @Quiver.Path.exists_eq_comp_of_mem_vertices V ⟨N.Hom⟩ _ _ p _ hzp
      refine ⟨u, hu, p₁, fun a ha ↦ .inr ?_⟩
      rw [ArrowWalk.toSubnetwork_arrowSet, Set.mem_ofPred_eq, ArrowWalk.arrows_comp]
      exact List.mem_append_left _ ha
  intro x hx y hy
  obtain ⟨x', hx'S, q₁, hq₁⟩ := to_S hx
  obtain ⟨y₀, hy₀S, q₃, hq₃⟩ := from_S hy
  obtain ⟨q₂, hq₂⟩ := hS hx'S hy₀S
  refine ⟨(q₁.comp q₂).comp q₃, fun a ha ↦ ?_⟩
  rw [ArrowWalk.arrows_comp, ArrowWalk.arrows_comp, List.mem_append, List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · exact hq₁ a ha
  · exact .inl (hq₂ a ha)
  · exact hq₃ a ha

end TauCeti.Network.Subnetwork
