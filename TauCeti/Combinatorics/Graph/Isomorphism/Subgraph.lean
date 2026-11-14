/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Lattice
public import Mathlib.Order.LatticeIntervals
public import TauCeti.Combinatorics.Graph.Isomorphism.Basic
public import TauCeti.Combinatorics.Graph.Union

/-!
# Subgraphs under multigraph isomorphisms

A multigraph isomorphism identifies the partially ordered sets of subgraphs of its source and
target. Transport selects the images of both the vertex set and the edge set: isolated vertices
are retained, and parallel edges and loops retain their identities. Each subgraph is isomorphic
to its image. This lets constructions that grow a graph by adjoining subgraphs be relabelled
without losing their intermediate graphs.

The construction uses Mathlib's vertex induction and edge restriction, rather than a new
subgraph representation. No finiteness of the graphs or their ambient types is required.
-/

public section

open Set

universe u v u' v' u'' v''

namespace Graph.Iso

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
  {α'' : Type u''} {β'' : Type v''}
  {G : Graph α β} {H : Graph α' β'} {K : Graph α'' β''}

/-- The image of a subgraph, retaining exactly its selected vertices and edge identities. -/
def mapSubgraph (f : Iso G H) (S : Set.Iic G) : Graph α' β' :=
  (H.induce (f.mapVertexSet V(S.val))).restrict (f.mapEdgeSet E(S.val))

/-- The image subgraph has precisely the transported vertex set. -/
@[simp, grind =]
theorem vertexSet_mapSubgraph (f : Iso G H) (S : Set.Iic G) :
    V(f.mapSubgraph S) = f.mapVertexSet V(S.val) :=
  (rfl)

/-- The transported graph is a subgraph of the target. -/
@[simp]
theorem mapSubgraph_le (f : Iso G H) (S : Set.Iic G) : f.mapSubgraph S ≤ H :=
  restrict_le.trans (induce_le (f.mapVertexSet_subset_vertexSet _))

/-- The image subgraph has precisely the transported edge set. -/
@[simp, grind =]
theorem edgeSet_mapSubgraph (f : Iso G H) (S : Set.Iic G) :
    E(f.mapSubgraph S) = f.mapEdgeSet E(S.val) := by
  apply Set.Subset.antisymm
  · exact fun _ h ↦ h.2
  intro e heS
  have he := f.mapEdgeSet_subset_edgeSet _ heS
  have hS := (f.mem_mapEdgeSet_iff E(S.val) ⟨e, he⟩).mp heS
  obtain ⟨x, y, hxy⟩ := S.val.exists_isLink_of_mem_edgeSet hS
  have hG := hxy.mono S.property
  have hH := f.map_isLink hG
  have hx : (f.vertexEquiv ⟨x, hG.left_mem⟩ : α') ∈ f.mapVertexSet V(S.val) := by
    simpa using hxy.left_mem
  have hy : (f.vertexEquiv ⟨y, hG.right_mem⟩ : α') ∈ f.mapVertexSet V(S.val) := by
    simpa using hxy.right_mem
  have hH' : H.IsLink e (f.vertexEquiv ⟨x, hG.left_mem⟩)
      (f.vertexEquiv ⟨y, hG.right_mem⟩) := by simpa using hH
  exact ⟨⟨_, _, hH', hx, hy⟩, heS⟩

/-- A link in the image is a target link whose edge belongs to the transported edge set. -/
@[grind =]
theorem mapSubgraph_isLink (f : Iso G H) (S : Set.Iic G) {e : β'} {x y : α'} :
    (f.mapSubgraph S).IsLink e x y ↔ H.IsLink e x y ∧ e ∈ f.mapEdgeSet E(S.val) := by
  rw [(f.mapSubgraph_le S).isLink_iff', edgeSet_mapSubgraph]

/-- Link transport restricts to any selected subgraph. -/
@[simp, grind =]
theorem mapSubgraph_isLink_edgeEquiv_iff (f : Iso G H) (S : Set.Iic G) (e : G.edgeSet)
    (x y : G.vertexSet) :
    (f.mapSubgraph S).IsLink (f.edgeEquiv e) (f.vertexEquiv x) (f.vertexEquiv y) ↔
      S.val.IsLink e x y := by
  simpa only [mapSubgraph_isLink, f.map_isLink_iff, f.mem_mapEdgeSet_iff,
    Equiv.symm_apply_apply] using (S.property.isLink_iff').symm

/-- Transport preserves and reflects inclusion between subgraphs. -/
@[simp, grind =]
theorem mapSubgraph_le_mapSubgraph_iff (f : Iso G H) (S T : Set.Iic G) :
    f.mapSubgraph S ≤ f.mapSubgraph T ↔ S ≤ T := by
  constructor
  · intro h
    apply (Compatible.of_le_le S.property T.property).le_iff.mpr
    constructor
    · have hV := f.symm.mapVertexSet_mono h.vertexSet_mono
      simpa [S.property.vertexSet_mono, T.property.vertexSet_mono] using hV
    · have hE := f.symm.mapEdgeSet_mono h.edgeSet_mono
      simpa [S.property.edgeSet_mono, T.property.edgeSet_mono] using hE
  · intro h
    exact (Compatible.of_le_le (f.mapSubgraph_le S) (f.mapSubgraph_le T)).le_iff.mpr
      ⟨f.mapVertexSet_mono h.vertexSet_mono, by
        simpa using f.mapEdgeSet_mono h.edgeSet_mono⟩

/-- Transport back along the inverse recovers the original subgraph. -/
private theorem mapSubgraph_symm_mapSubgraph (f : Iso G H) (S : Set.Iic G) :
    f.symm.mapSubgraph ⟨f.mapSubgraph S, f.mapSubgraph_le S⟩ = S.val := by
  apply (Compatible.of_le_le (f.symm.mapSubgraph_le _) S.property).ext
  · simp [S.property.vertexSet_mono]
  · simp [S.property.edgeSet_mono]

/-- A multigraph isomorphism identifies its two partially ordered sets of subgraphs. -/
def subgraphOrderIso (f : Iso G H) : Set.Iic G ≃o Set.Iic H where
  toFun S := ⟨f.mapSubgraph S, f.mapSubgraph_le S⟩
  invFun T := ⟨f.symm.mapSubgraph T, f.symm.mapSubgraph_le T⟩
  left_inv S := Subtype.ext (f.mapSubgraph_symm_mapSubgraph S)
  right_inv T := Subtype.ext (by simpa using f.symm.mapSubgraph_symm_mapSubgraph T)
  map_rel_iff' := f.mapSubgraph_le_mapSubgraph_iff _ _

/-- The order isomorphism returns the image subgraph. -/
@[simp]
theorem coe_subgraphOrderIso_apply (f : Iso G H) (S : Set.Iic G) :
    (f.subgraphOrderIso S).val = f.mapSubgraph S :=
  (rfl)

/-- Evaluating the inverse order isomorphism returns inverse graph transport. -/
@[simp]
theorem coe_subgraphOrderIso_symm_apply (f : Iso G H) (T : Set.Iic H) :
    (f.subgraphOrderIso.symm T).val = f.symm.mapSubgraph T :=
  (rfl)

/-- Bundling a transported subgraph agrees with the order isomorphism. -/
@[simp]
theorem mk_mapSubgraph (f : Iso G H) (S : Set.Iic G) :
    (⟨f.mapSubgraph S, f.mapSubgraph_le S⟩ : Set.Iic H) = f.subgraphOrderIso S :=
  (rfl)

/-- Inverse transport cancels forward transport in order-isomorphism normal form. -/
@[simp]
theorem symm_mapSubgraph_subgraphOrderIso (f : Iso G H) (S : Set.Iic G) :
    f.symm.mapSubgraph (f.subgraphOrderIso S) = S.val :=
  f.mapSubgraph_symm_mapSubgraph S

/-- Forward transport cancels inverse transport in order-isomorphism normal form. -/
@[simp]
theorem mapSubgraph_subgraphOrderIso_symm (f : Iso G H) (T : Set.Iic H) :
    f.mapSubgraph (f.subgraphOrderIso.symm T) = T.val := by
  simpa only [coe_subgraphOrderIso_apply] using
    congrArg Subtype.val (f.subgraphOrderIso.apply_symm_apply T)

/-- Subgraph transport preserves and reflects equality. -/
@[simp]
theorem mapSubgraph_inj (f : Iso G H) (S T : Set.Iic G) :
    f.mapSubgraph S = f.mapSubgraph T ↔ S = T := by
  simpa only [← coe_subgraphOrderIso_apply, Subtype.val_inj] using
    f.subgraphOrderIso.injective.eq_iff

/-- Inverse subgraph transport is transport by the inverse isomorphism. -/
@[simp]
theorem subgraphOrderIso_symm (f : Iso G H) :
    f.symm.subgraphOrderIso = f.subgraphOrderIso.symm := by
  apply DFunLike.ext
  intro S
  rfl

/-- The identity isomorphism fixes every subgraph. -/
@[simp]
theorem mapSubgraph_refl (S : Set.Iic G) : (refl G).mapSubgraph S = S.val := by
  apply (Compatible.of_le_le ((refl G).mapSubgraph_le S) S.property).ext
  · simp [Set.inter_eq_left.mpr S.property.vertexSet_mono]
  · simp [Set.inter_eq_left.mpr S.property.edgeSet_mono]

/-- Transport along a composite is successive transport of subgraphs. -/
@[simp]
theorem mapSubgraph_trans (f : Iso G H) (g : Iso H K) (S : Set.Iic G) :
    (f.trans g).mapSubgraph S = g.mapSubgraph (f.subgraphOrderIso S) := by
  apply (Compatible.of_le_le ((f.trans g).mapSubgraph_le S) (g.mapSubgraph_le _)).ext <;>
    simp

/-- Identity transport is the identity order isomorphism. -/
@[simp]
theorem subgraphOrderIso_refl (G : Graph α β) :
    (refl G).subgraphOrderIso = OrderIso.refl (Set.Iic G) := by
  apply DFunLike.ext
  intro S
  exact Subtype.ext (mapSubgraph_refl S)

/-- Composition of graph isomorphisms composes their subgraph order isomorphisms. -/
@[simp]
theorem subgraphOrderIso_trans (f : Iso G H) (g : Iso H K) :
    (f.trans g).subgraphOrderIso = f.subgraphOrderIso.trans g.subgraphOrderIso := by
  apply DFunLike.ext
  intro S
  exact Subtype.ext (mapSubgraph_trans f g S)

/-- The isomorphism from a subgraph to its image is the restriction of the original vertex and
edge equivalences. -/
def subgraphIso (f : Iso G H) (S : Set.Iic G) : Iso S.val (f.mapSubgraph S) where
  vertexEquiv :=
    (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ V(G))) (q := (· ∈ V(S.val)))
      (fun {_} hx ↦ S.property.vertexSet_mono hx)).symm.trans
      ((f.vertexEquiv.subtypeEquiv (p := fun x ↦ x.val ∈ V(S.val))
        (q := fun y ↦ y.val ∈ V(f.mapSubgraph S)) (fun _ ↦ by simp)).trans
          (Equiv.subtypeSubtypeEquivSubtype
            (fun {_} hy ↦ (f.mapSubgraph_le S).vertexSet_mono hy)))
  edgeEquiv :=
    (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ E(G))) (q := (· ∈ E(S.val)))
      (fun {_} he ↦ S.property.edgeSet_mono he)).symm.trans
      ((f.edgeEquiv.subtypeEquiv (p := fun e ↦ e.val ∈ E(S.val))
        (q := fun e ↦ e.val ∈ E(f.mapSubgraph S)) (fun _ ↦ by simp)).trans
          (Equiv.subtypeSubtypeEquivSubtype
            (fun {_} he ↦ (f.mapSubgraph_le S).edgeSet_mono he)))
  map_isLink_iff e x y := f.mapSubgraph_isLink_edgeEquiv_iff S _ _ _

/-- The restricted isomorphism acts on vertices by the original equivalence. -/
@[simp]
theorem coe_subgraphIso_vertexEquiv_apply (f : Iso G H) (S : Set.Iic G) (x : S.val.vertexSet) :
    ((f.subgraphIso S).vertexEquiv x : α') =
      f.vertexEquiv ⟨x, S.property.vertexSet_mono x.property⟩ :=
  (rfl)

/-- The restricted isomorphism acts on edges by the original equivalence. -/
@[simp]
theorem coe_subgraphIso_edgeEquiv_apply (f : Iso G H) (S : Set.Iic G) (e : S.val.edgeSet) :
    ((f.subgraphIso S).edgeEquiv e : β') =
      f.edgeEquiv ⟨e, S.property.edgeSet_mono e.property⟩ :=
  (rfl)

/-- The inverse restricted vertex equivalence is the original inverse on actual vertices. -/
@[simp]
theorem coe_subgraphIso_vertexEquiv_symm_apply (f : Iso G H) (S : Set.Iic G)
    (y : (f.mapSubgraph S).vertexSet) :
    ((f.subgraphIso S).vertexEquiv.symm y : α) =
      f.vertexEquiv.symm ⟨y, (f.mapSubgraph_le S).vertexSet_mono y.property⟩ :=
  (rfl)

/-- The inverse restricted edge equivalence is the original inverse on actual edges. -/
@[simp]
theorem coe_subgraphIso_edgeEquiv_symm_apply (f : Iso G H) (S : Set.Iic G)
    (e : (f.mapSubgraph S).edgeSet) :
    ((f.subgraphIso S).edgeEquiv.symm e : β) =
      f.edgeEquiv.symm ⟨e, (f.mapSubgraph_le S).edgeSet_mono e.property⟩ :=
  (rfl)

/-- Transport of an edgeless subgraph retains all its selected, isolated vertices. -/
@[simp]
theorem mapSubgraph_noEdge (f : Iso G H) (X : Set α) (h : noEdge X β ≤ G) :
    f.mapSubgraph ⟨noEdge X β, h⟩ =
      noEdge (f.mapVertexSet X) β' := by
  apply (Compatible.of_le_le (f.mapSubgraph_le _)
    (noEdge_le_iff.mpr (f.mapVertexSet_subset_vertexSet X))).ext
  · simp
  · simp

/-- Edge restriction commutes with subgraph transport, including when selected edges are parallel
or are loops. -/
@[simp]
theorem mapSubgraph_restrict (f : Iso G H) (S : Set.Iic G) (F : Set β) :
    f.mapSubgraph ⟨S.val.restrict F, restrict_le.trans S.property⟩ =
      (f.mapSubgraph S).restrict (f.mapEdgeSet F) := by
  apply (Compatible.of_le_le (f.mapSubgraph_le _)
    (restrict_le.trans (f.mapSubgraph_le S))).ext
  · simp
  · simp

/-- Transport of the whole source graph is the whole target graph. -/
@[simp]
theorem mapSubgraph_self (f : Iso G H) (h : G ≤ G) :
    f.mapSubgraph ⟨G, h⟩ = H := by
  apply (Compatible.of_le_le (f.mapSubgraph_le _) le_rfl).ext <;> simp

/-- Transport of the empty graph is empty. -/
@[simp]
theorem mapSubgraph_mk_bot (f : Iso G H) (h : (⊥ : Graph α β) ≤ G) :
    f.mapSubgraph ⟨⊥, h⟩ = ⊥ := by
  apply (Compatible.of_le_le (f.mapSubgraph_le _) bot_le).ext <;> simp

/-- The greatest subgraph is transported to the whole target graph. -/
@[simp]
theorem mapSubgraph_top (f : Iso G H) : f.mapSubgraph ⊤ = H := by
  simpa only [coe_subgraphOrderIso_apply, Iic.coe_top] using
    congrArg Subtype.val f.subgraphOrderIso.map_top

/-- The least subgraph is transported to the empty graph. -/
@[simp]
theorem mapSubgraph_bot (f : Iso G H) : f.mapSubgraph (⊥ : Set.Iic G) = ⊥ := by
  simpa only [coe_subgraphOrderIso_apply, Iic.coe_bot] using
    congrArg Subtype.val f.subgraphOrderIso.map_bot

/-- Restricting the ambient graph commutes with transport. -/
@[simp]
theorem mapSubgraph_restrict_self (f : Iso G H) (F : Set β) :
    f.mapSubgraph ⟨G.restrict F, restrict_le⟩ = H.restrict (f.mapEdgeSet F) := by
  simpa using f.mapSubgraph_restrict (⊤ : Set.Iic G) F

/-- Edge deletion commutes with subgraph transport. -/
@[simp]
theorem mapSubgraph_deleteEdges (f : Iso G H) (S : Set.Iic G) (F : Set β) :
    f.mapSubgraph ⟨S.val.deleteEdges F, deleteEdges_le.trans S.property⟩ =
      (f.mapSubgraph S).deleteEdges (f.mapEdgeSet F) := by
  apply (Compatible.of_le_le (f.mapSubgraph_le _)
    (deleteEdges_le.trans (f.mapSubgraph_le S))).ext <;> simp

/-- Deleting edges from the ambient graph commutes with transport. -/
@[simp]
theorem mapSubgraph_deleteEdges_self (f : Iso G H) (F : Set β) :
    f.mapSubgraph ⟨G.deleteEdges F, deleteEdges_le⟩ = H.deleteEdges (f.mapEdgeSet F) := by
  simpa using f.mapSubgraph_deleteEdges (⊤ : Set.Iic G) F

/-- Vertex induction commutes with subgraph transport, even when `X` adds isolated vertices. -/
@[simp]
theorem mapSubgraph_induce (f : Iso G H) (S : Set.Iic G) (X : Set α)
    (h : S.val.induce X ≤ G) :
    f.mapSubgraph ⟨S.val.induce X, h⟩ = (f.mapSubgraph S).induce (f.mapVertexSet X) := by
  apply Graph.ext (by simp)
  intro e x y
  have links (e : H.edgeSet) (x y : H.vertexSet) :
      (f.mapSubgraph ⟨S.val.induce X, h⟩).IsLink e x y ↔
        ((f.mapSubgraph S).induce (f.mapVertexSet X)).IsLink e x y := by
    obtain ⟨e, rfl⟩ := f.edgeEquiv.surjective e
    obtain ⟨x, rfl⟩ := f.vertexEquiv.surjective x
    obtain ⟨y, rfl⟩ := f.vertexEquiv.surjective y
    simp [induce_isLink]
  constructor
  · intro he
    have hH := (f.mapSubgraph_le _).isLink_mono he
    exact (links ⟨e, hH.edge_mem⟩ ⟨x, hH.left_mem⟩ ⟨y, hH.right_mem⟩).mp he
  · intro he
    have hH := (f.mapSubgraph_le S).isLink_mono he.1
    exact (links ⟨e, hH.edge_mem⟩ ⟨x, hH.left_mem⟩ ⟨y, hH.right_mem⟩).mpr he

/-- Inducing the ambient graph commutes with transport. -/
@[simp]
theorem mapSubgraph_induce_self (f : Iso G H) (X : Set α) (h : G.induce X ≤ G) :
    f.mapSubgraph ⟨G.induce X, h⟩ = H.induce (f.mapVertexSet X) := by
  simpa using f.mapSubgraph_induce (⊤ : Set.Iic G) X h

/-- Vertex deletion commutes with subgraph transport. -/
@[simp]
theorem mapSubgraph_deleteVerts (f : Iso G H) (S : Set.Iic G) (X : Set α) :
    f.mapSubgraph ⟨S.val.deleteVerts X, deleteVerts_le.trans S.property⟩ =
      (f.mapSubgraph S).deleteVerts (f.mapVertexSet X) := by
  have hi := f.mapSubgraph_induce S (V(S.val) \ X)
    ((induce_le sdiff_subset).trans S.property)
  rw [mapVertexSet_sdiff, ← vertexSet_mapSubgraph] at hi
  convert hi using 1 <;> congr 1 <;> ext <;>
    simp only [vertexSet_deleteVerts, vertexSet_induce, deleteVerts_isLink,
      induce_isLink, mem_sdiff, and_congr_right_iff]
  · intro h
    simp only [h.left_mem, h.right_mem, true_and]
  · intro h
    simp only [h.left_mem, h.right_mem, true_and]

/-- Deleting vertices from the ambient graph commutes with transport. -/
@[simp]
theorem mapSubgraph_deleteVerts_self (f : Iso G H) (X : Set α) :
    f.mapSubgraph ⟨G.deleteVerts X, deleteVerts_le⟩ = H.deleteVerts (f.mapVertexSet X) := by
  simpa using f.mapSubgraph_deleteVerts (⊤ : Set.Iic G) X

/-- Transport preserves the compatible union of two subgraphs. -/
@[simp]
theorem mapSubgraph_union (f : Iso G H) (S T : Set.Iic G) :
    f.mapSubgraph ⟨(Compatible.of_le_le S.property T.property).union,
      S.property.union_le T.property⟩ =
      (Compatible.of_le_le (f.mapSubgraph_le S) (f.mapSubgraph_le T)).union := by
  apply (Compatible.of_le_le (f.mapSubgraph_le _)
    ((f.mapSubgraph_le S).union_le (f.mapSubgraph_le T))).ext <;> simp

end Graph.Iso
