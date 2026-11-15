/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Delete
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
@[simp, grind .]
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

/-- Incidence in the image is target incidence on a selected edge. -/
@[grind =]
theorem mapSubgraph_inc (f : Iso G H) (S : Set.Iic G) {e : β'} {x : α'} :
    (f.mapSubgraph S).Inc e x ↔ H.Inc e x ∧ e ∈ f.mapEdgeSet E(S.val) := by
  simp [Graph.Inc, mapSubgraph_isLink, exists_and_right]

/-- A loop in the image is a target loop on a selected edge. -/
@[grind =]
theorem mapSubgraph_isLoopAt (f : Iso G H) (S : Set.Iic G) {e : β'} {x : α'} :
    (f.mapSubgraph S).IsLoopAt e x ↔ H.IsLoopAt e x ∧ e ∈ f.mapEdgeSet E(S.val) := by
  simp only [Graph.IsLoopAt, mapSubgraph_isLink]

/-- Incidence transport restricts to every subgraph. -/
@[simp, grind =]
theorem mapSubgraph_inc_edgeEquiv_iff (f : Iso G H) (S : Set.Iic G)
    (e : G.edgeSet) (x : G.vertexSet) :
    (f.mapSubgraph S).Inc (f.edgeEquiv e) (f.vertexEquiv x) ↔ S.val.Inc e x := by
  constructor
  · rintro ⟨y, hy⟩
    have hyH := (f.mapSubgraph_le S).isLink_mono hy
    refine ⟨f.vertexEquiv.symm ⟨y, hyH.right_mem⟩, ?_⟩
    simpa using (f.mapSubgraph_isLink_edgeEquiv_iff S e x
      (f.vertexEquiv.symm ⟨y, hyH.right_mem⟩)).mp (by simpa using hy)
  · rintro ⟨y, hy⟩
    exact ⟨_, (f.mapSubgraph_isLink_edgeEquiv_iff S e x
      ⟨y, S.property.vertexSet_mono hy.right_mem⟩).mpr hy⟩

/-- Loop transport restricts to every subgraph. -/
@[simp, grind =]
theorem mapSubgraph_isLoopAt_edgeEquiv_iff (f : Iso G H) (S : Set.Iic G)
    (e : G.edgeSet) (x : G.vertexSet) :
    (f.mapSubgraph S).IsLoopAt (f.edgeEquiv e) (f.vertexEquiv x) ↔ S.val.IsLoopAt e x := by
  simp only [Graph.IsLoopAt, mapSubgraph_isLink_edgeEquiv_iff]

/-- Adjacency transport restricts to every subgraph, including loops. -/
@[simp, grind =]
theorem mapSubgraph_adj_vertexEquiv_iff (f : Iso G H) (S : Set.Iic G)
    (x y : G.vertexSet) :
    (f.mapSubgraph S).Adj (f.vertexEquiv x) (f.vertexEquiv y) ↔ S.val.Adj x y := by
  constructor
  · rintro ⟨e, he⟩
    have heH := (f.mapSubgraph_le S).isLink_mono he
    refine ⟨f.edgeEquiv.symm ⟨e, heH.edge_mem⟩, ?_⟩
    exact (f.mapSubgraph_isLink_edgeEquiv_iff S _ x y).mp (by simpa using he)
  · rintro ⟨e, he⟩
    exact ⟨_, (f.mapSubgraph_isLink_edgeEquiv_iff S
      ⟨e, S.property.edgeSet_mono he.edge_mem⟩ x y).mpr he⟩

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
@[simp, grind =]
theorem coe_subgraphOrderIso_apply (f : Iso G H) (S : Set.Iic G) :
    (f.subgraphOrderIso S).val = f.mapSubgraph S :=
  (rfl)

/-- Evaluating the inverse order isomorphism returns inverse graph transport. -/
@[simp, grind =]
theorem coe_subgraphOrderIso_symm_apply (f : Iso G H) (T : Set.Iic H) :
    (f.subgraphOrderIso.symm T).val = f.symm.mapSubgraph T :=
  (rfl)

/-- Bundling a transported subgraph agrees with the order isomorphism. -/
@[simp, grind =]
theorem mk_mapSubgraph (f : Iso G H) (S : Set.Iic G) :
    (⟨f.mapSubgraph S, f.mapSubgraph_le S⟩ : Set.Iic H) = f.subgraphOrderIso S :=
  (rfl)

/-- Inverse transport cancels forward transport in order-isomorphism normal form. -/
@[simp, grind =]
theorem symm_mapSubgraph_subgraphOrderIso (f : Iso G H) (S : Set.Iic G) :
    f.symm.mapSubgraph (f.subgraphOrderIso S) = S.val :=
  f.mapSubgraph_symm_mapSubgraph S

/-- Forward transport cancels inverse transport in order-isomorphism normal form. -/
@[simp, grind =]
theorem mapSubgraph_subgraphOrderIso_symm (f : Iso G H) (T : Set.Iic H) :
    f.mapSubgraph (f.subgraphOrderIso.symm T) = T.val := by
  simpa only [coe_subgraphOrderIso_apply] using
    congrArg Subtype.val (f.subgraphOrderIso.apply_symm_apply T)

/-- Subgraph transport preserves and reflects equality. -/
@[simp, grind =]
theorem mapSubgraph_inj (f : Iso G H) (S T : Set.Iic G) :
    f.mapSubgraph S = f.mapSubgraph T ↔ S = T := by
  simpa only [← coe_subgraphOrderIso_apply, Subtype.val_inj] using
    f.subgraphOrderIso.injective.eq_iff

/-- Inverse subgraph transport is transport by the inverse isomorphism. -/
@[simp, grind =]
theorem subgraphOrderIso_symm (f : Iso G H) :
    f.symm.subgraphOrderIso = f.subgraphOrderIso.symm := by
  apply DFunLike.ext
  intro S
  rfl

/-- The identity isomorphism fixes every subgraph. -/
@[simp, grind =]
theorem mapSubgraph_refl (S : Set.Iic G) : (refl G).mapSubgraph S = S.val := by
  apply (Compatible.of_le_le ((refl G).mapSubgraph_le S) S.property).ext
  · simp [Set.inter_eq_left.mpr S.property.vertexSet_mono]
  · simp [Set.inter_eq_left.mpr S.property.edgeSet_mono]

/-- Transport along a composite is successive transport of subgraphs. -/
@[simp, grind =]
theorem mapSubgraph_trans (f : Iso G H) (g : Iso H K) (S : Set.Iic G) :
    (f.trans g).mapSubgraph S = g.mapSubgraph (f.subgraphOrderIso S) := by
  apply (Compatible.of_le_le ((f.trans g).mapSubgraph_le S) (g.mapSubgraph_le _)).ext <;>
    simp

/-- Identity transport is the identity order isomorphism. -/
@[simp, grind =]
theorem subgraphOrderIso_refl (G : Graph α β) :
    (refl G).subgraphOrderIso = OrderIso.refl (Set.Iic G) := by
  apply DFunLike.ext
  intro S
  exact Subtype.ext (mapSubgraph_refl S)

/-- Composition of graph isomorphisms composes their subgraph order isomorphisms. -/
@[simp, grind =]
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
@[simp, grind =]
theorem coe_subgraphIso_vertexEquiv_apply (f : Iso G H) (S : Set.Iic G) (x : S.val.vertexSet) :
    ((f.subgraphIso S).vertexEquiv x : α') =
      f.vertexEquiv ⟨x, S.property.vertexSet_mono x.property⟩ :=
  (rfl)

/-- The restricted isomorphism acts on edges by the original equivalence. -/
@[simp, grind =]
theorem coe_subgraphIso_edgeEquiv_apply (f : Iso G H) (S : Set.Iic G) (e : S.val.edgeSet) :
    ((f.subgraphIso S).edgeEquiv e : β') =
      f.edgeEquiv ⟨e, S.property.edgeSet_mono e.property⟩ :=
  (rfl)

/-- The inverse restricted vertex equivalence is the original inverse on actual vertices. -/
@[simp, grind =]
theorem coe_subgraphIso_vertexEquiv_symm_apply (f : Iso G H) (S : Set.Iic G)
    (y : (f.mapSubgraph S).vertexSet) :
    ((f.subgraphIso S).vertexEquiv.symm y : α) =
      f.vertexEquiv.symm ⟨y, (f.mapSubgraph_le S).vertexSet_mono y.property⟩ :=
  (rfl)

/-- The inverse restricted edge equivalence is the original inverse on actual edges. -/
@[simp, grind =]
theorem coe_subgraphIso_edgeEquiv_symm_apply (f : Iso G H) (S : Set.Iic G)
    (e : (f.mapSubgraph S).edgeSet) :
    ((f.subgraphIso S).edgeEquiv.symm e : β) =
      f.edgeEquiv.symm ⟨e, (f.mapSubgraph_le S).edgeSet_mono e.property⟩ :=
  (rfl)

/-- Restricting an isomorphism restricts its action on ambient vertex sets. -/
@[simp, grind =]
theorem subgraphIso_mapVertexSet (f : Iso G H) (S : Set.Iic G) (X : Set α) :
    (f.subgraphIso S).mapVertexSet X = f.mapVertexSet X ∩ f.mapVertexSet V(S.val) := by
  ext y
  constructor
  · intro hy
    have hyS := (f.subgraphIso S).mapVertexSet_subset_vertexSet X hy
    have hyH := (f.mapSubgraph_le S).vertexSet_mono hyS
    refine ⟨(f.mem_mapVertexSet_iff X ⟨y, hyH⟩).mpr ?_, by simpa using hyS⟩
    simpa using ((f.subgraphIso S).mem_mapVertexSet_iff X ⟨y, hyS⟩).mp hy
  · rintro ⟨hyX, hyS⟩
    have hyS' : y ∈ V(f.mapSubgraph S) := by simpa using hyS
    have hyH := (f.mapSubgraph_le S).vertexSet_mono hyS'
    apply ((f.subgraphIso S).mem_mapVertexSet_iff X ⟨y, hyS'⟩).mpr
    simpa using (f.mem_mapVertexSet_iff X ⟨y, hyH⟩).mp hyX

/-- Restricting an isomorphism restricts its action on ambient edge sets. -/
@[simp, grind =]
theorem subgraphIso_mapEdgeSet (f : Iso G H) (S : Set.Iic G) (F : Set β) :
    (f.subgraphIso S).mapEdgeSet F = f.mapEdgeSet F ∩ f.mapEdgeSet E(S.val) := by
  ext e
  constructor
  · intro he
    have heS := (f.subgraphIso S).mapEdgeSet_subset_edgeSet F he
    have heH := (f.mapSubgraph_le S).edgeSet_mono heS
    refine ⟨(f.mem_mapEdgeSet_iff F ⟨e, heH⟩).mpr ?_, by simpa using heS⟩
    simpa using ((f.subgraphIso S).mem_mapEdgeSet_iff F ⟨e, heS⟩).mp he
  · rintro ⟨heF, heS⟩
    have heS' : e ∈ E(f.mapSubgraph S) := by simpa using heS
    have heH := (f.mapSubgraph_le S).edgeSet_mono heS'
    apply ((f.subgraphIso S).mem_mapEdgeSet_iff F ⟨e, heS'⟩).mpr
    simpa using (f.mem_mapEdgeSet_iff F ⟨e, heH⟩).mp heF

/-- The restriction agrees with ambient transport on sets of selected vertices. -/
@[simp high, grind =]
theorem subgraphIso_mapVertexSet_of_subset (f : Iso G H) (S : Set.Iic G)
    {X : Set α} (hX : X ⊆ V(S.val)) :
    (f.subgraphIso S).mapVertexSet X = f.mapVertexSet X := by
  rw [subgraphIso_mapVertexSet, inter_eq_left.mpr (f.mapVertexSet_mono hX)]

/-- The restriction agrees with ambient transport on sets of selected edges. -/
@[simp high, grind =]
theorem subgraphIso_mapEdgeSet_of_subset (f : Iso G H) (S : Set.Iic G)
    {F : Set β} (hF : F ⊆ E(S.val)) :
    (f.subgraphIso S).mapEdgeSet F = f.mapEdgeSet F := by
  rw [subgraphIso_mapEdgeSet, inter_eq_left.mpr (f.mapEdgeSet_mono hF)]

/-- Transporting a nested subgraph uses the same ambient isomorphism. -/
@[simp, grind =]
theorem subgraphIso_mapSubgraph (f : Iso G H) (S : Set.Iic G) (T : Set.Iic S.val) :
    (f.subgraphIso S).mapSubgraph T =
      f.mapSubgraph ⟨T.val, IsSubgraph.trans T.property S.property⟩ := by
  apply (Compatible.of_le_le
    (((f.subgraphIso S).mapSubgraph_le T).trans (f.mapSubgraph_le S))
    (f.mapSubgraph_le _)).ext
  · simp only [vertexSet_mapSubgraph, subgraphIso_mapVertexSet,
      inter_eq_left.mpr (f.mapVertexSet_mono T.property.vertexSet_mono)]
  · simp only [edgeSet_mapSubgraph, subgraphIso_mapEdgeSet,
      inter_eq_left.mpr (f.mapEdgeSet_mono T.property.edgeSet_mono)]

/-- Transport of an edgeless subgraph retains all its selected, isolated vertices. -/
@[simp, grind =]
theorem mapSubgraph_noEdge (f : Iso G H) (X : Set α) (h : noEdge X β ≤ G) :
    f.mapSubgraph ⟨noEdge X β, h⟩ =
      noEdge (f.mapVertexSet X) β' := by
  apply (Compatible.of_le_le (f.mapSubgraph_le _)
    (noEdge_le_iff.mpr (f.mapVertexSet_subset_vertexSet X))).ext
  · simp
  · simp

/-- Edge restriction commutes with subgraph transport, including when selected edges are parallel
or are loops. -/
@[simp, grind =]
theorem mapSubgraph_restrict (f : Iso G H) (S : Set.Iic G) (F : Set β) :
    f.mapSubgraph ⟨S.val.restrict F, restrict_le.trans S.property⟩ =
      (f.mapSubgraph S).restrict (f.mapEdgeSet F) := by
  apply (Compatible.of_le_le (f.mapSubgraph_le _)
    (restrict_le.trans (f.mapSubgraph_le S))).ext
  · simp
  · simp

/-- Transport of the whole source graph is the whole target graph. -/
@[simp, grind =]
theorem mapSubgraph_self (f : Iso G H) (h : G ≤ G) :
    f.mapSubgraph ⟨G, h⟩ = H := by
  apply (Compatible.of_le_le (f.mapSubgraph_le _) le_rfl).ext <;> simp

/-- Transport of the empty graph is empty. -/
@[simp, grind =]
theorem mapSubgraph_mk_bot (f : Iso G H) (h : (⊥ : Graph α β) ≤ G) :
    f.mapSubgraph ⟨⊥, h⟩ = ⊥ := by
  apply (Compatible.of_le_le (f.mapSubgraph_le _) bot_le).ext <;> simp

/-- The greatest subgraph is transported to the whole target graph. -/
@[simp, grind =]
theorem mapSubgraph_top (f : Iso G H) : f.mapSubgraph ⊤ = H := by
  simpa only [coe_subgraphOrderIso_apply, Iic.coe_top] using
    congrArg Subtype.val f.subgraphOrderIso.map_top

/-- The least subgraph is transported to the empty graph. -/
@[simp, grind =]
theorem mapSubgraph_bot (f : Iso G H) : f.mapSubgraph (⊥ : Set.Iic G) = ⊥ := by
  simpa only [coe_subgraphOrderIso_apply, Iic.coe_bot] using
    congrArg Subtype.val f.subgraphOrderIso.map_bot

/-- Restricting the ambient graph commutes with transport. -/
@[simp, grind =]
theorem mapSubgraph_restrict_self (f : Iso G H) (F : Set β) :
    f.mapSubgraph ⟨G.restrict F, restrict_le⟩ = H.restrict (f.mapEdgeSet F) := by
  simpa using f.mapSubgraph_restrict (⊤ : Set.Iic G) F

/-- Edge deletion commutes with subgraph transport. -/
@[simp, grind =]
theorem mapSubgraph_deleteEdges (f : Iso G H) (S : Set.Iic G) (F : Set β) :
    f.mapSubgraph ⟨S.val.deleteEdges F, deleteEdges_le.trans S.property⟩ =
      (f.mapSubgraph S).deleteEdges (f.mapEdgeSet F) := by
  apply (Compatible.of_le_le (f.mapSubgraph_le _)
    (deleteEdges_le.trans (f.mapSubgraph_le S))).ext <;> simp

/-- Deleting edges from the ambient graph commutes with transport. -/
@[simp, grind =]
theorem mapSubgraph_deleteEdges_self (f : Iso G H) (F : Set β) :
    f.mapSubgraph ⟨G.deleteEdges F, deleteEdges_le⟩ = H.deleteEdges (f.mapEdgeSet F) := by
  simpa using f.mapSubgraph_deleteEdges (⊤ : Set.Iic G) F

/-- Vertex induction commutes with subgraph transport, even when `X` adds isolated vertices. -/
@[simp, grind =]
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
@[simp, grind =]
theorem mapSubgraph_induce_self (f : Iso G H) (X : Set α) (h : G.induce X ≤ G) :
    f.mapSubgraph ⟨G.induce X, h⟩ = H.induce (f.mapVertexSet X) := by
  simpa using f.mapSubgraph_induce (⊤ : Set.Iic G) X h

/-- Vertex deletion commutes with subgraph transport. -/
@[simp, grind =]
theorem mapSubgraph_deleteVerts (f : Iso G H) (S : Set.Iic G) (X : Set α) :
    f.mapSubgraph ⟨S.val.deleteVerts X, deleteVerts_le.trans S.property⟩ =
      (f.mapSubgraph S).deleteVerts (f.mapVertexSet X) := by
  have hi := f.mapSubgraph_induce S (V(S.val) \ X)
    ((induce_le sdiff_subset).trans S.property)
  rw [mapVertexSet_sdiff, ← vertexSet_mapSubgraph] at hi
  simpa only [deleteVerts_eq_induce] using hi

/-- Deleting vertices from the ambient graph commutes with transport. -/
@[simp, grind =]
theorem mapSubgraph_deleteVerts_self (f : Iso G H) (X : Set α) :
    f.mapSubgraph ⟨G.deleteVerts X, deleteVerts_le⟩ = H.deleteVerts (f.mapVertexSet X) := by
  simpa using f.mapSubgraph_deleteVerts (⊤ : Set.Iic G) X

/-- Transport preserves the compatible union of two subgraphs. -/
@[simp, grind =]
theorem mapSubgraph_union (f : Iso G H) {S T : Graph α β} (hST : S.Compatible T)
    (h : hST.union ≤ G) :
    f.mapSubgraph ⟨hST.union, h⟩ =
      (Compatible.of_le_le (f.mapSubgraph_le ⟨S, (hST.union_le_iff.mp h).1⟩)
        (f.mapSubgraph_le ⟨T, (hST.union_le_iff.mp h).2⟩)).union := by
  apply (Compatible.of_le_le (f.mapSubgraph_le _)
    ((f.mapSubgraph_le _).union_le (f.mapSubgraph_le _))).ext <;> simp

/-- Transport preserves and reflects the spanning subgraph relation. -/
@[simp, grind =]
theorem mapSubgraph_isSpanningSubgraph_iff (f : Iso G H) (S T : Set.Iic G) :
    f.mapSubgraph S ≤s f.mapSubgraph T ↔ S.val ≤s T.val := by
  simp only [isSpanningSubgraph_iff, isSubgraph_iff_le,
    mapSubgraph_le_mapSubgraph_iff, vertexSet_mapSubgraph]
  constructor
  · rintro ⟨h, hV⟩
    refine ⟨h, ?_⟩
    simpa [S.property.vertexSet_mono, T.property.vertexSet_mono] using
      congrArg f.symm.mapVertexSet hV
  · rintro ⟨h, hV⟩
    exact ⟨h, congrArg f.mapVertexSet hV⟩

/-- Transport preserves and reflects the induced subgraph relation. -/
@[simp, grind =]
theorem mapSubgraph_isInducedSubgraph_iff (f : Iso G H) (S T : Set.Iic G) :
    f.mapSubgraph S ≤i f.mapSubgraph T ↔ S.val ≤i T.val := by
  constructor
  · intro h
    refine ⟨(f.mapSubgraph_le_mapSubgraph_iff S T).mp h.le, ?_⟩
    intro e x y hT hx hy
    have heG := T.property.edgeSet_mono hT.edge_mem
    have hxG := S.property.vertexSet_mono hx
    have hyG := S.property.vertexSet_mono hy
    apply (f.mapSubgraph_isLink_edgeEquiv_iff S ⟨e, heG⟩ ⟨x, hxG⟩ ⟨y, hyG⟩).mp
    exact h.isLink_of_mem_mem
      ((f.mapSubgraph_isLink_edgeEquiv_iff T _ _ _).mpr hT)
      (by simpa using hx) (by simpa using hy)
  · intro h
    refine ⟨(f.mapSubgraph_le_mapSubgraph_iff S T).mpr h.le, ?_⟩
    intro e x y hT hx hy
    have hH := (f.mapSubgraph_le T).isLink_mono hT
    let e' := f.edgeEquiv.symm ⟨e, hH.edge_mem⟩
    let x' := f.vertexEquiv.symm ⟨x, hH.left_mem⟩
    let y' := f.vertexEquiv.symm ⟨y, hH.right_mem⟩
    have hT' : T.val.IsLink e' x' y' :=
      (f.mapSubgraph_isLink_edgeEquiv_iff T e' x' y').mp (by simpa [e', x', y'] using hT)
    have hx' : (x' : α) ∈ V(S.val) :=
      (f.mem_mapVertexSet_iff V(S.val) ⟨x, hH.left_mem⟩).mp (by simpa using hx)
    have hy' : (y' : α) ∈ V(S.val) :=
      (f.mem_mapVertexSet_iff V(S.val) ⟨y, hH.right_mem⟩).mp (by simpa using hy)
    simpa [e', x', y'] using (f.mapSubgraph_isLink_edgeEquiv_iff S e' x' y').mpr
      (h.isLink_of_mem_mem hT' hx' hy')

/-- Transport preserves and reflects the closed subgraph relation. -/
@[simp, grind =]
theorem mapSubgraph_isClosedSubgraph_iff (f : Iso G H) (S T : Set.Iic G) :
    f.mapSubgraph S ≤c f.mapSubgraph T ↔ S.val ≤c T.val := by
  constructor
  · intro h
    refine ⟨(f.mapSubgraph_isInducedSubgraph_iff S T).mp h.isInducedSubgraph, ?_⟩
    intro e x he hx
    have heG := T.property.edgeSet_mono he.edge_mem
    have hxG := S.property.vertexSet_mono hx
    have hm := h.closed
      ((f.mapSubgraph_inc_edgeEquiv_iff T ⟨e, heG⟩ ⟨x, hxG⟩).mpr he)
      (by simpa using hx)
    simpa using hm
  · intro h
    refine ⟨(f.mapSubgraph_isInducedSubgraph_iff S T).mpr h.isInducedSubgraph, ?_⟩
    intro e x he hx
    have heH := he.mono (f.mapSubgraph_le T)
    let e' := f.edgeEquiv.symm ⟨e, heH.edge_mem⟩
    let x' := f.vertexEquiv.symm ⟨x, heH.vertex_mem⟩
    have he' : T.val.Inc e' x' :=
      (f.mapSubgraph_inc_edgeEquiv_iff T e' x').mp (by simpa [e', x'] using he)
    have hx' : (x' : α) ∈ V(S.val) :=
      (f.mem_mapVertexSet_iff V(S.val) ⟨x, heH.vertex_mem⟩).mp (by simpa using hx)
    have hm := h.closed he' hx'
    simpa [e'] using (f.mem_mapEdgeSet_iff E(S.val) ⟨e, heH.edge_mem⟩).mpr hm

/-- Spanning the target is equivalent to spanning the source before transport. -/
@[simp, grind =]
theorem mapSubgraph_isSpanningSubgraph_self_iff (f : Iso G H) (S : Set.Iic G) :
    f.mapSubgraph S ≤s H ↔ S.val ≤s G := by
  simpa using f.mapSubgraph_isSpanningSubgraph_iff S ⊤

/-- Being induced in the target is equivalent to being induced in the source. -/
@[simp, grind =]
theorem mapSubgraph_isInducedSubgraph_self_iff (f : Iso G H) (S : Set.Iic G) :
    f.mapSubgraph S ≤i H ↔ S.val ≤i G := by
  simpa using f.mapSubgraph_isInducedSubgraph_iff S ⊤

/-- Being closed in the target is equivalent to being closed in the source. -/
@[simp, grind =]
theorem mapSubgraph_isClosedSubgraph_self_iff (f : Iso G H) (S : Set.Iic G) :
    f.mapSubgraph S ≤c H ↔ S.val ≤c G := by
  simpa using f.mapSubgraph_isClosedSubgraph_iff S ⊤

/-- Transport preserves intersections of subgraphs. -/
@[simp, grind =]
theorem mapSubgraph_inf (f : Iso G H) (S T : Set.Iic G) :
    f.mapSubgraph (S ⊓ T) = f.mapSubgraph S ⊓ f.mapSubgraph T := by
  simpa only [coe_subgraphOrderIso_apply, Iic.coe_inf] using
    congrArg Subtype.val (f.subgraphOrderIso.map_inf S T)

/-- Transport preserves an unbundled intersection of subgraphs. -/
@[simp, grind =]
theorem mapSubgraph_mk_inf (f : Iso G H) (S T : Set.Iic G) (h : S.val ⊓ T.val ≤ G) :
    f.mapSubgraph ⟨S.val ⊓ T.val, h⟩ = f.mapSubgraph S ⊓ f.mapSubgraph T :=
  f.mapSubgraph_inf S T

end Graph.Iso
