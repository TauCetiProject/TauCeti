/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bond
public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Basic
public import TauCeti.Combinatorics.Graph.Isomorphism

/-!
# Transporting multigraph cuts, bridges, and bonds along isomorphisms

A multigraph isomorphism transports subsets of the actual vertices and edges by its two
underlying equivalences. This transport sends an edge cut to the edge cut of the transported
vertex side, and consequently preserves edge cuts, bridges, and bonds. It also preserves the
absence of cycles, hence multigraph forests.

The set transport is stated on the ambient vertex and edge types because Mathlib's
`Graph.edgeCut`, `Graph.IsEdgeCut`, and `Graph.IsBond` use ambient sets. Elements outside the
actual carrier are discarded. On subsets of the actual carrier, transport along the inverse
isomorphism is an exact inverse.
-/

public section

open Set

universe u v u' v'

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {G : Graph α β} {H : Graph α' β'}

namespace Iso

/-- Transport a set of ambient vertices along a graph isomorphism, discarding points outside the
actual vertex set. -/
def mapVertexSet (f : Iso G H) (S : Set α) : Set α' :=
  {y | ∃ hy : y ∈ V(H), (f.vertexEquiv.symm ⟨y, hy⟩ : G.vertexSet).1 ∈ S}

/-- Transport a set of ambient edges along a graph isomorphism, discarding edges outside the
actual edge set. -/
def mapEdgeSet (f : Iso G H) (F : Set β) : Set β' :=
  {e | ∃ he : e ∈ E(H), (f.edgeEquiv.symm ⟨e, he⟩ : G.edgeSet).1 ∈ F}

/-- A transported vertex set contains only actual vertices of the target graph. -/
theorem mapVertexSet_subset_vertexSet (f : Iso G H) (S : Set α) :
    f.mapVertexSet S ⊆ V(H) := by
  rintro y ⟨hy, -⟩
  exact hy

/-- A transported edge set contains only actual edges of the target graph. -/
theorem mapEdgeSet_subset_edgeSet (f : Iso G H) (F : Set β) :
    f.mapEdgeSet F ⊆ E(H) := by
  rintro e ⟨he, -⟩
  exact he

/-- Membership of an actual target vertex in a transported set is membership of its inverse
image in the original set. -/
@[simp]
theorem mem_mapVertexSet_iff (f : Iso G H) (S : Set α) (y : H.vertexSet) :
    (y : α') ∈ f.mapVertexSet S ↔ (f.vertexEquiv.symm y : α) ∈ S := by
  constructor
  · rintro ⟨hy, h⟩
    simpa only [Subtype.coe_eta] using h
  · intro h
    exact ⟨y.2, by simpa only [Subtype.coe_eta] using h⟩

/-- Membership of an actual target edge in a transported set is membership of its inverse image
in the original set. -/
@[simp]
theorem mem_mapEdgeSet_iff (f : Iso G H) (F : Set β) (e : H.edgeSet) :
    (e : β') ∈ f.mapEdgeSet F ↔ (f.edgeEquiv.symm e : β) ∈ F := by
  constructor
  · rintro ⟨he, h⟩
    simpa only [Subtype.coe_eta] using h
  · intro h
    exact ⟨e.2, by simpa only [Subtype.coe_eta] using h⟩

/-- Vertex-set transport is monotone. -/
theorem mapVertexSet_mono (f : Iso G H) {S T : Set α} (hST : S ⊆ T) :
    f.mapVertexSet S ⊆ f.mapVertexSet T := by
  rintro y ⟨hy, hS⟩
  exact ⟨hy, hST hS⟩

/-- Edge-set transport is monotone. -/
theorem mapEdgeSet_mono (f : Iso G H) {F F' : Set β} (hFF' : F ⊆ F') :
    f.mapEdgeSet F ⊆ f.mapEdgeSet F' := by
  rintro e ⟨he, hF⟩
  exact ⟨he, hFF' hF⟩

/-- Transport along an isomorphism and its inverse recovers a set of actual vertices. -/
@[simp]
theorem symm_mapVertexSet_mapVertexSet (f : Iso G H) {S : Set α} (hS : S ⊆ V(G)) :
    f.symm.mapVertexSet (f.mapVertexSet S) = S := by
  ext x
  by_cases hx : x ∈ V(G)
  · let x' : G.vertexSet := ⟨x, hx⟩
    have heq : f.symm.vertexEquiv.symm x' = f.vertexEquiv x' := by
      apply f.symm.vertexEquiv.injective
      simp
    have hx' : (x' : α) = x := rfl
    rw [← hx', f.symm.mem_mapVertexSet_iff, heq, f.mem_mapVertexSet_iff]
    simp
  · have hxS : x ∉ S := fun h ↦ hx (hS h)
    constructor
    · rintro ⟨h, -⟩
      exact (hx h).elim
    · exact fun h ↦ (hxS h).elim

/-- Transport along an isomorphism and its inverse recovers a set of actual edges. -/
@[simp]
theorem symm_mapEdgeSet_mapEdgeSet (f : Iso G H) {F : Set β} (hF : F ⊆ E(G)) :
    f.symm.mapEdgeSet (f.mapEdgeSet F) = F := by
  ext e
  by_cases he : e ∈ E(G)
  · let e' : G.edgeSet := ⟨e, he⟩
    have heq : f.symm.edgeEquiv.symm e' = f.edgeEquiv e' := by
      apply f.symm.edgeEquiv.injective
      simp
    have he' : (e' : β) = e := rfl
    rw [← he', f.symm.mem_mapEdgeSet_iff, heq, f.mem_mapEdgeSet_iff]
    simp
  · have heF : e ∉ F := fun h ↦ he (hF h)
    constructor
    · rintro ⟨h, -⟩
      exact (he h).elim
    · exact fun h ↦ (heF h).elim

/-- Transport preserves and reflects nonemptiness for sets of actual edges. -/
theorem mapEdgeSet_nonempty_iff (f : Iso G H) {F : Set β} (hF : F ⊆ E(G)) :
    (f.mapEdgeSet F).Nonempty ↔ F.Nonempty := by
  constructor
  · rintro ⟨e, he⟩
    let e' : H.edgeSet := ⟨e, f.mapEdgeSet_subset_edgeSet F he⟩
    exact ⟨f.edgeEquiv.symm e', by simpa [e'] using (f.mem_mapEdgeSet_iff F e').mp he⟩
  · rintro ⟨e, he⟩
    exact ⟨f.edgeEquiv ⟨e, hF he⟩, by simpa using he⟩

/-- An edge crosses a transported vertex side exactly when its inverse image crosses the original
side. -/
theorem edgeEquiv_mem_edgeCut_mapVertexSet_iff (f : Iso G H) (S : Set α)
    (e : G.edgeSet) :
    (f.edgeEquiv e : β') ∈ H.edgeCut (f.mapVertexSet S) ↔ (e : β) ∈ G.edgeCut S := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.2
  rw [(f.map_isLink hxy).mem_edgeCut_iff, hxy.mem_edgeCut_iff]
  simp

/-- Transporting an edge cut gives the edge cut of the transported vertex side. -/
theorem mapEdgeSet_edgeCut (f : Iso G H) (S : Set α) :
    f.mapEdgeSet (G.edgeCut S) = H.edgeCut (f.mapVertexSet S) := by
  ext e
  by_cases he : e ∈ E(H)
  · let e' : H.edgeSet := ⟨e, he⟩
    have hcut := f.edgeEquiv_mem_edgeCut_mapVertexSet_iff S (f.edgeEquiv.symm e')
    have hmem := f.mem_mapEdgeSet_iff (G.edgeCut S) e'
    simpa [e'] using hmem.trans hcut.symm
  · have hleft : e ∉ f.mapEdgeSet (G.edgeCut S) := fun h ↦
      he (f.mapEdgeSet_subset_edgeSet _ h)
    have hright : e ∉ H.edgeCut (f.mapVertexSet S) := fun h ↦
      he (H.edgeCut_subset_edgeSet h)
    exact iff_of_false hleft hright

/-- A graph isomorphism sends edge cuts to edge cuts. -/
theorem map_isEdgeCut (f : Iso G H) {F : Set β} (hF : G.IsEdgeCut F) :
    H.IsEdgeCut (f.mapEdgeSet F) := by
  rw [isEdgeCut_iff] at hF ⊢
  obtain ⟨S, rfl⟩ := hF
  exact ⟨f.mapVertexSet S, (f.mapEdgeSet_edgeCut S).symm⟩

/-- Edge-cut status is invariant under graph isomorphism for a set of actual edges. -/
theorem isEdgeCut_mapEdgeSet_iff (f : Iso G H) {F : Set β} (hF : F ⊆ E(G)) :
    H.IsEdgeCut (f.mapEdgeSet F) ↔ G.IsEdgeCut F := by
  refine ⟨fun h ↦ ?_, f.map_isEdgeCut⟩
  have h' := f.symm.map_isEdgeCut h
  rwa [f.symm_mapEdgeSet_mapEdgeSet hF] at h'

/-- Bridge status is invariant under graph isomorphism. -/
theorem isBridge_edgeEquiv_iff (f : Iso G H) (e : G.edgeSet) :
    H.IsBridge (f.edgeEquiv e) ↔ G.IsBridge e := by
  have hsingleton : f.mapEdgeSet ({(e : β)} : Set β) = {(f.edgeEquiv e : β')} := by
    ext e'
    by_cases he' : e' ∈ E(H)
    · let e'' : H.edgeSet := ⟨e', he'⟩
      have he'' : (e'' : β') = e' := rfl
      rw [← he'', f.mem_mapEdgeSet_iff]
      simp only [mem_singleton_iff]
      constructor
      · intro h
        have hpre : f.edgeEquiv.symm e'' = e := Subtype.ext h
        have himage := congrArg f.edgeEquiv hpre
        exact congrArg Subtype.val (by simpa using himage)
      · intro h
        have himage : e'' = f.edgeEquiv e := Subtype.ext h
        have hpre := congrArg f.edgeEquiv.symm himage
        exact congrArg Subtype.val (by simpa using hpre)
    · have hleft : e' ∉ f.mapEdgeSet ({(e : β)} : Set β) := fun h ↦
        he' (f.mapEdgeSet_subset_edgeSet _ h)
      have hright : e' ∉ ({(f.edgeEquiv e : β')} : Set β') := fun h ↦
        he' (h ▸ (f.edgeEquiv e).2)
      exact iff_of_false hleft hright
  have hcut := f.isEdgeCut_mapEdgeSet_iff (singleton_subset_iff.mpr e.2)
  simpa only [Graph.IsBridge, hsingleton] using hcut

/-- A graph isomorphism sends bonds to bonds. -/
theorem map_isBond (f : Iso G H) {B : Set β} (hB : G.IsBond B) :
    H.IsBond (f.mapEdgeSet B) := by
  refine ⟨⟨f.map_isEdgeCut hB.isEdgeCut,
    (f.mapEdgeSet_nonempty_iff hB.subset).2 hB.nonempty⟩, ?_⟩
  intro C hC hCB
  have hCE : C ⊆ E(H) := hC.1.subset_edgeSet
  have hpreCut : G.IsEdgeCut (f.symm.mapEdgeSet C) := f.symm.map_isEdgeCut hC.1
  have hpreNonempty : (f.symm.mapEdgeSet C).Nonempty :=
    (f.symm.mapEdgeSet_nonempty_iff hCE).2 hC.2
  have hpreB : f.symm.mapEdgeSet C ⊆ B := by
    have h := f.symm.mapEdgeSet_mono hCB
    rwa [f.symm_mapEdgeSet_mapEdgeSet hB.subset] at h
  have hBpre : B ⊆ f.symm.mapEdgeSet C := hB.2 ⟨hpreCut, hpreNonempty⟩ hpreB
  have hmap := f.mapEdgeSet_mono hBpre
  have hround := f.symm.symm_mapEdgeSet_mapEdgeSet hCE
  rw [symm_symm] at hround
  exact hmap.trans_eq hround

/-- Bond status is invariant under graph isomorphism. -/
theorem isBond_mapEdgeSet_iff (f : Iso G H) {B : Set β} (hB : B ⊆ E(G)) :
    H.IsBond (f.mapEdgeSet B) ↔ G.IsBond B := by
  refine ⟨fun h ↦ ?_, f.map_isBond⟩
  have h' := f.symm.map_isBond h
  rwa [f.symm_mapEdgeSet_mapEdgeSet hB] at h'

/-- The set of bridges is transported pointwise by a graph isomorphism. -/
theorem mapEdgeSet_bridgeSet (f : Iso G H) : f.mapEdgeSet G.bridgeSet = H.bridgeSet := by
  ext e
  by_cases he : e ∈ E(H)
  · let e' : H.edgeSet := ⟨e, he⟩
    have hmem := f.mem_mapEdgeSet_iff G.bridgeSet e'
    calc
      e ∈ f.mapEdgeSet G.bridgeSet ↔
          (f.edgeEquiv.symm e' : β) ∈ G.bridgeSet := by simpa [e'] using hmem
      _ ↔ G.IsBridge (f.edgeEquiv.symm e') := mem_bridgeSet
      _ ↔ H.IsBridge e := by simpa [e'] using
        (f.isBridge_edgeEquiv_iff (f.edgeEquiv.symm e')).symm
      _ ↔ e ∈ H.bridgeSet := mem_bridgeSet.symm
  · have hleft : e ∉ f.mapEdgeSet G.bridgeSet := fun h ↦
      he (f.mapEdgeSet_subset_edgeSet _ h)
    have hright : e ∉ H.bridgeSet := fun h ↦ he (mem_bridgeSet.mp h).mem_edgeSet
    exact iff_of_false hleft hright

/-- Being a forest is invariant under graph isomorphism. -/
theorem isForest_iff (f : Iso G H) : H.IsForest ↔ G.IsForest := by
  rw [H.isForest_iff_forall_isBridge, G.isForest_iff_forall_isBridge]
  constructor
  · intro hH e he
    exact (f.isBridge_edgeEquiv_iff ⟨e, he⟩).mp (hH (f.edgeEquiv ⟨e, he⟩).2)
  · intro hG e he
    let e' : H.edgeSet := ⟨e, he⟩
    simpa [e'] using (f.isBridge_edgeEquiv_iff (f.edgeEquiv.symm e')).mpr
      (hG (f.edgeEquiv.symm e').2)

end Iso

end Graph
