/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Basic

/-!
# Isomorphisms of multigraphs

An isomorphism between Mathlib multigraphs consists of equivalences between their actual vertex
and edge types which preserve the link relation. Edge identities are part of the data, so this
notion distinguishes parallel edges and retains loops.

This file supplies identity, inverse, composition, the groupoid laws, and transport of ambient
vertex and edge sets for multigraph isomorphisms.

## Main definitions

* `Graph.Iso`: an isomorphism of multigraphs on possibly different ambient types.
* `Graph.Iso.mapVertexSet`, `Graph.Iso.mapEdgeSet`: transport of ambient sets, restricted to the
  actual graph carriers.
-/

public section

open Set

universe u v u' v' u'' v''

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {α'' : Type u''} {β'' : Type v''}
variable {G : Graph α β} {H : Graph α' β'} {K : Graph α'' β''}

/-- An isomorphism of multigraphs is an equivalence of their actual vertices and actual edges
which preserves the link relation. -/
@[ext]
structure Iso (G : Graph α β) (H : Graph α' β') where
  /-- The equivalence between actual vertices. -/
  vertexEquiv : G.vertexSet ≃ H.vertexSet
  /-- The equivalence between actual edge identities. -/
  edgeEquiv : G.edgeSet ≃ H.edgeSet
  /-- Corresponding edges link corresponding vertices. -/
  map_isLink_iff : ∀ (e : G.edgeSet) (x y : G.vertexSet),
    H.IsLink (edgeEquiv e) (vertexEquiv x) (vertexEquiv y) ↔ G.IsLink e x y

namespace Iso

attribute [simp] map_isLink_iff

/-- The identity isomorphism of a multigraph. -/
@[refl]
def refl (G : Graph α β) : Iso G G where
  vertexEquiv := Equiv.refl G.vertexSet
  edgeEquiv := Equiv.refl G.edgeSet
  map_isLink_iff _ _ _ := Iff.rfl

/-- The composite of two multigraph isomorphisms. -/
@[trans]
def trans (f : Iso G H) (g : Iso H K) : Iso G K where
  vertexEquiv := f.vertexEquiv.trans g.vertexEquiv
  edgeEquiv := f.edgeEquiv.trans g.edgeEquiv
  map_isLink_iff e x y := (g.map_isLink_iff (f.edgeEquiv e)
    (f.vertexEquiv x) (f.vertexEquiv y)).trans (f.map_isLink_iff e x y)

/-- The inverse of a multigraph isomorphism. -/
@[symm]
def symm (f : Iso G H) : Iso H G where
  vertexEquiv := f.vertexEquiv.symm
  edgeEquiv := f.edgeEquiv.symm
  map_isLink_iff e x y := by
    rw [← f.map_isLink_iff (f.edgeEquiv.symm e) (f.vertexEquiv.symm x)
      (f.vertexEquiv.symm y)]
    simp

/-- The identity isomorphism fixes actual vertices. -/
@[simp]
theorem refl_vertexEquiv_apply (G : Graph α β) (x : G.vertexSet) :
    (refl G).vertexEquiv x = x :=
  (rfl)

/-- The identity isomorphism fixes actual edges. -/
@[simp]
theorem refl_edgeEquiv_apply (G : Graph α β) (e : G.edgeSet) :
    (refl G).edgeEquiv e = e :=
  (rfl)

/-- A composite isomorphism applies the two vertex equivalences in order. -/
@[simp]
theorem trans_vertexEquiv_apply (f : Iso G H) (g : Iso H K) (x : G.vertexSet) :
    (f.trans g).vertexEquiv x = g.vertexEquiv (f.vertexEquiv x) :=
  (rfl)

/-- A composite isomorphism applies the two edge equivalences in order. -/
@[simp]
theorem trans_edgeEquiv_apply (f : Iso G H) (g : Iso H K) (e : G.edgeSet) :
    (f.trans g).edgeEquiv e = g.edgeEquiv (f.edgeEquiv e) :=
  (rfl)

/-- The inverse isomorphism applies the inverse vertex equivalence. -/
@[simp]
theorem symm_vertexEquiv_apply (f : Iso G H) (x : H.vertexSet) :
    f.symm.vertexEquiv x = f.vertexEquiv.symm x :=
  (rfl)

/-- The inverse isomorphism applies the inverse edge equivalence. -/
@[simp]
theorem symm_edgeEquiv_apply (f : Iso G H) (e : H.edgeSet) :
    f.symm.edgeEquiv e = f.edgeEquiv.symm e :=
  (rfl)

/-- Applying an isomorphism and then its inverse fixes an actual vertex. -/
theorem symm_vertexEquiv_apply_vertexEquiv (f : Iso G H) (x : G.vertexSet) :
    f.symm.vertexEquiv (f.vertexEquiv x) = x := by
  rw [symm_vertexEquiv_apply, Equiv.symm_apply_apply]

/-- Applying an inverse isomorphism and then the original fixes an actual vertex. -/
theorem vertexEquiv_apply_symm_vertexEquiv (f : Iso G H) (x : H.vertexSet) :
    f.vertexEquiv (f.symm.vertexEquiv x) = x := by
  rw [symm_vertexEquiv_apply, Equiv.apply_symm_apply]

/-- Applying an isomorphism and then its inverse fixes an actual edge. -/
theorem symm_edgeEquiv_apply_edgeEquiv (f : Iso G H) (e : G.edgeSet) :
    f.symm.edgeEquiv (f.edgeEquiv e) = e := by
  rw [symm_edgeEquiv_apply, Equiv.symm_apply_apply]

/-- Applying an inverse isomorphism and then the original fixes an actual edge. -/
theorem edgeEquiv_apply_symm_edgeEquiv (f : Iso G H) (e : H.edgeSet) :
    f.edgeEquiv (f.symm.edgeEquiv e) = e := by
  rw [symm_edgeEquiv_apply, Equiv.apply_symm_apply]

/-- Inverting a graph isomorphism twice returns the original isomorphism. -/
@[simp]
theorem symm_symm (f : Iso G H) : f.symm.symm = f := by
  ext <;> rfl

/-- The identity graph isomorphism is self-inverse. -/
@[simp]
theorem refl_symm (G : Graph α β) : (refl G).symm = refl G := by
  rfl

/-- Composing the identity isomorphism on the left changes nothing. -/
@[simp]
theorem refl_trans (f : Iso G H) : (refl G).trans f = f := by
  ext <;> rfl

/-- Composing the identity isomorphism on the right changes nothing. -/
@[simp]
theorem trans_refl (f : Iso G H) : f.trans (refl H) = f := by
  ext <;> rfl

/-- Composition of graph isomorphisms is associative. -/
@[simp]
theorem trans_assoc (f : Iso G H) (g : Iso H K)
    {α''' β''' : Type*} {L : Graph α''' β'''} (h : Iso K L) :
    (f.trans g).trans h = f.trans (g.trans h) := by
  ext <;> rfl

/-- Composing a graph isomorphism with its inverse gives the identity. -/
@[simp]
theorem self_trans_symm (f : Iso G H) : f.trans f.symm = refl G := by
  ext <;> simp

/-- Composing the inverse of a graph isomorphism with it gives the identity. -/
@[simp]
theorem symm_trans_self (f : Iso G H) : f.symm.trans f = refl H := by
  ext <;> simp

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

/-- Transporting a vertex set along the identity isomorphism intersects it with the actual
vertex set. -/
@[simp]
theorem mapVertexSet_refl (G : Graph α β) (S : Set α) :
    (refl G).mapVertexSet S = S ∩ V(G) := by
  ext x
  constructor
  · rintro ⟨hx, hS⟩
    exact ⟨hS, hx⟩
  · rintro ⟨hS, hx⟩
    exact ⟨hx, hS⟩

/-- Transporting an edge set along the identity isomorphism intersects it with the actual edge
set. -/
@[simp]
theorem mapEdgeSet_refl (G : Graph α β) (F : Set β) :
    (refl G).mapEdgeSet F = F ∩ E(G) := by
  ext e
  constructor
  · rintro ⟨he, hF⟩
    exact ⟨hF, he⟩
  · rintro ⟨hF, he⟩
    exact ⟨he, hF⟩

/-- Transporting a vertex set along a composite applies the two transports in order. -/
@[simp]
theorem mapVertexSet_trans (f : Iso G H) (g : Iso H K) (S : Set α) :
    (f.trans g).mapVertexSet S = g.mapVertexSet (f.mapVertexSet S) := by
  ext z
  by_cases hz : z ∈ V(K)
  · let z' : K.vertexSet := ⟨z, hz⟩
    have hz' : (z' : α'') = z := rfl
    rw [← hz', (f.trans g).mem_mapVertexSet_iff, g.mem_mapVertexSet_iff,
      f.mem_mapVertexSet_iff]
    rfl
  · have hleft : z ∉ (f.trans g).mapVertexSet S := fun h ↦
      hz ((f.trans g).mapVertexSet_subset_vertexSet S h)
    have hright : z ∉ g.mapVertexSet (f.mapVertexSet S) := fun h ↦
      hz (g.mapVertexSet_subset_vertexSet _ h)
    exact iff_of_false hleft hright

/-- Transporting an edge set along a composite applies the two transports in order. -/
@[simp]
theorem mapEdgeSet_trans (f : Iso G H) (g : Iso H K) (F : Set β) :
    (f.trans g).mapEdgeSet F = g.mapEdgeSet (f.mapEdgeSet F) := by
  ext e
  by_cases he : e ∈ E(K)
  · let e' : K.edgeSet := ⟨e, he⟩
    have he' : (e' : β'') = e := rfl
    rw [← he', (f.trans g).mem_mapEdgeSet_iff, g.mem_mapEdgeSet_iff,
      f.mem_mapEdgeSet_iff]
    rfl
  · have hleft : e ∉ (f.trans g).mapEdgeSet F := fun h ↦
      he ((f.trans g).mapEdgeSet_subset_edgeSet F h)
    have hright : e ∉ g.mapEdgeSet (f.mapEdgeSet F) := fun h ↦
      he (g.mapEdgeSet_subset_edgeSet _ h)
    exact iff_of_false hleft hright

/-- A graph isomorphism transports a singleton actual vertex to the corresponding singleton. -/
@[simp]
theorem mapVertexSet_singleton (f : Iso G H) (x : G.vertexSet) :
    f.mapVertexSet ({(x : α)} : Set α) = {(f.vertexEquiv x : α')} := by
  ext y
  by_cases hy : y ∈ V(H)
  · let y' : H.vertexSet := ⟨y, hy⟩
    have hy' : (y' : α') = y := rfl
    rw [← hy', f.mem_mapVertexSet_iff]
    simp only [mem_singleton_iff, Subtype.coe_inj, Equiv.symm_apply_eq]
  · have hleft : y ∉ f.mapVertexSet ({(x : α)} : Set α) := fun h ↦
      hy (f.mapVertexSet_subset_vertexSet _ h)
    have hright : y ∉ ({(f.vertexEquiv x : α')} : Set α') := fun h ↦
      hy (h ▸ (f.vertexEquiv x).2)
    exact iff_of_false hleft hright

/-- A graph isomorphism transports a singleton actual edge to the corresponding singleton. -/
@[simp]
theorem mapEdgeSet_singleton (f : Iso G H) (e : G.edgeSet) :
    f.mapEdgeSet ({(e : β)} : Set β) = {(f.edgeEquiv e : β')} := by
  ext e'
  by_cases he' : e' ∈ E(H)
  · let e'' : H.edgeSet := ⟨e', he'⟩
    have he'' : (e'' : β') = e' := rfl
    rw [← he'', f.mem_mapEdgeSet_iff]
    simp only [mem_singleton_iff, Subtype.coe_inj, Equiv.symm_apply_eq]
  · have hleft : e' ∉ f.mapEdgeSet ({(e : β)} : Set β) := fun h ↦
      he' (f.mapEdgeSet_subset_edgeSet _ h)
    have hright : e' ∉ ({(f.edgeEquiv e : β')} : Set β') := fun h ↦
      he' (h ▸ (f.edgeEquiv e).2)
    exact iff_of_false hleft hright

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
  rw [← mapVertexSet_trans, self_trans_symm, mapVertexSet_refl, inter_eq_left.mpr hS]

/-- Transport along an isomorphism and its inverse recovers a set of actual edges. -/
@[simp]
theorem symm_mapEdgeSet_mapEdgeSet (f : Iso G H) {F : Set β} (hF : F ⊆ E(G)) :
    f.symm.mapEdgeSet (f.mapEdgeSet F) = F := by
  rw [← mapEdgeSet_trans, self_trans_symm, mapEdgeSet_refl, inter_eq_left.mpr hF]

/-- Transport preserves and reflects nonemptiness for sets of actual edges. -/
theorem mapEdgeSet_nonempty_iff (f : Iso G H) {F : Set β} (hF : F ⊆ E(G)) :
    (f.mapEdgeSet F).Nonempty ↔ F.Nonempty := by
  constructor
  · rintro ⟨e, he⟩
    let e' : H.edgeSet := ⟨e, f.mapEdgeSet_subset_edgeSet F he⟩
    exact ⟨f.edgeEquiv.symm e', by simpa [e'] using (f.mem_mapEdgeSet_iff F e').mp he⟩
  · rintro ⟨e, he⟩
    exact ⟨f.edgeEquiv ⟨e, hF he⟩, by simpa using he⟩

/-- A graph isomorphism sends a link to a link. -/
theorem map_isLink (f : Iso G H) {e : β} {x y : α} (he : G.IsLink e x y) :
    H.IsLink (f.edgeEquiv ⟨e, he.edge_mem⟩) (f.vertexEquiv ⟨x, he.left_mem⟩)
      (f.vertexEquiv ⟨y, he.right_mem⟩) :=
  (f.map_isLink_iff ⟨e, he.edge_mem⟩ ⟨x, he.left_mem⟩ ⟨y, he.right_mem⟩).2 he

end Iso

end Graph
