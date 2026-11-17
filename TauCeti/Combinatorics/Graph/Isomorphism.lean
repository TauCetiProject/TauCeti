/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Data.Set.Card
public import TauCeti.Combinatorics.Graph.Union

/-!
# Isomorphisms of multigraphs

An isomorphism between Mathlib multigraphs consists of equivalences between their actual vertex
and edge types which preserve the link relation. Edge identities are part of the data, so this
notion distinguishes parallel edges and retains loops.

This file supplies identity, inverse, composition, the groupoid laws, and transport of ambient
vertex and edge sets for multigraph isomorphisms. It also transports subgraphs: an isomorphism
`G ≅ H` sends each subgraph of `G` to a subgraph of `H`, compatibly with inclusion, unions, and
the groupoid operations, so that constructions recorded as sequences of subgraphs, such as ear
decompositions, can be moved between isomorphic graphs.

## Main definitions

* `Graph.Iso`: an isomorphism of multigraphs on possibly different ambient types.
* `Graph.Iso.mapVertexSet`, `Graph.Iso.mapEdgeSet`: transport of ambient sets, restricted to the
  actual graph carriers.
* `Graph.Iso.mapGraph`: transport of a graph on the ambient types, restricted to the actual graph
  carriers; on subgraphs it is the image subgraph.
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

/-- The vertex equivalence of the identity is the identity equivalence. -/
@[simp]
theorem refl_vertexEquiv (G : Graph α β) : (refl G).vertexEquiv = Equiv.refl G.vertexSet :=
  (rfl)

/-- The edge equivalence of the identity is the identity equivalence. -/
@[simp]
theorem refl_edgeEquiv (G : Graph α β) : (refl G).edgeEquiv = Equiv.refl G.edgeSet :=
  (rfl)

/-- Composition of graph isomorphisms composes their vertex equivalences. -/
@[simp]
theorem trans_vertexEquiv (f : Iso G H) (g : Iso H K) :
    (f.trans g).vertexEquiv = f.vertexEquiv.trans g.vertexEquiv :=
  (rfl)

/-- Composition of graph isomorphisms composes their edge equivalences. -/
@[simp]
theorem trans_edgeEquiv (f : Iso G H) (g : Iso H K) :
    (f.trans g).edgeEquiv = f.edgeEquiv.trans g.edgeEquiv :=
  (rfl)

/-- Inversion of a graph isomorphism inverts its vertex equivalence. -/
@[simp]
theorem symm_vertexEquiv (f : Iso G H) : f.symm.vertexEquiv = f.vertexEquiv.symm :=
  (rfl)

/-- Inversion of a graph isomorphism inverts its edge equivalence. -/
@[simp]
theorem symm_edgeEquiv (f : Iso G H) : f.symm.edgeEquiv = f.edgeEquiv.symm :=
  (rfl)

/-- Applying an isomorphism and then its inverse fixes an actual vertex. -/
theorem symm_vertexEquiv_apply_vertexEquiv (f : Iso G H) (x : G.vertexSet) :
    f.symm.vertexEquiv (f.vertexEquiv x) = x := by
  rw [symm_vertexEquiv, Equiv.symm_apply_apply]

/-- Applying an inverse isomorphism and then the original fixes an actual vertex. -/
theorem vertexEquiv_apply_symm_vertexEquiv (f : Iso G H) (x : H.vertexSet) :
    f.vertexEquiv (f.symm.vertexEquiv x) = x := by
  rw [symm_vertexEquiv, Equiv.apply_symm_apply]

/-- Applying an isomorphism and then its inverse fixes an actual edge. -/
theorem symm_edgeEquiv_apply_edgeEquiv (f : Iso G H) (e : G.edgeSet) :
    f.symm.edgeEquiv (f.edgeEquiv e) = e := by
  rw [symm_edgeEquiv, Equiv.symm_apply_apply]

/-- Applying an inverse isomorphism and then the original fixes an actual edge. -/
theorem edgeEquiv_apply_symm_edgeEquiv (f : Iso G H) (e : H.edgeSet) :
    f.edgeEquiv (f.symm.edgeEquiv e) = e := by
  rw [symm_edgeEquiv, Equiv.apply_symm_apply]

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

/-- A point lies in a transported vertex set exactly when it is the image of an actual vertex in
the original set. -/
theorem mem_mapVertexSet_iff_exists (f : Iso G H) (S : Set α) (y : α') :
    y ∈ f.mapVertexSet S ↔ ∃ x : G.vertexSet, (x : α) ∈ S ∧ (f.vertexEquiv x : α') = y :=
  ⟨fun ⟨_, h⟩ ↦ ⟨_, h, by simp⟩, fun ⟨x, hx, hxy⟩ ↦ hxy ▸ ⟨(f.vertexEquiv x).2, by simpa using hx⟩⟩

/-- An edge lies in a transported edge set exactly when it is the image of an actual edge in the
original set. -/
theorem mem_mapEdgeSet_iff_exists (f : Iso G H) (F : Set β) (e : β') :
    e ∈ f.mapEdgeSet F ↔ ∃ a : G.edgeSet, (a : β) ∈ F ∧ (f.edgeEquiv a : β') = e :=
  ⟨fun ⟨_, h⟩ ↦ ⟨_, h, by simp⟩, fun ⟨a, ha, hae⟩ ↦ hae ▸ ⟨(f.edgeEquiv a).2, by simpa using ha⟩⟩

/-- Transport preserves the extended cardinality of a set of actual edges. -/
@[simp]
theorem encard_mapEdgeSet (f : Iso G H) {F : Set β} (hF : F ⊆ E(G)) :
    (f.mapEdgeSet F).encard = F.encard := by
  apply Set.encard_congr
  exact
    { toFun := fun e ↦ ⟨(f.edgeEquiv.symm ⟨e, f.mapEdgeSet_subset_edgeSet F e.2⟩ : β),
        (f.mem_mapEdgeSet_iff F ⟨e, f.mapEdgeSet_subset_edgeSet F e.2⟩).mp e.2⟩
      invFun := fun e ↦ ⟨(f.edgeEquiv ⟨e, hF e.2⟩ : β'), by simp⟩
      left_inv := fun e ↦ by simp
      right_inv := fun e ↦ by simp }

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

/-- Transporting all actual vertices gives all actual vertices of the target. -/
@[simp]
theorem mapVertexSet_vertexSet (f : Iso G H) : f.mapVertexSet V(G) = V(H) :=
  Subset.antisymm (f.mapVertexSet_subset_vertexSet _) fun _ hy ↦ ⟨hy, (f.vertexEquiv.symm _).2⟩

/-- Transporting all actual edges gives all actual edges of the target. -/
@[simp]
theorem mapEdgeSet_edgeSet (f : Iso G H) : f.mapEdgeSet E(G) = E(H) :=
  Subset.antisymm (f.mapEdgeSet_subset_edgeSet _) fun _ he ↦ ⟨he, (f.edgeEquiv.symm _).2⟩

/-- Transporting the empty edge set gives the empty edge set. -/
@[simp]
theorem mapEdgeSet_empty (f : Iso G H) : f.mapEdgeSet (∅ : Set β) = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, h⟩ ↦ h

/-- Vertex-set transport commutes with unions. -/
@[simp]
theorem mapVertexSet_union (f : Iso G H) (S T : Set α) :
    f.mapVertexSet (S ∪ T) = f.mapVertexSet S ∪ f.mapVertexSet T := by
  ext y
  simp only [mapVertexSet, mem_union, mem_ofPred_eq, exists_or]

/-- Edge-set transport commutes with unions. -/
@[simp]
theorem mapEdgeSet_union (f : Iso G H) (F F' : Set β) :
    f.mapEdgeSet (F ∪ F') = f.mapEdgeSet F ∪ f.mapEdgeSet F' := by
  ext e
  simp only [mapEdgeSet, mem_union, mem_ofPred_eq, exists_or]

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

/-- A graph isomorphism preserves and reflects incidence between actual edges and vertices. -/
@[simp]
theorem map_inc_iff (f : Iso G H) (e : G.edgeSet) (x : G.vertexSet) :
    H.Inc (f.edgeEquiv e) (f.vertexEquiv x) ↔ G.Inc e x := by
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨_, (f.map_isLink_iff e x (f.vertexEquiv.symm ⟨y, hy.right_mem⟩)).1 ?_⟩,
    fun ⟨y, hy⟩ ↦ ⟨_, (f.map_isLink_iff e x ⟨y, hy.right_mem⟩).2 hy⟩⟩
  simpa using hy

/-! ### Transport of subgraphs -/

section mapGraph

variable {L M : Graph α β}

/-- Transport a graph on the ambient types of `G` along an isomorphism `G ≅ H`, keeping exactly
the transported actual vertices and edge identities. For a subgraph of `G` this is its image, a
subgraph of `H`. -/
def mapGraph (f : Iso G H) (L : Graph α β) : Graph α' β' :=
  (H.induce (f.mapVertexSet V(L))).restrict (f.mapEdgeSet E(L))


@[simp]
theorem vertexSet_mapGraph (f : Iso G H) (L : Graph α β) :
    V(f.mapGraph L) = f.mapVertexSet V(L) :=
  (rfl)

/-- The links of a transported graph are the links of `H` along transported edges between
transported vertices. -/
theorem mapGraph_isLink (f : Iso G H) (L : Graph α β) (e : β') (x y : α') :
    (f.mapGraph L).IsLink e x y ↔ e ∈ f.mapEdgeSet E(L) ∧ H.IsLink e x y ∧
      x ∈ f.mapVertexSet V(L) ∧ y ∈ f.mapVertexSet V(L) := by
  simp [mapGraph]

/-- A transported graph is a subgraph of the target graph. -/
theorem mapGraph_le (f : Iso G H) (L : Graph α β) : f.mapGraph L ≤ H :=
  restrict_le.trans (H.induce_le (f.mapVertexSet_subset_vertexSet _))

/-- Graph transport is monotone. -/
theorem mapGraph_mono (f : Iso G H) (hLM : L ≤ M) : f.mapGraph L ≤ f.mapGraph M where
  vertexSet_mono := f.mapVertexSet_mono hLM.vertexSet_mono
  isLink_mono e x y h := by
    rw [mapGraph_isLink] at h ⊢
    exact ⟨f.mapEdgeSet_mono hLM.edgeSet_mono h.1, h.2.1,
      f.mapVertexSet_mono hLM.vertexSet_mono h.2.2.1,
      f.mapVertexSet_mono hLM.vertexSet_mono h.2.2.2⟩

/-- For a subgraph `L ≤ G`, the transported graph links corresponding vertices by a
corresponding edge exactly when `L` links the originals. -/
@[simp]
theorem mapGraph_isLink_edgeEquiv_iff (f : Iso G H) (hL : L ≤ G) (e : G.edgeSet)
    (x y : G.vertexSet) :
    (f.mapGraph L).IsLink (f.edgeEquiv e) (f.vertexEquiv x) (f.vertexEquiv y) ↔
      L.IsLink e x y := by
  simp only [mapGraph_isLink, mem_mapEdgeSet_iff, mem_mapVertexSet_iff, map_isLink_iff,
    Equiv.symm_apply_apply]
  constructor
  · rintro ⟨he, hxy, -, -⟩
    exact (hL.isLink_iff he).mpr hxy
  · intro h
    exact ⟨h.edge_mem, h.mono hL, h.left_mem, h.right_mem⟩

/-- For a subgraph `L ≤ G`, the links of the transported graph are the links of `H` along
transported edges. -/
theorem mapGraph_isLink_of_le (f : Iso G H) (hL : L ≤ G) {e : β'} {x y : α'} :
    (f.mapGraph L).IsLink e x y ↔ e ∈ f.mapEdgeSet E(L) ∧ H.IsLink e x y := by
  refine ⟨fun h ↦ ((f.mapGraph_isLink L e x y).mp h).imp_right And.left, fun ⟨he, hxy⟩ ↦ ?_⟩
  let e' : H.edgeSet := ⟨e, hxy.edge_mem⟩
  let x' : H.vertexSet := ⟨x, hxy.left_mem⟩
  let y' : H.vertexSet := ⟨y, hxy.right_mem⟩
  have hL' : L.IsLink (f.edgeEquiv.symm e') (f.vertexEquiv.symm x') (f.vertexEquiv.symm y') :=
    (hL.isLink_iff ((f.mem_mapEdgeSet_iff _ e').mp he)).mpr
      ((f.symm.map_isLink_iff e' x' y').mpr hxy)
  have h := (f.mapGraph_isLink_edgeEquiv_iff hL _ _ _).mpr hL'
  simpa using h

/-- The edge set of a transported subgraph is the transported edge set. -/
@[simp]
theorem edgeSet_mapGraph (f : Iso G H) (hL : L ≤ G) : E(f.mapGraph L) = f.mapEdgeSet E(L) := by
  ext e
  refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
  · obtain ⟨x, _, hxy⟩ := (f.mapGraph L).exists_isLink_of_mem_edgeSet he
    exact ((f.mapGraph_isLink_of_le hL).mp hxy).1
  · obtain ⟨e', he'L, rfl⟩ : ∃ e' : G.edgeSet, (e' : β) ∈ E(L) ∧ (f.edgeEquiv e' : β') = e := by
      obtain ⟨heH, h⟩ := he
      exact ⟨_, h, by simp⟩
    obtain ⟨x, y, hxy⟩ := L.exists_isLink_of_mem_edgeSet he'L
    exact ((f.mapGraph_isLink_edgeEquiv_iff hL e' ⟨x, (hxy.mono hL).left_mem⟩
      ⟨y, (hxy.mono hL).right_mem⟩).mpr hxy).edge_mem

/-- Transporting the whole source graph gives the whole target graph. -/
@[simp]
theorem mapGraph_self (f : Iso G H) : f.mapGraph G = H :=
  (Compatible.of_le (f.mapGraph_le G)).ext (by simp) (by simp)

/-- The identity isomorphism fixes every subgraph. -/
@[simp]
theorem mapGraph_refl (hL : L ≤ G) : (refl G).mapGraph L = L :=
  (Compatible.of_le_le ((refl G).mapGraph_le L) hL).ext
    (by simp [inter_eq_left.mpr hL.vertexSet_mono])
    (by simp [edgeSet_mapGraph _ hL, inter_eq_left.mpr hL.edgeSet_mono])

/-- Transport along a composite isomorphism applies the two transports in order. -/
theorem mapGraph_trans (f : Iso G H) (g : Iso H K) (hL : L ≤ G) :
    (f.trans g).mapGraph L = g.mapGraph (f.mapGraph L) :=
  (Compatible.of_le_le ((f.trans g).mapGraph_le L) (g.mapGraph_le _)).ext (by simp)
    (by rw [edgeSet_mapGraph _ hL, edgeSet_mapGraph _ (f.mapGraph_le L),
      edgeSet_mapGraph _ hL, mapEdgeSet_trans])

/-- Transport along an isomorphism and its inverse recovers a subgraph. -/
@[simp]
theorem symm_mapGraph_mapGraph (f : Iso G H) (hL : L ≤ G) : f.symm.mapGraph (f.mapGraph L) = L := by
  rw [← mapGraph_trans _ _ hL, self_trans_symm, mapGraph_refl hL]

/-- Graph transport preserves and reflects inclusion of subgraphs. -/
@[simp]
theorem mapGraph_le_mapGraph_iff (f : Iso G H) (hL : L ≤ G) (hM : M ≤ G) :
    f.mapGraph L ≤ f.mapGraph M ↔ L ≤ M := by
  refine ⟨fun h ↦ ?_, f.mapGraph_mono⟩
  simpa [hL, hM] using f.symm.mapGraph_mono h

/-- Graph transport is injective on subgraphs. -/
theorem mapGraph_inj (f : Iso G H) (hL : L ≤ G) (hM : M ≤ G) :
    f.mapGraph L = f.mapGraph M ↔ L = M := by
  refine ⟨fun h ↦ ?_, congrArg _⟩
  rw [← f.symm_mapGraph_mapGraph hL, h, f.symm_mapGraph_mapGraph hM]

/-- An isomorphism transports an edgeless single-vertex graph to the edgeless graph on the
corresponding vertex. -/
@[simp]
theorem mapGraph_noEdge (f : Iso G H) (x : G.vertexSet) :
    f.mapGraph (noEdge {(x : α)} β) = noEdge {(f.vertexEquiv x : α')} β' := by
  exact (Compatible.of_le_le (f.mapGraph_le _)
    (noEdge_le_iff.mpr (singleton_subset_iff.mpr (f.vertexEquiv x).2))).ext (by simp)
    (by simp)

/-- Graph transport commutes with the union of compatible subgraphs. -/
theorem mapGraph_union (f : Iso G H) (hL : L ≤ G) (hM : M ≤ G) (h : L.Compatible M) :
    f.mapGraph h.union =
      (Compatible.of_le_le (f.mapGraph_le L) (f.mapGraph_le M)).union := by
  have hLM : h.union ≤ G := IsSubgraph.union_le hL hM
  exact (Compatible.of_le_le (f.mapGraph_le _)
    (IsSubgraph.union_le (f.mapGraph_le L) (f.mapGraph_le M))).ext (by simp)
    (by simp [edgeSet_mapGraph f hLM, edgeSet_mapGraph f hL, edgeSet_mapGraph f hM])

end mapGraph

end Iso

end Graph
