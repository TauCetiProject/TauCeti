/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Contraction
import Mathlib.Algebra.BigOperators.Fin

/-!
# Isomorphisms of dual graphs

The dual graph of a pointed nodal curve is determined by the curve only up to relabelling its
components and its nodes, and the two branches of a node come in no preferred order. An
**isomorphism** of dual graphs `G ≅ H` is therefore a pair of bijections, between the vertices and
between the edges, which carries the unordered pair of endpoints `TauCeti.DualGraph.ends` of each
edge to that of its image and preserves the genera of the components and the components carrying
the markings. An edge may be carried to an edge whose endpoints are listed in the opposite order.

All numerical invariants of a dual graph are invariant under isomorphism: valences, numbers of
markings, log-canonical degrees, the first Betti number and the arithmetic genus, hence stability,
semistability, and being a rational tail or a rational bridge. Contraction of a tail or of a
bridge is compatible with isomorphisms, so a stabilization step can be transported along an
isomorphism: an isomorphic graph admits a corresponding step with an isomorphic result.

## Main definitions

* `TauCeti.DualGraph.Iso G H`: the isomorphisms from `G` to `H`, with `Iso.refl`, `Iso.symm` and
  `Iso.trans`.
* `TauCeti.DualGraph.Iso.ofInjective`: an isomorphism from bijections whose compatibility is
  checked after an injective map of the vertices into a common type, as for two graphs obtained
  from a third by deleting the same vertices.
* `TauCeti.DualGraph.Iso.contractTail` and `TauCeti.DualGraph.Iso.contractBridge`: the
  isomorphisms of contractions induced by an isomorphism.

## Main results

* `TauCeti.DualGraph.Iso.valence_vertexEquiv`, `TauCeti.DualGraph.Iso.numMarkings_vertexEquiv`
  and `TauCeti.DualGraph.Iso.logCanonicalDegree_vertexEquiv`: the local invariants are preserved.
* `TauCeti.DualGraph.Iso.arithmeticGenus_eq` and `TauCeti.DualGraph.Iso.isStable_iff`: so are
  the arithmetic genus and stability.
* `TauCeti.DualGraph.StabilizationStep.exists_iso`: a stabilization step transported along an
  isomorphism, and `TauCeti.DualGraph.exists_reflTransGen_iso`, its iterate.

## References

* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*,
  Chapter X, §2, for isomorphisms of dual graphs of pointed nodal curves.
-/

public section

namespace TauCeti

namespace DualGraph

open Finset Function

universe u u' u'' v w

variable {ι : Type v}

/-- An **isomorphism** of dual graphs: bijections of the vertices and of the edges, carrying the
unordered pair of endpoints of each edge to that of its image, and preserving the genera of the
components and the components carrying the markings. -/
@[ext]
structure Iso (G : DualGraph.{u} ι) (H : DualGraph.{u'} ι) where
  /-- The bijection of vertices. -/
  vertexEquiv : G.Vertex ≃ H.Vertex
  /-- The bijection of edges. -/
  edgeEquiv : G.Edge ≃ H.Edge
  /-- An edge is carried to an edge joining the images of its endpoints, in either order. -/
  ends_edgeEquiv (e : G.Edge) : H.ends (edgeEquiv e) = (G.ends e).map vertexEquiv
  /-- The genera of the components are preserved. -/
  genus_vertexEquiv (v : G.Vertex) : H.genus (vertexEquiv v) = G.genus v
  /-- The components carrying the markings correspond. -/
  vertexEquiv_marking (i : ι) : vertexEquiv (G.marking i) = H.marking i

attribute [simp] Iso.ends_edgeEquiv Iso.genus_vertexEquiv Iso.vertexEquiv_marking

namespace Iso

variable {G : DualGraph.{u} ι} {H : DualGraph.{u'} ι} {K : DualGraph.{u''} ι}

/-- The identity isomorphism. -/
def refl (G : DualGraph.{u} ι) : G.Iso G where
  vertexEquiv := .refl _
  edgeEquiv := .refl _
  ends_edgeEquiv _ := by simp
  genus_vertexEquiv _ := rfl
  vertexEquiv_marking _ := rfl

/-- The identity isomorphism is the identity on vertices. -/
@[simp]
theorem refl_vertexEquiv (G : DualGraph.{u} ι) : (refl G).vertexEquiv = .refl _ := (rfl)

/-- The identity isomorphism is the identity on edges. -/
@[simp]
theorem refl_edgeEquiv (G : DualGraph.{u} ι) : (refl G).edgeEquiv = .refl _ := (rfl)

/-- The inverse isomorphism. -/
def symm (f : G.Iso H) : H.Iso G where
  vertexEquiv := f.vertexEquiv.symm
  edgeEquiv := f.edgeEquiv.symm
  ends_edgeEquiv e := by
    obtain ⟨e, rfl⟩ := f.edgeEquiv.surjective e
    simp [Sym2.map_map]
  genus_vertexEquiv v := by
    obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective v
    simp
  vertexEquiv_marking i := by rw [← f.vertexEquiv_marking, Equiv.symm_apply_apply]

/-- The inverse isomorphism acts on vertices by the inverse bijection. -/
@[simp]
theorem symm_vertexEquiv (f : G.Iso H) : f.symm.vertexEquiv = f.vertexEquiv.symm := (rfl)

/-- The inverse isomorphism acts on edges by the inverse bijection. -/
@[simp]
theorem symm_edgeEquiv (f : G.Iso H) : f.symm.edgeEquiv = f.edgeEquiv.symm := (rfl)

/-- The composite of two isomorphisms. -/
def trans (f : G.Iso H) (g : H.Iso K) : G.Iso K where
  vertexEquiv := f.vertexEquiv.trans g.vertexEquiv
  edgeEquiv := f.edgeEquiv.trans g.edgeEquiv
  ends_edgeEquiv e := by simp [Sym2.map_map, Function.comp_def]
  genus_vertexEquiv v := by simp
  vertexEquiv_marking i := by simp

/-- The composite isomorphism acts on vertices by the composite bijection. -/
@[simp]
theorem trans_vertexEquiv (f : G.Iso H) (g : H.Iso K) :
    (f.trans g).vertexEquiv = f.vertexEquiv.trans g.vertexEquiv := (rfl)

/-- The composite isomorphism acts on edges by the composite bijection. -/
@[simp]
theorem trans_edgeEquiv (f : G.Iso H) (g : H.Iso K) :
    (f.trans g).edgeEquiv = f.edgeEquiv.trans g.edgeEquiv := (rfl)

/-- Build an isomorphism from bijections of vertices and edges whose compatibility with the ends of
edges and with the markings is checked after mapping the vertices of both graphs into a common
type `α`, injectively on the target. This applies to two graphs obtained from a third one by
deleting the same vertices, both of whose vertices are vertices of the third graph. -/
def ofInjective {α : Type w} (p : G.Vertex → α) (q : H.Vertex → α) (hq : Injective q)
    (σ : G.Vertex ≃ H.Vertex) (hσ : ∀ v, q (σ v) = p v) (τ : G.Edge ≃ H.Edge)
    (hτ : ∀ e, (H.ends (τ e)).map q = (G.ends e).map p)
    (hgenus : ∀ v, H.genus (σ v) = G.genus v) (hmarking : ∀ i, q (H.marking i) = p (G.marking i)) :
    G.Iso H where
  vertexEquiv := σ
  edgeEquiv := τ
  ends_edgeEquiv e := Sym2.map.injective hq <| by
    rw [hτ, Sym2.map_map]
    exact congrArg (Sym2.map · (G.ends e)) (funext fun v ↦ (hσ v).symm)
  genus_vertexEquiv := hgenus
  vertexEquiv_marking i := hq (by rw [hσ, hmarking])

section ofInjective

variable {α : Type w} (p : G.Vertex → α) (q : H.Vertex → α) (hq : Injective q)
  (σ : G.Vertex ≃ H.Vertex) (hσ : ∀ v, q (σ v) = p v) (τ : G.Edge ≃ H.Edge)
  (hτ : ∀ e, (H.ends (τ e)).map q = (G.ends e).map p)
  (hgenus : ∀ v, H.genus (σ v) = G.genus v) (hmarking : ∀ i, q (H.marking i) = p (G.marking i))

/-- The isomorphism `Iso.ofInjective` acts on vertices by the given bijection. -/
@[simp]
theorem ofInjective_vertexEquiv :
    (ofInjective p q hq σ hσ τ hτ hgenus hmarking).vertexEquiv = σ := (rfl)

/-- The isomorphism `Iso.ofInjective` acts on edges by the given bijection. -/
@[simp]
theorem ofInjective_edgeEquiv :
    (ofInjective p q hq σ hσ τ hτ hgenus hmarking).edgeEquiv = τ := (rfl)

end ofInjective

variable (f : G.Iso H)

include f

/-- A vertex lies on an edge exactly when its image lies on the image of the edge. -/
theorem mem_ends_edgeEquiv {v : G.Vertex} {e : G.Edge} :
    f.vertexEquiv v ∈ H.ends (f.edgeEquiv e) ↔ v ∈ G.ends e := by
  rw [ends_edgeEquiv, Sym2.mem_map]
  simp

/-- An edge avoids a vertex exactly when its image avoids the image of the vertex. -/
theorem forall_endpoint_edgeEquiv_ne_iff {v : G.Vertex} {e : G.Edge} :
    (∀ i, H.endpoint (f.edgeEquiv e) i ≠ f.vertexEquiv v) ↔ ∀ i, G.endpoint e i ≠ v := by
  rw [forall_endpoint_ne_iff, forall_endpoint_ne_iff, mem_ends_edgeEquiv]

/-- Each branch of an edge is carried to a branch of its image, the other branch going to the
other branch. -/
theorem exists_endpoint_edgeEquiv (e : G.Edge) (i : Fin 2) :
    ∃ j, H.endpoint (f.edgeEquiv e) j = f.vertexEquiv (G.endpoint e i) ∧
      H.endpoint (f.edgeEquiv e) j.rev = f.vertexEquiv (G.endpoint e i.rev) := by
  have := f.ends_edgeEquiv e
  rw [ends_def, ends_def, Sym2.map_mk, Sym2.eq_iff] at this
  rcases this with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ <;> fin_cases i
  exacts [⟨0, h₀, h₁⟩, ⟨1, h₁, h₀⟩, ⟨1, h₁, h₀⟩, ⟨0, h₀, h₁⟩]

/-- The ends of the image of an edge, with the endpoints listed explicitly. -/
theorem mk_endpoint_edgeEquiv (e : G.Edge) :
    s(H.endpoint (f.edgeEquiv e) 0, H.endpoint (f.edgeEquiv e) 1) =
      s(f.vertexEquiv (G.endpoint e 0), f.vertexEquiv (G.endpoint e 1)) := by
  simpa only [ends_def, Sym2.map_mk] using f.ends_edgeEquiv e

/-- Isomorphisms preserve valences. -/
@[simp]
theorem valence_vertexEquiv (v : G.Vertex) : H.valence (f.vertexEquiv v) = G.valence v := by
  rw [valence_eq_sum, valence_eq_sum, ← f.edgeEquiv.sum_comp]
  refine sum_congr rfl fun e _ ↦ ?_
  -- The number of branches of an edge at a vertex only depends on its unordered pair of ends.
  rcases Sym2.eq_iff.mp (f.mk_endpoint_edgeEquiv e) with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ <;>
    simp [card_filter, Fin.sum_univ_two, h₀, h₁, add_comm, -sum_boole]

/-- Isomorphisms preserve the numbers of markings. -/
@[simp]
theorem numMarkings_vertexEquiv [Fintype ι] (v : G.Vertex) :
    H.numMarkings (f.vertexEquiv v) = G.numMarkings v := by
  simp only [numMarkings_def, ← f.vertexEquiv_marking, f.vertexEquiv.injective.eq_iff]

/-- Isomorphisms preserve log-canonical degrees. -/
@[simp]
theorem logCanonicalDegree_vertexEquiv [Fintype ι] (v : G.Vertex) :
    H.logCanonicalDegree (f.vertexEquiv v) = G.logCanonicalDegree v := by
  simp [logCanonicalDegree_def]

/-- Isomorphic graphs have the same number of vertices. -/
theorem card_vertex_eq : Fintype.card G.Vertex = Fintype.card H.Vertex :=
  Fintype.card_congr f.vertexEquiv

/-- Isomorphic graphs have the same number of edges. -/
theorem card_edge_eq : Fintype.card G.Edge = Fintype.card H.Edge :=
  Fintype.card_congr f.edgeEquiv

/-- Isomorphic graphs have the same first Betti number. -/
theorem firstBetti_eq : G.firstBetti = H.firstBetti := by
  rw [firstBetti_def, firstBetti_def, f.card_vertex_eq, f.card_edge_eq]

/-- Isomorphic graphs have the same arithmetic genus. -/
theorem arithmeticGenus_eq : G.arithmeticGenus = H.arithmeticGenus := by
  rw [arithmeticGenus_def, arithmeticGenus_def, f.firstBetti_eq, ← f.vertexEquiv.sum_comp]
  simp

/-- A vertex is a rational tail exactly when its image is. -/
@[simp]
theorem isRationalTail_vertexEquiv_iff {v : G.Vertex} :
    H.IsRationalTail (f.vertexEquiv v) ↔ G.IsRationalTail v := by
  simp [isRationalTail_iff]

/-- A vertex carries no loop exactly when its image carries none. -/
theorem forall_endpoint_one_ne_vertexEquiv_iff {v : G.Vertex} :
    (∀ e, H.endpoint e 0 = f.vertexEquiv v → H.endpoint e 1 ≠ f.vertexEquiv v) ↔
      ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v := by
  rw [forall_endpoint_one_ne_iff, forall_endpoint_one_ne_iff, ← f.edgeEquiv.forall_congr_right]
  refine forall_congr' fun e ↦ ?_
  rw [ends_edgeEquiv, ← Sym2.map_mk, (Sym2.map.injective f.vertexEquiv.injective).ne_iff]

/-- A vertex is a rational bridge exactly when its image is. -/
@[simp]
theorem isRationalBridge_vertexEquiv_iff {v : G.Vertex} :
    H.IsRationalBridge (f.vertexEquiv v) ↔ G.IsRationalBridge v := by
  simp [isRationalBridge_iff, f.forall_endpoint_one_ne_vertexEquiv_iff]

/-- Isomorphic graphs are simultaneously stable. -/
theorem isStable_iff [Fintype ι] : G.IsStable ↔ H.IsStable := by
  simp only [DualGraph.isStable_iff, ← f.vertexEquiv.forall_congr_right,
    logCanonicalDegree_vertexEquiv]

/-- Isomorphic graphs are simultaneously semistable. -/
theorem isSemistable_iff [Fintype ι] : G.IsSemistable ↔ H.IsSemistable := by
  simp only [DualGraph.isSemistable_iff, ← f.vertexEquiv.forall_congr_right,
    logCanonicalDegree_vertexEquiv]

/-- Isomorphisms carry the attachment of a vertex of valence one to the attachment of its
image. -/
theorem vertexEquiv_attachment {v : G.Vertex} (hv : G.valence v = 1)
    (hv' : H.valence (f.vertexEquiv v) = 1) :
    f.vertexEquiv (G.attachment hv) = H.attachment hv' := by
  obtain ⟨⟨e, i⟩, he⟩ := exists_endpoint_eq_of_valence_pos (G := G) (by omega : 0 < G.valence v)
  obtain ⟨j, hj, hj'⟩ := f.exists_endpoint_edgeEquiv e i
  rw [← endpoint_rev_eq_attachment hv he, ← hj',
    endpoint_rev_eq_attachment hv' (hj.trans (congrArg _ he))]

/-- Isomorphisms carry the unordered pair of neighbours of a loopless vertex of valence two to
that of its image. -/
theorem sym2_bridgeNeighbor {v : G.Vertex} (hv : G.valence v = 2)
    (hloop : ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v)
    (hv' : H.valence (f.vertexEquiv v) = 2) :
    s(H.bridgeNeighbor hv' 0, H.bridgeNeighbor hv' 1) =
      s(f.vertexEquiv (G.bridgeNeighbor hv 0), f.vertexEquiv (G.bridgeNeighbor hv 1)) := by
  obtain ⟨j₀, hj₀, hj₀'⟩ := f.exists_endpoint_edgeEquiv (G.halfEdgeOfValenceEqTwo hv 0).1.1
    (G.halfEdgeOfValenceEqTwo hv 0).1.2
  obtain ⟨j₁, hj₁, hj₁'⟩ := f.exists_endpoint_edgeEquiv (G.halfEdgeOfValenceEqTwo hv 1).1.1
    (G.halfEdgeOfValenceEqTwo hv 1).1.2
  rw [(G.halfEdgeOfValenceEqTwo hv 0).2] at hj₀
  rw [(G.halfEdgeOfValenceEqTwo hv 1).2] at hj₁
  have hne := halfEdgeOfValenceEqTwo_fst_ne hv hloop
  rw [H.sym2_bridgeNeighbor_eq hv' (h := (_, j₀)) (h' := (_, j₁)) hj₀ hj₁
    fun h ↦ hne (f.edgeEquiv.injective (congrArg Prod.fst h)), hj₀', hj₁',
    endpoint_halfEdgeOfValenceEqTwo_rev, endpoint_halfEdgeOfValenceEqTwo_rev]

/-- The isomorphism of tail contractions induced by an isomorphism. -/
noncomputable def contractTail {v : G.Vertex} (hv : G.valence v = 1)
    (hv' : H.valence (f.vertexEquiv v) = 1) :
    (G.contractTail hv).Iso (H.contractTail hv') :=
  ofInjective (f.vertexEquiv ∘ Subtype.val) Subtype.val Subtype.val_injective
    (f.vertexEquiv.subtypeEquiv fun _ ↦ f.vertexEquiv.injective.ne_iff.symm) (fun _ ↦ rfl)
    (f.edgeEquiv.subtypeEquiv fun _ ↦ f.forall_endpoint_edgeEquiv_ne_iff.symm)
    (fun e ↦ by rw [← Sym2.map_map, map_val_ends_contractTail, map_val_ends_contractTail]; simp)
    (fun _ ↦ by simp) fun i ↦ by
      by_cases h : G.marking i = v
      · have h' : H.marking i = f.vertexEquiv v := by rw [← f.vertexEquiv_marking, h]
        rw [marking_contractTail, marking_contractTail, dite_eq_left h, dite_eq_left h']
        exact (f.vertexEquiv_attachment hv hv').symm
      · have h' : H.marking i ≠ f.vertexEquiv v := by
          rw [← f.vertexEquiv_marking]
          exact f.vertexEquiv.injective.ne h
        rw [marking_contractTail, marking_contractTail, dite_eq_right h, dite_eq_right h']
        exact (f.vertexEquiv_marking i).symm

/-- The isomorphism of tail contractions acts on vertices as the original isomorphism. -/
@[simp]
theorem coe_contractTail_vertexEquiv_apply {v : G.Vertex} (hv : G.valence v = 1)
    (hv' : H.valence (f.vertexEquiv v) = 1) (w : (G.contractTail hv).Vertex) :
    ((f.contractTail hv hv').vertexEquiv w : H.Vertex) = f.vertexEquiv w := by
  rfl

/-- The isomorphism of tail contractions acts on edges as the original isomorphism. -/
@[simp]
theorem coe_contractTail_edgeEquiv_apply {v : G.Vertex} (hv : G.valence v = 1)
    (hv' : H.valence (f.vertexEquiv v) = 1) (e : (G.contractTail hv).Edge) :
    ((f.contractTail hv hv').edgeEquiv e : H.Edge) = f.edgeEquiv e := by
  rfl

/-- The isomorphism of bridge contractions induced by an isomorphism. -/
noncomputable def contractBridge {v : G.Vertex} (hv : G.valence v = 2)
    (hloop : ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v) (hm : ∀ i, G.marking i ≠ v)
    (hv' : H.valence (f.vertexEquiv v) = 2)
    (hloop' : ∀ e, H.endpoint e 0 = f.vertexEquiv v → H.endpoint e 1 ≠ f.vertexEquiv v)
    (hm' : ∀ i, H.marking i ≠ f.vertexEquiv v) :
    (G.contractBridge hv hloop hm).Iso (H.contractBridge hv' hloop' hm') :=
  ofInjective (f.vertexEquiv ∘ Subtype.val) Subtype.val Subtype.val_injective
    (f.vertexEquiv.subtypeEquiv fun _ ↦ f.vertexEquiv.injective.ne_iff.symm) (fun _ ↦ rfl)
    (Equiv.optionCongr (f.edgeEquiv.subtypeEquiv fun _ ↦ f.forall_endpoint_edgeEquiv_ne_iff.symm))
    (fun e ↦ by
      rw [← Sym2.map_map]
      cases e with
      | none => simpa using f.sym2_bridgeNeighbor hv hloop hv'
      | some e => simp)
    (fun _ ↦ by simp) fun i ↦ by simp

section contractBridge

variable {v : G.Vertex} (hv : G.valence v = 2)
  (hloop : ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v) (hm : ∀ i, G.marking i ≠ v)
  (hv' : H.valence (f.vertexEquiv v) = 2)
  (hloop' : ∀ e, H.endpoint e 0 = f.vertexEquiv v → H.endpoint e 1 ≠ f.vertexEquiv v)
  (hm' : ∀ i, H.marking i ≠ f.vertexEquiv v)

/-- The isomorphism of bridge contractions acts on vertices as the original isomorphism. -/
@[simp]
theorem coe_contractBridge_vertexEquiv_apply (w : (G.contractBridge hv hloop hm).Vertex) :
    ((f.contractBridge hv hloop hm hv' hloop' hm').vertexEquiv w : H.Vertex) = f.vertexEquiv w := by
  rfl

/-- The isomorphism of bridge contractions carries the new node to the new node. -/
@[simp]
theorem contractBridge_edgeEquiv_none :
    (f.contractBridge hv hloop hm hv' hloop' hm').edgeEquiv none = none := by
  rfl

/-- The isomorphism of bridge contractions acts on the old edges as the original isomorphism. -/
@[simp]
theorem contractBridge_edgeEquiv_some (e : {e // ∀ i, G.endpoint e i ≠ v}) :
    (f.contractBridge hv hloop hm hv' hloop' hm').edgeEquiv (some e) =
      some ⟨f.edgeEquiv e, f.forall_endpoint_edgeEquiv_ne_iff.mpr e.2⟩ := by
  rfl

end contractBridge

end Iso

variable [Fintype ι] {G G' H : DualGraph.{u} ι}

/-- A stabilization step can be transported along an isomorphism: if `G` contracts to `G'` and
`G ≅ H`, then `H` contracts to a graph isomorphic to `G'`. -/
theorem StabilizationStep.exists_iso (h : StabilizationStep G G') (f : G.Iso H) :
    ∃ H', StabilizationStep H H' ∧ Nonempty (G'.Iso H') := by
  cases h with
  | contractTail hv hm =>
    have hv' : H.IsRationalTail (f.vertexEquiv _) := f.isRationalTail_vertexEquiv_iff.mpr hv
    exact ⟨_, .contractTail H hv' (by rwa [f.numMarkings_vertexEquiv]),
      ⟨f.contractTail _ (H.isRationalTail_iff.mp hv').2⟩⟩
  | contractBridge hv hm =>
    have hv' : H.IsRationalBridge (f.vertexEquiv _) := f.isRationalBridge_vertexEquiv_iff.mpr hv
    have hm' : ∀ i, H.marking i ≠ f.vertexEquiv _ := fun i ↦ by
      rw [← f.vertexEquiv_marking, f.vertexEquiv.injective.ne_iff]
      exact hm i
    exact ⟨_, .contractBridge H hv' hm',
      ⟨f.contractBridge _ _ _ (H.isRationalBridge_iff.mp hv').2.1
        (H.isRationalBridge_iff.mp hv').2.2 hm'⟩⟩

/-- Iterated stabilization steps can be transported along an isomorphism. -/
theorem exists_reflTransGen_iso (h : Relation.ReflTransGen StabilizationStep G G')
    (f : G.Iso H) :
    ∃ H', Relation.ReflTransGen StabilizationStep H H' ∧ Nonempty (G'.Iso H') := by
  induction h with
  | refl => exact ⟨H, .refl, ⟨f⟩⟩
  | tail _ hstep ih =>
    obtain ⟨H₁, h₁, ⟨f₁⟩⟩ := ih
    obtain ⟨H₂, h₂, f₂⟩ := hstep.exists_iso f₁
    exact ⟨H₂, h₁.tail h₂, f₂⟩

end DualGraph

end TauCeti
