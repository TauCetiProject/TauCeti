/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Iso
public import TauCeti.Combinatorics.Graph.Serre.OfGraph.ToGraph

/-!
# A Serre graph is determined by its underlying multigraph

A Serre graph `Γ` has an underlying multigraph `Γ.toGraph`, whose edges are the reversal orbits
`{e, rev e}` of darts. Conversely a multigraph `G` gives the Serre graph `G.toSerreGraph`, which
attaches two darts to every edge after choosing an ordering of its two ends. Up to isomorphism a
Serre graph carries no information beyond its underlying multigraph.

An isomorphism of Serre graphs induces an isomorphism of the underlying multigraphs, and every
isomorphism of the underlying multigraphs lifts to an isomorphism of Serre graphs. The lift is
forced on every dart except a loop, where both darts of the orbit have the right ends; it is not
unique, since reversing the darts of a loop is a nontrivial automorphism of a Serre graph which
induces the identity of its multigraph. Hence two Serre graphs are isomorphic exactly when their
underlying multigraphs are, and a Serre graph is isomorphic to `G.toSerreGraph` exactly when its
underlying multigraph is isomorphic to `G`.

For an orientation `O` of a Serre graph, the multigraph `Γ.endpointGraph O` of the darts of `O`
is isomorphic to `Γ.toGraph`. A Serre graph obtained from `G` by ordering the ends of each edge in
any way and adding the reverse darts has the orientation formed by the darts following the chosen
orderings, and the multigraph of that orientation is `G`. So different orderings of the ends give
isomorphic Serre graphs. Finally, passing from a Serre graph to its multigraph and back recovers
the Serre graph; the other round trip, `G.toSerreGraph.toGraph ≅ G`, is
`Graph.toSerreGraphToGraphIso`.

## Main declarations

* `TauCeti.SerreGraph.Iso.toGraphIso`: the isomorphism of underlying multigraphs induced by an
  isomorphism of Serre graphs.
* `TauCeti.SerreGraph.Iso.ofToGraphIso`: a lift of an isomorphism of underlying multigraphs to an
  isomorphism of Serre graphs, with `TauCeti.SerreGraph.Iso.toGraphIso_ofToGraphIso`.
* `TauCeti.SerreGraph.nonempty_iso_iff_nonempty_toGraph_iso`: two Serre graphs are isomorphic
  exactly when their underlying multigraphs are.
* `Graph.nonempty_iso_toSerreGraph_iff`: the Serre graphs isomorphic to `G.toSerreGraph` are those
  whose underlying multigraph is isomorphic to `G`.
* `TauCeti.SerreGraph.IsOrientation.endpointGraphIsoToGraph`: the multigraph of the darts of an
  orientation is the underlying multigraph.
* `TauCeti.SerreGraph.IsOrientation.nonempty_iso_toSerreGraph_iff`: different orderings of the
  ends of the edges of a multigraph give isomorphic Serre graphs.
* `TauCeti.SerreGraph.toGraphToSerreGraphIso`: the Serre graph of the underlying multigraph of a
  Serre graph is isomorphic to it.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1.
* I. Kapovich, R. Weidmann, A. Miasnikov, *Foldings, graphs of groups and the membership
  problem*, Convention 2.1 and Convention 3.2.
* I. Kapovich, A. Myasnikov, *Stallings foldings and subgroups of free groups*, Convention 2.2.
-/

public section

universe u v w x y z

namespace TauCeti

namespace SerreGraph

variable {Γ : SerreGraph.{u, v}} {Δ : SerreGraph.{w, x}} {Θ : SerreGraph.{y, z}}

/-- The reversal orbit of the image of a dart representing a reversal orbit. For a map of darts
commuting with reversal it does not depend on the representative (`edgeMap_edge`). -/
private noncomputable def edgeMap (f : Γ.E → Δ.E) (q : Γ.Edge) : Δ.Edge :=
  Δ.edge (f (Γ.edge_surjective q).choose)

private theorem edgeMap_edge (f : Γ.E → Δ.E) (hf : ∀ e, f (Γ.rev e) = Δ.rev (f e)) (e : Γ.E) :
    edgeMap f (Γ.edge e) = Δ.edge (f e) := by
  rcases (Γ.edge_eq_iff _ _).1 (Γ.edge_surjective (Γ.edge e)).choose_spec with h | h <;>
    simp only [edgeMap, h, hf, edge_rev]

namespace Iso

/-- The bijection of reversal orbits induced by an isomorphism of Serre graphs. -/
private noncomputable def orbitEquiv (φ : Γ.Iso Δ) : Γ.Edge ≃ Δ.Edge where
  toFun := edgeMap φ.equivE
  invFun := edgeMap φ.symm.equivE
  left_inv q := by
    induction q using Edge.ind with
    | h e => rw [edgeMap_edge _ φ.map_rev, edgeMap_edge _ φ.symm.map_rev, symm_equivE,
        Equiv.symm_apply_apply]
  right_inv q := by
    induction q using Edge.ind with
    | h e => rw [edgeMap_edge _ φ.symm.map_rev, edgeMap_edge _ φ.map_rev, symm_equivE,
        Equiv.apply_symm_apply]

private theorem orbitEquiv_edge (φ : Γ.Iso Δ) (e : Γ.E) :
    φ.orbitEquiv (Γ.edge e) = Δ.edge (φ.equivE e) :=
  edgeMap_edge _ φ.map_rev e

/-- The isomorphism of underlying multigraphs induced by an isomorphism of Serre graphs: a vertex
goes to its image, and the reversal orbit of a dart to the reversal orbit of its image. -/
noncomputable def toGraphIso (φ : Γ.Iso Δ) : Γ.toGraph.Iso Δ.toGraph where
  vertexEquiv := φ.equivV.subtypeEquiv fun _ ↦ by simp
  edgeEquiv := φ.orbitEquiv.subtypeEquiv fun _ ↦ by simp
  map_isLink_iff q a b := by
    obtain ⟨q, hq⟩ := q
    induction q using Edge.ind with
    | h e =>
      simp only [Equiv.subtypeEquiv_apply, orbitEquiv_edge, toGraph_isLink, edgeEnds_edge,
        map_src, map_tgt, ← Sym2.map_mk]
      exact (Sym2.map.injective φ.equivV.injective).eq_iff

/-- The induced isomorphism of multigraphs is the vertex bijection on vertices. -/
@[simp] theorem coe_toGraphIso_vertexEquiv_apply (φ : Γ.Iso Δ) (x : Γ.toGraph.vertexSet) :
    (φ.toGraphIso.vertexEquiv x : Δ.V) = φ.equivV x := (rfl)

/-- The induced isomorphism of multigraphs sends the reversal orbit of a dart to the reversal
orbit of its image. -/
@[simp] theorem toGraphIso_edgeEquiv_mk (φ : Γ.Iso Δ) (e : Γ.E)
    (he : Γ.edge e ∈ Γ.toGraph.edgeSet) :
    φ.toGraphIso.edgeEquiv ⟨Γ.edge e, he⟩ = ⟨Δ.edge (φ.equivE e), by simp⟩ :=
  Subtype.ext (φ.orbitEquiv_edge e)

private theorem graphIso_ext {φ ψ : Γ.toGraph.Iso Δ.toGraph}
    (hV : ∀ x, (φ.vertexEquiv x : Δ.V) = ψ.vertexEquiv x)
    (hE : ∀ e he, (φ.edgeEquiv ⟨Γ.edge e, he⟩ : Δ.Edge) = ψ.edgeEquiv ⟨Γ.edge e, he⟩) : φ = ψ := by
  refine Graph.Iso.ext (Equiv.ext fun x ↦ Subtype.ext (hV x)) (Equiv.ext fun q ↦ ?_)
  obtain ⟨q, hq⟩ := q
  induction q using Edge.ind with
  | h e => exact Subtype.ext (hE e hq)

/-- The identity of a Serre graph induces the identity of its multigraph. -/
@[simp] theorem toGraphIso_refl (Γ : SerreGraph.{u, v}) :
    (refl Γ).toGraphIso = Graph.Iso.refl Γ.toGraph :=
  graphIso_ext (fun _ ↦ by simp) fun _ _ ↦ by simp

/-- Inducing isomorphisms of multigraphs is compatible with composition. -/
@[simp] theorem toGraphIso_trans (φ : Γ.Iso Δ) (ψ : Δ.Iso Θ) :
    (φ.trans ψ).toGraphIso = φ.toGraphIso.trans ψ.toGraphIso :=
  graphIso_ext (fun _ ↦ by simp) fun _ _ ↦ by simp

/-- Inducing isomorphisms of multigraphs is compatible with inverses. -/
@[simp] theorem toGraphIso_symm (φ : Γ.Iso Δ) : φ.symm.toGraphIso = φ.toGraphIso.symm := by
  have h : φ.toGraphIso.trans φ.symm.toGraphIso = Graph.Iso.refl Γ.toGraph := by
    rw [← toGraphIso_trans, self_trans_symm, toGraphIso_refl]
  rw [← Graph.Iso.refl_trans φ.symm.toGraphIso, ← Graph.Iso.symm_trans_self φ.toGraphIso,
    Graph.Iso.trans_assoc, h, Graph.Iso.trans_refl]

section Lift

variable (φ : Γ.toGraph.Iso Δ.toGraph)

/-- The bijection of all vertices underlying an isomorphism of underlying multigraphs. -/
private def liftV : Γ.V ≃ Δ.V :=
  (Equiv.subtypeUnivEquiv fun _ ↦ by simp).symm.trans
    (φ.vertexEquiv.trans (Equiv.subtypeUnivEquiv fun _ ↦ by simp))

/-- The bijection of all reversal orbits underlying an isomorphism of underlying multigraphs. -/
private def liftOrbit : Γ.Edge ≃ Δ.Edge :=
  (Equiv.subtypeUnivEquiv fun _ ↦ by simp).symm.trans
    (φ.edgeEquiv.trans (Equiv.subtypeUnivEquiv fun _ ↦ by simp))

private theorem exists_liftDart (e : Γ.E) :
    ∃ f : Quiver.Hom (liftV φ (Γ.src e)) (liftV φ (Γ.tgt e)), Δ.edge f.1 = liftOrbit φ (Γ.edge e) :=
  Δ.exists_hom_of_toGraph_isLink <|
    (φ.map_isLink_iff ⟨Γ.edge e, by simp⟩ ⟨Γ.src e, by simp⟩ ⟨Γ.tgt e, by simp⟩).2
      (by simp)

/-- A dart above the image of the orbit of a dart, joining the images of its ends. -/
private noncomputable def liftDart (e : Γ.E) : Δ.E := (exists_liftDart φ e).choose.1

private theorem src_liftDart (e : Γ.E) : Δ.src (liftDart φ e) = liftV φ (Γ.src e) :=
  (exists_liftDart φ e).choose.2.1

private theorem tgt_liftDart (e : Γ.E) : Δ.tgt (liftDart φ e) = liftV φ (Γ.tgt e) :=
  (exists_liftDart φ e).choose.2.2

private theorem edge_liftDart (e : Γ.E) : Δ.edge (liftDart φ e) = liftOrbit φ (Γ.edge e) :=
  (exists_liftDart φ e).choose_spec

open Classical in
/-- The dart map of the lift: `liftDart` on a chosen orientation, extended to the reverse darts
by reversal. -/
private noncomputable def liftE (e : Γ.E) : Δ.E :=
  if e ∈ Γ.exists_isOrientation.choose then liftDart φ e else Δ.rev (liftDart φ (Γ.rev e))

private theorem liftE_rev (e : Γ.E) : liftE φ (Γ.rev e) = Δ.rev (liftE φ e) := by
  by_cases he : e ∈ Γ.exists_isOrientation.choose <;>
    simp [liftE, he, Γ.exists_isOrientation.choose_spec.mem_rev_iff Γ e]

private theorem src_liftE (e : Γ.E) : Δ.src (liftE φ e) = liftV φ (Γ.src e) := by
  by_cases he : e ∈ Γ.exists_isOrientation.choose <;> simp [liftE, he, src_liftDart, tgt_liftDart]

private theorem edge_liftE (e : Γ.E) : Δ.edge (liftE φ e) = liftOrbit φ (Γ.edge e) := by
  by_cases he : e ∈ Γ.exists_isOrientation.choose <;> simp [liftE, he, edge_liftDart]

/-- The morphism of Serre graphs lifting an isomorphism of underlying multigraphs. -/
private noncomputable def liftHom : Γ.Hom Δ where
  mapV := liftV φ
  mapE := liftE φ
  map_src := src_liftE φ
  map_rev := liftE_rev φ

private theorem liftE_injective : Function.Injective (liftE φ) := by
  intro e e' h
  have hq : liftOrbit φ (Γ.edge e) = liftOrbit φ (Γ.edge e') := by
    rw [← edge_liftE, ← edge_liftE, h]
  rcases (Γ.edge_eq_iff _ _).1 ((liftOrbit φ).injective hq) with rfl | rfl
  · rfl
  · rw [liftE_rev] at h
    exact absurd h (Δ.rev_ne _)

private theorem liftE_surjective : Function.Surjective (liftE φ) := by
  intro f
  obtain ⟨e, he⟩ := Γ.edge_surjective ((liftOrbit φ).symm (Δ.edge f))
  have hf : Δ.edge (liftE φ e) = Δ.edge f := by
    rw [edge_liftE, he, Equiv.apply_symm_apply]
  rcases (Δ.edge_eq_iff _ _).1 hf with h | h
  · exact ⟨e, h⟩
  · exact ⟨Γ.rev e, by rw [liftE_rev, h, rev_rev]⟩

end Lift

/-- An isomorphism of the underlying multigraphs of two Serre graphs lifts to an isomorphism of
the Serre graphs. Each dart goes to a dart over the image of its reversal orbit, with the image
ends; for a loop the direction is chosen, compatibly with reversal. -/
noncomputable def ofToGraphIso (φ : Γ.toGraph.Iso Δ.toGraph) : Γ.Iso Δ :=
  (liftHom φ).toIso (liftV φ).bijective ⟨liftE_injective φ, liftE_surjective φ⟩

/-- The lift of a multigraph isomorphism is that isomorphism on vertices. -/
@[simp] theorem ofToGraphIso_equivV_apply (φ : Γ.toGraph.Iso Δ.toGraph) (v : Γ.V)
    (hv : v ∈ Γ.toGraph.vertexSet) : (ofToGraphIso φ).equivV v = φ.vertexEquiv ⟨v, hv⟩ :=
  Hom.toIso_equivV_apply _ _ _ _

/-- The lift of a multigraph isomorphism sends each dart into the image of its reversal orbit. -/
@[simp] theorem edge_ofToGraphIso_equivE (φ : Γ.toGraph.Iso Δ.toGraph) (e : Γ.E)
    (he : Γ.edge e ∈ Γ.toGraph.edgeSet) :
    Δ.edge ((ofToGraphIso φ).equivE e) = φ.edgeEquiv ⟨Γ.edge e, he⟩ :=
  (congrArg Δ.edge (Hom.toIso_equivE_apply _ _ _ _)).trans (edge_liftE φ e)

/-- The lift of a multigraph isomorphism induces that multigraph isomorphism. -/
@[simp] theorem toGraphIso_ofToGraphIso (φ : Γ.toGraph.Iso Δ.toGraph) :
    (ofToGraphIso φ).toGraphIso = φ :=
  graphIso_ext (fun _ ↦ by simp) fun _ _ ↦ by simp

end Iso

private theorem IsOrientation.bijective_edge {O : Set Γ.E} (hO : Γ.IsOrientation O) :
    Function.Bijective fun e : (Γ.endpointGraph O).edgeSet ↦
      (⟨Γ.edge e, by simp⟩ : Γ.toGraph.edgeSet) := by
  refine ⟨fun e e' h ↦ Subtype.ext ?_, fun q ↦ ?_⟩
  · rcases (Γ.edge_eq_iff _ _).1 (congrArg Subtype.val h) with h | h
    · exact h
    · refine absurd ?_ (hO.rev_notMem_of_mem Γ _ (by simpa using e'.2))
      rw [← h]
      simpa using e.2
  · obtain ⟨q, hq⟩ := q
    obtain ⟨d, rfl⟩ := Γ.edge_surjective q
    rcases hO.mem_or_rev_mem d with hd | hd
    · exact ⟨⟨d, by simpa using hd⟩, rfl⟩
    · exact ⟨⟨Γ.rev d, by simpa using hd⟩, Subtype.ext (Γ.edge_rev d)⟩

/-- For an orientation `O` of a Serre graph, the multigraph of the darts of `O`, each joining its
source to its target, is the underlying multigraph of the Serre graph: the isomorphism is the
identity on vertices and sends a dart of `O` to its reversal orbit. -/
noncomputable def IsOrientation.endpointGraphIsoToGraph {O : Set Γ.E} (hO : Γ.IsOrientation O) :
    (Γ.endpointGraph O).Iso Γ.toGraph where
  vertexEquiv := Equiv.subtypeEquivRight fun _ ↦ by simp
  edgeEquiv := .ofBijective _ hO.bijective_edge
  map_isLink_iff e a b := by
    simp [show (e : Γ.E) ∈ O by simpa using e.2]

/-- The isomorphism of the multigraph of an orientation with the underlying multigraph is the
identity on vertices. -/
@[simp] theorem IsOrientation.coe_endpointGraphIsoToGraph_vertexEquiv_apply {O : Set Γ.E}
    (hO : Γ.IsOrientation O) (x : (Γ.endpointGraph O).vertexSet) :
    (hO.endpointGraphIsoToGraph.vertexEquiv x : Γ.V) = x := (rfl)

/-- The isomorphism of the multigraph of an orientation with the underlying multigraph sends a dart
of the orientation to its reversal orbit. -/
@[simp] theorem IsOrientation.coe_endpointGraphIsoToGraph_edgeEquiv_apply {O : Set Γ.E}
    (hO : Γ.IsOrientation O) (e : (Γ.endpointGraph O).edgeSet) :
    (hO.endpointGraphIsoToGraph.edgeEquiv e : Γ.Edge) = Γ.edge e := (rfl)

/-- Two Serre graphs are isomorphic exactly when their underlying multigraphs are. -/
theorem nonempty_iso_iff_nonempty_toGraph_iso :
    Nonempty (Γ.Iso Δ) ↔ Nonempty (Γ.toGraph.Iso Δ.toGraph) :=
  ⟨Nonempty.map Iso.toGraphIso, Nonempty.map Iso.ofToGraphIso⟩

/-- A Serre graph is recovered from its underlying multigraph: the Serre graph of `Γ.toGraph` is
isomorphic to `Γ`, by the identity on vertices and a bijection sending each dart of
`Γ.toGraph.toSerreGraph` into the reversal orbit it lies over. -/
noncomputable def toGraphToSerreGraphIso (Γ : SerreGraph.{u, v}) : Γ.toGraph.toSerreGraph.Iso Γ :=
  Iso.ofToGraphIso Γ.toGraph.toSerreGraphToGraphIso

/-- The isomorphism `Γ.toGraph.toSerreGraph ≅ Γ` is the identity on vertices. -/
@[simp] theorem toGraphToSerreGraphIso_equivV_apply (Γ : SerreGraph.{u, v})
    (a : Γ.toGraph.toSerreGraph.V) : Γ.toGraphToSerreGraphIso.equivV a = a.1 := by
  simp [toGraphToSerreGraphIso]

/-- The isomorphism `Γ.toGraph.toSerreGraph ≅ Γ` sends a dart over an edge of `Γ.toGraph` into
that reversal orbit. -/
@[simp] theorem edge_toGraphToSerreGraphIso_equivE (Γ : SerreGraph.{u, v})
    (d : Γ.toGraph.toSerreGraph.E) : Γ.edge (Γ.toGraphToSerreGraphIso.equivE d) = d.1.1 := by
  simp [toGraphToSerreGraphIso]

end SerreGraph

end TauCeti

namespace Graph

open TauCeti

variable {V : Type*} {E : Type*}

/-- The Serre graph of a multigraph `G` is, up to isomorphism, the only Serre graph whose
underlying multigraph is `G`. -/
theorem nonempty_iso_toSerreGraph_iff {G : Graph V E} {Γ : SerreGraph} :
    Nonempty (Γ.Iso G.toSerreGraph) ↔ Nonempty (Γ.toGraph.Iso G) := by
  rw [SerreGraph.nonempty_iso_iff_nonempty_toGraph_iso]
  exact ⟨Nonempty.map (·.trans G.toSerreGraphToGraphIso),
    Nonempty.map (·.trans G.toSerreGraphToGraphIso.symm)⟩

end Graph

namespace TauCeti.SerreGraph.IsOrientation

variable {V : Type*} {E : Type*}

/-- Different orderings of the ends of the edges of a multigraph `G` give isomorphic Serre
graphs. A Serre graph `Γ` with an orientation `O` such that the multigraph of the darts of `O`
is `G` arises from `G` by ordering the ends of each edge as the source and target of the dart of
`O` over it, and adding the reverse darts. Every such Serre graph is isomorphic to
`G.toSerreGraph`, and conversely. -/
theorem nonempty_iso_toSerreGraph_iff {Γ : SerreGraph} {O : Set Γ.E} (hO : Γ.IsOrientation O)
    {G : Graph V E} : Nonempty (Γ.Iso G.toSerreGraph) ↔ Nonempty ((Γ.endpointGraph O).Iso G) := by
  rw [Graph.nonempty_iso_toSerreGraph_iff]
  exact ⟨Nonempty.map hO.endpointGraphIsoToGraph.trans,
    Nonempty.map hO.endpointGraphIsoToGraph.symm.trans⟩

end TauCeti.SerreGraph.IsOrientation
