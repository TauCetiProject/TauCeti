/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.BlockCut.Basic

/-!
# Degrees of cut vertices in the block--cut forest

For a cut vertex `v` of a finite simple graph, the blocks containing `v` are in bijection with
the connected components of the original component of `v` after `v` is deleted.  Since those
blocks are precisely the neighbours of `v` in the block--cut graph, this identifies the degree
of `v` in the block--cut forest with the number of branches created inside its component.

The resulting count is

`components(G - v) + 1 = components(G) + degree(blockCutGraph G, v)`.

This is the degree formula for the block--cut forest in R. Diestel, *Graph Theory*, 5th ed.,
Graduate Texts in Mathematics 173, Springer, 2017, Section 3.1.
-/

public section

open Set

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {v : V}

namespace CutVertex

variable (c : G.CutVertex)

/-- The connected components left inside the original component of a cut vertex after deleting
that vertex. -/
abbrev DeletedComponent :=
  {C : (G.induce ({(c : V)}ᶜ : Set V)).ConnectedComponent //
    C.map (Embedding.induce ({(c : V)}ᶜ : Set V)).toHom = G.connectedComponentMk c}

/-- A chosen neighbour of `c` in an incident block. -/
private noncomputable def neighborInBlock
    (B : {B : G.BlockVertex // (c : V) ∈ (B : Set V)}) : V :=
  (B.1.2.exists_adj_of_isCutVertex_mem c.2 B.2).choose

private theorem neighborInBlock_mem
    (B : {B : G.BlockVertex // (c : V) ∈ (B : Set V)}) :
    c.neighborInBlock B ∈ (B.1 : Set V) :=
  (B.1.2.exists_adj_of_isCutVertex_mem c.2 B.2).choose_spec.1

private theorem adj_neighborInBlock
    (B : {B : G.BlockVertex // (c : V) ∈ (B : Set V)}) :
    G.Adj c (c.neighborInBlock B) :=
  (B.1.2.exists_adj_of_isCutVertex_mem c.2 B.2).choose_spec.2

private theorem neighborInBlock_ne
    (B : {B : G.BlockVertex // (c : V) ∈ (B : Set V)}) :
    c.neighborInBlock B ≠ c :=
  (c.adj_neighborInBlock B).ne'

/-- The component after deleting `c` that contains the part of an incident block away from `c`.

The definition chooses a neighbour of `c` in the block; injectivity below shows that the
resulting component remembers exactly the block. -/
private noncomputable def incidentBlockComponent
    (B : {B : G.BlockVertex // (c : V) ∈ (B : Set V)}) : c.DeletedComponent := by
  let x : ↑({(c : V)}ᶜ : Set V) :=
    ⟨c.neighborInBlock B, Set.mem_compl_singleton_iff.mpr (c.neighborInBlock_ne B)⟩
  refine ⟨(G.induce ({(c : V)}ᶜ : Set V)).connectedComponentMk x, ?_⟩
  rw [ConnectedComponent.map_mk, ConnectedComponent.eq]
  exact (c.adj_neighborInBlock B).symm.reachable

private theorem incidentBlockComponent_injective :
    Function.Injective c.incidentBlockComponent := by
  intro B D hBD
  apply Subtype.ext
  by_contra hne
  let x : ↑({(c : V)}ᶜ : Set V) :=
    ⟨c.neighborInBlock B, Set.mem_compl_singleton_iff.mpr (c.neighborInBlock_ne B)⟩
  let y : ↑({(c : V)}ᶜ : Set V) :=
    ⟨c.neighborInBlock D, Set.mem_compl_singleton_iff.mpr (c.neighborInBlock_ne D)⟩
  have hxy : (G.induce ({(c : V)}ᶜ : Set V)).Reachable x y := by
    rw [← ConnectedComponent.eq]
    exact congrArg Subtype.val hBD
  obtain ⟨p⟩ := hxy
  let q : G.Walk (c.neighborInBlock B) (c.neighborInBlock D) :=
    p.map (Embedding.induce ({(c : V)}ᶜ : Set V)).toHom
  have hcq : (c : V) ∉ q.support := by
    intro hc
    -- Unfold the local walk abbreviation so the support transport lemma applies.
    change (c : V) ∈ (p.map (Embedding.induce ({(c : V)}ᶜ : Set V)).toHom).support at hc
    rw [Walk.support_map] at hc
    obtain ⟨z, -, hz⟩ := List.mem_map.mp hc
    exact z.property (by simpa using hz)
  have hne' : (B.1 : Set V) ≠ (D.1 : Set V) := fun h ↦ hne (Subtype.ext h)
  exact hcq (B.1.2.mem_support_of_ne D.1.2 hne' B.2 D.2
    (c.neighborInBlock_mem B) (c.neighborInBlock_mem D) q)

variable [Finite V]

private theorem incidentBlockComponent_surjective :
    Function.Surjective c.incidentBlockComponent := by
  intro C
  obtain ⟨x, hxC⟩ := C.1.exists_rep
  have hxc : (x : V) ≠ c := Set.mem_compl_singleton_iff.mp x.property
  have hreach : G.Reachable x c := by
    apply ConnectedComponent.exact
    exact (ConnectedComponent.map_mk (Embedding.induce ({(c : V)}ᶜ : Set V)).toHom x).symm.trans
      ((congrArg (ConnectedComponent.map
        (Embedding.induce ({(c : V)}ᶜ : Set V)).toHom) hxC).trans C.2)
  obtain ⟨p⟩ := hreach
  let S : Set V := (fun z : ↑({(c : V)}ᶜ : Set V) ↦ (z : V)) '' (C.1 : Set _)
  have hxS : (x : V) ∈ S := ⟨x, by simpa [hxC]⟩
  have hcS : (c : V) ∉ S := by
    rintro ⟨z, -, hz⟩
    exact z.property (by simpa using hz)
  -- The first edge leaving this deletion component must enter the deleted vertex itself.
  obtain ⟨d, -, hdS, hdnotS⟩ := p.exists_boundary_dart S hxS hcS
  obtain ⟨z, hzC, hzd⟩ := hdS
  have hdsnd : d.snd = c := by
    by_contra hne
    have hdfst : d.fst ≠ c := by
      intro h
      exact (Set.mem_compl_singleton_iff.mp z.property) (hzd.trans h)
    let y : ↑({(c : V)}ᶜ : Set V) :=
      ⟨d.snd, Set.mem_compl_singleton_iff.mpr hne⟩
    have hadj : (G.induce ({(c : V)}ᶜ : Set V)).Adj z y := by
      apply induce_adj.mpr
      simpa only [hzd] using d.adj
    apply hdnotS
    refine ⟨y, ?_, rfl⟩
    apply (ConnectedComponent.mem_supp_iff C.1 y).2
    calc
      (G.induce ({(c : V)}ᶜ : Set V)).connectedComponentMk y =
          (G.induce ({(c : V)}ᶜ : Set V)).connectedComponentMk z :=
        ConnectedComponent.sound hadj.symm.reachable
      _ = C.1 := (ConnectedComponent.mem_supp_iff C.1 z).1 hzC
  have hadj : G.Adj c d.fst := by simpa [hdsnd] using d.adj.symm
  obtain ⟨B, ⟨hB, hpair⟩, -⟩ := hadj.existsUnique_isBlock_superset_pair
  let Bc : {B : G.BlockVertex // (c : V) ∈ (B : Set V)} :=
    ⟨⟨B, hB⟩, hpair (Set.mem_insert (c : V) {d.fst})⟩
  refine ⟨Bc, Subtype.ext ?_⟩
  obtain ⟨q, hq⟩ := exists_walk_forall_mem_support_mem_and_ne hB.connected
    hB.not_isCutVertex (c.neighborInBlock_mem Bc)
    (hpair (Set.mem_insert_of_mem _ (Set.mem_singleton d.fst)))
    (c.neighborInBlock_ne Bc) (fun h ↦ d.adj.ne (h.trans hdsnd.symm))
  have hqReach : (G.induce ({(c : V)}ᶜ : Set V)).Reachable
      ⟨c.neighborInBlock Bc,
        Set.mem_compl_singleton_iff.mpr (c.neighborInBlock_ne Bc)⟩ z := by
    apply reachable_induce_iff.mpr
    refine ⟨q.copy rfl hzd.symm, ?_⟩
    intro w hw
    rw [Walk.support_copy] at hw
    exact Set.mem_compl_singleton_iff.mpr (hq w hw).2
  simpa only [incidentBlockComponent] using (ConnectedComponent.sound hqReach).trans
      ((ConnectedComponent.mem_supp_iff C.1 z).1 hzC)

/-- The blocks containing a cut vertex are in bijection with the components of its original
connected component after deleting that vertex. -/
noncomputable def incidentBlockEquivDeletedComponent :
    {B : G.BlockVertex // (c : V) ∈ (B : Set V)} ≃ c.DeletedComponent :=
  Equiv.ofBijective c.incidentBlockComponent
    ⟨c.incidentBlockComponent_injective, c.incidentBlockComponent_surjective⟩

private theorem incidentBlockEquivDeletedComponent_apply
    (B : {B : G.BlockVertex // (c : V) ∈ (B : Set V)}) :
    c.incidentBlockEquivDeletedComponent B = c.incidentBlockComponent B :=
  rfl

/-- The deletion component corresponding to an incident block contains every vertex of that
block other than the deleted cut vertex. -/
theorem mem_incidentBlockEquivDeletedComponent
    (B : {B : G.BlockVertex // (c : V) ∈ (B : Set V)}) {x : V}
    (hxB : x ∈ (B.1 : Set V)) (hxc : x ≠ c) :
    (⟨x, Set.mem_compl_singleton_iff.mpr hxc⟩ : ↑({(c : V)}ᶜ : Set V)) ∈
      ((c.incidentBlockEquivDeletedComponent B).1 : Set _) := by
  let x' : ↑({(c : V)}ᶜ : Set V) :=
    ⟨x, Set.mem_compl_singleton_iff.mpr hxc⟩
  obtain ⟨p, hp⟩ := exists_walk_forall_mem_support_mem_and_ne B.1.2.connected
    B.1.2.not_isCutVertex hxB (c.neighborInBlock_mem B) hxc (c.neighborInBlock_ne B)
  have hreach : (G.induce ({(c : V)}ᶜ : Set V)).Reachable
      x'
      ⟨c.neighborInBlock B,
        Set.mem_compl_singleton_iff.mpr (c.neighborInBlock_ne B)⟩ := by
    apply reachable_induce_iff.mpr
    exact ⟨p, fun z hz ↦ Set.mem_compl_singleton_iff.mpr (hp z hz).2⟩
  have hcomponent : (G.induce ({(c : V)}ᶜ : Set V)).connectedComponentMk x' =
      (c.incidentBlockEquivDeletedComponent B).1 := by
    rw [incidentBlockEquivDeletedComponent_apply]
    simpa only [incidentBlockComponent] using ConnectedComponent.sound hreach
  exact (ConnectedComponent.mem_supp_iff _ _).mpr hcomponent

/-- The neighbours of a cut vertex in the block--cut graph are counted by the components into
which deleting it splits its original connected component. -/
theorem ncard_neighborSet_blockCutGraph_eq_natCard_deletedComponent :
    (G.blockCutGraph.neighborSet (.inr c)).ncard = Nat.card c.DeletedComponent := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr ((G.neighborSetCutVertexEquiv c).trans
    c.incidentBlockEquivDeletedComponent)

/-- The degree of a cut vertex in the block--cut graph is the number of components into which
deleting it splits its original connected component. -/
theorem degree_blockCutGraph_eq_natCard_deletedComponent
    [Fintype ↑(G.blockCutGraph.neighborSet (.inr c))] :
    G.blockCutGraph.degree (.inr c) = Nat.card c.DeletedComponent := by
  rw [← ncard_neighborSet, c.ncard_neighborSet_blockCutGraph_eq_natCard_deletedComponent]

/-- **The block--cut degree formula.** Deleting a cut vertex adds its block--cut degree minus
one to the number of connected components. -/
theorem natCard_connectedComponent_induce_compl_singleton_add_one :
    Nat.card (G.induce ({(c : V)}ᶜ : Set V)).ConnectedComponent + 1 =
      Nat.card G.ConnectedComponent +
        (G.blockCutGraph.neighborSet (.inr c)).ncard := by
  classical
  let _ : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let f : (G.induce ({(c : V)}ᶜ : Set V)).ConnectedComponent → G.ConnectedComponent :=
    ConnectedComponent.map (Embedding.induce ({(c : V)}ᶜ : Set V)).toHom
  let C₀ : G.ConnectedComponent := G.connectedComponentMk c
  have htotal : Nat.card (G.induce ({(c : V)}ᶜ : Set V)).ConnectedComponent =
      ∑ C : G.ConnectedComponent, Nat.card {D // f D = C} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
  have hdegree : Nat.card {D // f D = C₀} =
      (G.blockCutGraph.neighborSet (.inr c)).ncard := by
    exact c.ncard_neighborSet_blockCutGraph_eq_natCard_deletedComponent.symm
  have hfiber (C : G.ConnectedComponent) (hC : C ≠ C₀) :
      Nat.card {D // f D = C} = 1 := by
    exact ConnectedComponent.natCard_fiber_map_induce_compl_singleton_eq_one hC
  have hsum : ∑ C ∈ Finset.univ.erase C₀, Nat.card {D // f D = C} =
      Nat.card G.ConnectedComponent - 1 := by
    calc
      ∑ C ∈ Finset.univ.erase C₀, Nat.card {D // f D = C} =
          ∑ _C ∈ Finset.univ.erase C₀, 1 := by
        apply Finset.sum_congr rfl
        intro C hC
        exact hfiber C (by simpa using hC)
      _ = (Finset.univ.erase C₀).card := by simp
      _ = Fintype.card G.ConnectedComponent - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ C₀)]
        simp
      _ = Nat.card G.ConnectedComponent - 1 := by rw [Nat.card_eq_fintype_card]
  have hsplit : ∑ C : G.ConnectedComponent, Nat.card {D // f D = C} =
      Nat.card {D // f D = C₀} +
        ∑ C ∈ Finset.univ.erase C₀, Nat.card {D // f D = C} := by
    exact (Finset.add_sum_erase (a := C₀) (Finset.univ : Finset G.ConnectedComponent)
      (fun C ↦ Nat.card {D // f D = C}) (Finset.mem_univ C₀)).symm
  have hpos : 0 < Nat.card G.ConnectedComponent := by
    exact Nat.card_pos_iff.mpr ⟨⟨G.connectedComponentMk c⟩, inferInstance⟩
  rw [htotal, hsplit, hdegree, hsum]
  omega

/-- The block--cut component-count formula, stated with `SimpleGraph.degree`. -/
theorem natCard_connectedComponent_induce_compl_singleton_add_one_eq_add_degree
    [Fintype ↑(G.blockCutGraph.neighborSet (.inr c))] :
    Nat.card (G.induce ({(c : V)}ᶜ : Set V)).ConnectedComponent + 1 =
      Nat.card G.ConnectedComponent + G.blockCutGraph.degree (.inr c) := by
  rw [← ncard_neighborSet]
  exact c.natCard_connectedComponent_induce_compl_singleton_add_one

end CutVertex

end SimpleGraph

namespace Graph

variable {α : Type u} {β : Type*} {G : Graph α β} {v : V(G)}

/-- **The multigraph block--cut degree formula.** For a cut vertex of a multigraph with finitely
many actual vertices, deleting that vertex adds its degree in the block--cut forest of the
underlying simple graph minus one to the number of components. -/
theorem IsCutVertex.componentCount_deleteVerts_add_one_eq_add_blockCutDegree
    [Finite V(G)] (hv : G.IsCutVertex v) :
    (G.deleteVerts {(v : α)}).componentCount + 1 = G.componentCount +
      (G.toSimpleGraph.blockCutGraph.neighborSet (.inr
        (⟨v, (G.isCutVertex_iff_toSimpleGraph_isCutVertex v.property).mp hv⟩ :
          G.toSimpleGraph.CutVertex))).ncard := by
  let c : G.toSimpleGraph.CutVertex :=
    ⟨v, (G.isCutVertex_iff_toSimpleGraph_isCutVertex v.property).mp hv⟩
  have hs : {x : V(G) | (x : α) ∉ ({(v : α)} : Set α)} = ({v}ᶜ : Set V(G)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_compl_iff, Subtype.ext_iff]
  let e : (G.deleteVerts {(v : α)}).toSimpleGraph ≃g
      G.toSimpleGraph.induce ({v}ᶜ : Set V(G)) := by
    rw [← hs]
    exact G.toSimpleGraphDeleteVertsIso {(v : α)}
  have heq : Nat.card (G.deleteVerts {(v : α)}).toSimpleGraph.ConnectedComponent =
      Nat.card (G.toSimpleGraph.induce ({v}ᶜ : Set V(G))).ConnectedComponent :=
    Nat.card_congr e.connectedComponentEquiv
  rw [componentCount_eq_natCard_toSimpleGraph, componentCount_eq_natCard_toSimpleGraph, heq]
  exact c.natCard_connectedComponent_induce_compl_singleton_add_one

end Graph
