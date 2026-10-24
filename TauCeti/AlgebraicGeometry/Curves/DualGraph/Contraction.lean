/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Contracting unstable rational components of dual graphs

A pointed nodal curve is made stable by repeatedly contracting rational components with at most
two special points. There are three kinds of such components, and each contraction has a
combinatorial shadow on the dual graph:

* an unmarked **rational tail** (a rational component meeting the rest of the curve in one point)
  is deleted;
* a rational tail carrying one marking is deleted, and the marking moves to the point where the
  tail met the rest of the curve, on the neighbouring component;
* an unmarked **rational bridge** (a smooth rational component meeting the rest of the curve in
  two points) is replaced by a node joining the two neighbouring branches.

This file constructs both graph operations, `TauCeti.DualGraph.contractTail` and
`TauCeti.DualGraph.contractBridge`, and computes how they change the numerical invariants. They
keep the markings and remove one vertex. They lower the arithmetic genus by the genus of the
contracted vertex, so they preserve it when that vertex is rational, as in a stabilization step.
Contracting a bridge changes no log-canonical degree. Contracting a tail changes only the
log-canonical degree of the neighbouring component, which drops by one when the tail is unmarked.
So a component of positive log-canonical degree can become unstable once its tails are removed,
and stabilization has to be iterated, recomputing degrees after each step.

`TauCeti.DualGraph.StabilizationStep G H` says that `H` arises from `G` by one such contraction.
In the stable range `2g - 2 + n > 0`, a graph admits a stabilization step exactly when it is not
stable, and iterating steps from any graph reaches a stable graph of the same genus with the same
markings; the number of vertices decreases at every step.

## Main definitions

* `TauCeti.DualGraph.attachment`: the neighbour of a vertex of valence one.
* `TauCeti.DualGraph.contractTail`: the graph with a vertex of valence one deleted and its
  markings moved to its neighbour.
* `TauCeti.DualGraph.contractBridge`: the graph with an unmarked loopless vertex of valence two
  replaced by an edge joining its two neighbours.
* `TauCeti.DualGraph.StabilizationStep`: contraction of a rational tail with at most one marking
  or of an unmarked rational bridge.

## Main results

* `TauCeti.DualGraph.arithmeticGenus_contractTail` and
  `TauCeti.DualGraph.arithmeticGenus_contractBridge`: the arithmetic genus drops by the genus of
  the contracted vertex.
* `TauCeti.DualGraph.logCanonicalDegree_contractTail` and
  `TauCeti.DualGraph.logCanonicalDegree_contractBridge`: the change of log-canonical degrees.
* `TauCeti.DualGraph.isStable_iff_forall_not_stabilizationStep`: in the stable range, a graph is
  stable exactly when it admits no stabilization step.
* `TauCeti.DualGraph.exists_reflTransGen_stabilizationStep_isStable`: in the stable range,
  iterated stabilization steps reach a stable graph.

## References

* [Stacks, Tag 0E7N](https://stacks.math.columbia.edu/tag/0E7N), contracting rational tails and
  rational bridges.
* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks
  `M_{g,n}`*, Math. Scand. 52 (1983), 161–199, §2, for stabilization of pointed curves.
-/

public section

namespace TauCeti

namespace DualGraph

open Finset

universe u v

variable {ι : Type v} (G : DualGraph.{u} ι)

/-! ### Half-edges at a vertex -/

variable {G}

/-- A loopless vertex: the other branch of a node at `v` lies on another component. -/
lemma endpoint_rev_ne {v : G.Vertex} (hloop : ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v)
    {e : G.Edge} {i : Fin 2} (he : G.endpoint e i = v) : G.endpoint e i.rev ≠ v := by
  fin_cases i
  · exact hloop e he
  · exact fun h ↦ hloop e h he

/-- A vertex of positive valence carries a half-edge. -/
lemma exists_endpoint_eq_of_valence_pos {v : G.Vertex} (hv : 0 < G.valence v) :
    ∃ h : G.Edge × Fin 2, G.endpoint h.1 h.2 = v := by
  rw [valence_def] at hv
  obtain ⟨h, hh⟩ := card_pos.mp hv
  exact ⟨h, (mem_filter.mp hh).2⟩

/-- At a vertex of valence one, any two half-edges coincide. -/
lemma eq_of_valence_eq_one {v : G.Vertex} (hv : G.valence v = 1) (h h' : G.Edge × Fin 2)
    (hh : G.endpoint h.1 h.2 = v) (hh' : G.endpoint h'.1 h'.2 = v) : h = h' := by
  rw [valence_def] at hv
  exact card_le_one.mp hv.le h (by simpa using hh) h' (by simpa using hh')

/-- A vertex of valence one carries no loop. -/
lemma endpoint_one_ne_of_valence_eq_one {v : G.Vertex} (hv : G.valence v = 1) (e : G.Edge)
    (he : G.endpoint e 0 = v) : G.endpoint e 1 ≠ v := fun he' ↦
  absurd (congrArg Prod.snd (eq_of_valence_eq_one hv (e, 0) (e, 1) he he')) Fin.zero_ne_one

/-- The **attachment** of a vertex of valence one: the other endpoint of its unique edge. For a
rational tail, it is the component that the tail meets. -/
noncomputable def attachment {v : G.Vertex} (hv : G.valence v = 1) : G.Vertex :=
  G.endpoint (exists_endpoint_eq_of_valence_pos (G := G) (v := v) (by omega)).choose.1
    (exists_endpoint_eq_of_valence_pos (G := G) (v := v) (by omega)).choose.2.rev

/-- The other branch of the unique node at a vertex of valence one lies on its attachment. -/
lemma endpoint_rev_eq_attachment {v : G.Vertex} (hv : G.valence v = 1) {e : G.Edge} {i : Fin 2}
    (he : G.endpoint e i = v) : G.endpoint e i.rev = G.attachment hv := by
  have := eq_of_valence_eq_one hv (e, i) _ he
    (exists_endpoint_eq_of_valence_pos (G := G) (v := v) (by omega)).choose_spec
  rw [attachment, ← this]

/-- A vertex of valence one is not its own attachment. -/
lemma attachment_ne {v : G.Vertex} (hv : G.valence v = 1) : G.attachment hv ≠ v := by
  obtain ⟨⟨e, i⟩, he⟩ := exists_endpoint_eq_of_valence_pos (G := G) (by omega : 0 < G.valence v)
  rw [← endpoint_rev_eq_attachment hv he]
  exact endpoint_rev_ne (endpoint_one_ne_of_valence_eq_one hv) he

/-- A vertex of valence one is adjacent to its attachment. -/
lemma adj_attachment {v : G.Vertex} (hv : G.valence v = 1) : G.Adj v (G.attachment hv) := by
  obtain ⟨⟨e, i⟩, he⟩ := exists_endpoint_eq_of_valence_pos (G := G) (by omega : 0 < G.valence v)
  have he' := endpoint_rev_eq_attachment hv he
  fin_cases i
  · exact adj_iff.mpr ⟨e, Or.inl ⟨he, he'⟩⟩
  · exact adj_iff.mpr ⟨e, Or.inr ⟨he', he⟩⟩

/-- The two half-edges at a vertex of valence two, enumerated in some order. -/
noncomputable def halfEdgeOfValenceEqTwo {v : G.Vertex} (hv : G.valence v = 2) :
    Fin 2 ≃ {h : G.Edge × Fin 2 // G.endpoint h.1 h.2 = v} :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype, ← valence_def, hv])).symm

/-- At a loopless vertex of valence two, the two half-edges lie on distinct edges. -/
lemma halfEdgeOfValenceEqTwo_fst_ne {v : G.Vertex} (hv : G.valence v = 2)
    (hloop : ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v) :
    (G.halfEdgeOfValenceEqTwo hv 0).1.1 ≠ (G.halfEdgeOfValenceEqTwo hv 1).1.1 := by
  intro h
  have hne : (G.halfEdgeOfValenceEqTwo hv 0).1.2 ≠ (G.halfEdgeOfValenceEqTwo hv 1).1.2 :=
    fun h' ↦ absurd ((G.halfEdgeOfValenceEqTwo hv).injective (Subtype.ext (Prod.ext h h')))
      (by decide)
  -- The second index of a loopless edge at `v` is determined by the first.
  have hrev : (G.halfEdgeOfValenceEqTwo hv 1).1.2 = (G.halfEdgeOfValenceEqTwo hv 0).1.2.rev := by
    revert hne
    generalize (G.halfEdgeOfValenceEqTwo hv 0).1.2 = i
    generalize (G.halfEdgeOfValenceEqTwo hv 1).1.2 = j
    revert i j
    decide
  have h1 := (G.halfEdgeOfValenceEqTwo hv 1).2
  rw [← h, hrev] at h1
  exact endpoint_rev_ne hloop (G.halfEdgeOfValenceEqTwo hv 0).2 h1

/-- Every half-edge at a vertex of valence two is one of the two enumerated half-edges. -/
lemma exists_eq_halfEdgeOfValenceEqTwo {v : G.Vertex} (hv : G.valence v = 2)
    {h : G.Edge × Fin 2} (hh : G.endpoint h.1 h.2 = v) :
    ∃ k, (G.halfEdgeOfValenceEqTwo hv k).1 = h :=
  ⟨(G.halfEdgeOfValenceEqTwo hv).symm ⟨h, hh⟩, by simp⟩

/-- The **neighbours** of a loopless vertex of valence two: the components carrying the other
branches of its two nodes. For a rational bridge, these are the two components that it joins. -/
noncomputable def bridgeNeighbor {v : G.Vertex} (hv : G.valence v = 2) (k : Fin 2) : G.Vertex :=
  G.endpoint (G.halfEdgeOfValenceEqTwo hv k).1.1 (G.halfEdgeOfValenceEqTwo hv k).1.2.rev

/-- The neighbours of a loopless vertex are distinct from it. -/
lemma bridgeNeighbor_ne {v : G.Vertex} (hv : G.valence v = 2)
    (hloop : ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v) (k : Fin 2) :
    G.bridgeNeighbor hv k ≠ v :=
  endpoint_rev_ne hloop (G.halfEdgeOfValenceEqTwo hv k).2

/-! ### Edges and half-edges away from a vertex -/

/-- For a node `e` with a branch at `v` and a vertex `u ≠ v`, the node has a branch at `u`
exactly when its other branch lies there. -/
private lemma card_endpoint_eq_of_endpoint_eq {v u : G.Vertex} (hu : u ≠ v) {e : G.Edge}
    {i : Fin 2} (he : G.endpoint e i = v) :
    #{j | G.endpoint e j = u} = if G.endpoint e i.rev = u then 1 else 0 := by
  have hvu : G.endpoint e i ≠ u := he ▸ Ne.symm hu
  fin_cases i <;> simp_all [card_filter, Fin.sum_univ_two, -sum_boole]

/-- The valence of `u` splits into the half-edges on edges avoiding `v` and those on edges
meeting `v`. -/
private lemma valence_eq_sum_add_sum (v u : G.Vertex) :
    G.valence u = ∑ e : {e // ∀ i, G.endpoint e i ≠ v}, #{j | G.endpoint e.1 j = u} +
      ∑ e ∈ {e | ∃ i, G.endpoint e i = v}, #{j | G.endpoint e j = u} := by
  rw [valence_eq_sum, ← sum_filter_add_sum_filter_not univ (fun e ↦ ∀ i, G.endpoint e i ≠ v)]
  congr 1
  · exact sum_subtype _ (by simp) _
  · exact sum_congr (filter_congr fun e _ ↦ not_forall_not) fun _ _ ↦ rfl

/-- The edges avoiding `v` and the edges meeting `v` together make up all edges. -/
private lemma card_edge_eq (v : G.Vertex) :
    Fintype.card {e // ∀ i, G.endpoint e i ≠ v} + #{e | ∃ i, G.endpoint e i = v} =
      Fintype.card G.Edge := by
  have : (univ.filter fun e : G.Edge ↦ ∃ i, G.endpoint e i = v) =
      univ.filter fun e ↦ ¬ ∀ i, G.endpoint e i ≠ v :=
    filter_congr fun e _ ↦ by simp only [ne_eq, not_forall, not_not]
  rw [this, Fintype.card_subtype, card_filter_add_card_filter_not, card_univ]

/-! ### Contracting a tail -/

/-- The graph left after deleting a vertex of valence one is connected: chains in `G` collapse
onto it, the unique edge at the vertex being collapsed onto its attachment. -/
private lemma connected_contractTail {v : G.Vertex} (hv : G.valence v = 1) (x y : {w // w ≠ v}) :
    Relation.ReflTransGen (fun a b ↦ ∃ e : {e // ∀ i, G.endpoint e i ≠ v},
      ((⟨G.endpoint e.1 0, e.2 0⟩ : {w // w ≠ v}) = a ∧ ⟨G.endpoint e.1 1, e.2 1⟩ = b) ∨
        ((⟨G.endpoint e.1 0, e.2 0⟩ : {w // w ≠ v}) = b ∧ ⟨G.endpoint e.1 1, e.2 1⟩ = a)) x y := by
  refine G.connected_of_surjective
    (f := fun (e : {e // ∀ i, G.endpoint e i ≠ v}) i ↦ (⟨G.endpoint e.1 i, e.2 i⟩ : {w // w ≠ v}))
    (fun w ↦ if h : w = v then ⟨G.attachment hv, attachment_ne hv⟩ else ⟨w, h⟩)
    (fun w ↦ ⟨w.1, by simp [w.2]⟩) (fun e ↦ ?_) x y
  by_cases he : ∀ i, G.endpoint e i ≠ v
  · exact .inr ⟨⟨e, he⟩, .inl ⟨by simp [he 0], by simp [he 1]⟩⟩
  · -- The edge `e` is the unique edge at `v`; it joins `v` to its attachment.
    simp only [not_forall, not_not] at he
    obtain ⟨i, hi⟩ := he
    left
    have hrev := endpoint_rev_eq_attachment hv hi
    have hne := attachment_ne hv
    fin_cases i
    · simp_all
    · simp_all


variable (G)

/-- The **contraction** of a vertex `v` of valence one: `v` and its unique edge are deleted, and
the markings on `v` move to its attachment. When `v` is a rational tail, this is the dual graph of
the curve obtained by contracting the tail. -/
noncomputable abbrev contractTail {v : G.Vertex} (hv : G.valence v = 1) : DualGraph.{u} ι where
  Vertex := {w // w ≠ v}
  vertexNonempty := ⟨⟨G.attachment hv, attachment_ne hv⟩⟩
  Edge := {e // ∀ i, G.endpoint e i ≠ v}
  endpoint e i := ⟨G.endpoint e.1 i, e.2 i⟩
  genus w := G.genus w
  marking i :=
    if h : G.marking i = v then ⟨G.attachment hv, attachment_ne hv⟩ else ⟨G.marking i, h⟩
  connected := by exact G.connected_contractTail hv

section Tail

variable {G} {v : G.Vertex} (hv : G.valence v = 1)

@[simp]
lemma endpoint_contractTail (e : (G.contractTail hv).Edge) (i : Fin 2) :
    (G.contractTail hv).endpoint e i = ⟨G.endpoint e.1 i, e.2 i⟩ :=
  rfl

@[simp]
lemma genus_contractTail (w : (G.contractTail hv).Vertex) :
    (G.contractTail hv).genus w = G.genus w.1 :=
  rfl

/-- The markings on the tail move to its attachment; the other markings stay in place. -/
@[simp]
lemma marking_contractTail (i : ι) :
    (G.contractTail hv).marking i = if h : G.marking i = v then
      ⟨G.attachment hv, attachment_ne hv⟩ else ⟨G.marking i, h⟩ :=
  rfl

/-- Contracting a tail removes one vertex. -/
lemma card_vertex_contractTail :
    Fintype.card (G.contractTail hv).Vertex + 1 = Fintype.card G.Vertex :=
  Fintype.card_option.symm.trans (Fintype.card_congr (Equiv.optionSubtypeNe v))

/-- A sum over the vertices of the contracted graph is the sum over the vertices other than `v`. -/
lemma sum_vertex_contractTail {M : Type*} [AddCommMonoid M] (f : G.Vertex → M) :
    ∑ w : (G.contractTail hv).Vertex, f w.1 = ∑ w : {w // w ≠ v}, f w :=
  rfl

/-- The only edge meeting a vertex of valence one is its unique edge. -/
private lemma filter_endpoint_eq_of_valence_eq_one (hv : G.valence v = 1) {e : G.Edge} {i : Fin 2}
    (he : G.endpoint e i = v) : ({e' | ∃ j, G.endpoint e' j = v} : Finset G.Edge) = {e} := by
  ext e'
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  refine ⟨fun ⟨j, hj⟩ ↦ congrArg Prod.fst (eq_of_valence_eq_one hv (e', j) (e, i) hj he),
    fun h ↦ ⟨i, h ▸ he⟩⟩

/-- Contracting a tail removes one edge. -/
lemma card_edge_contractTail : Fintype.card (G.contractTail hv).Edge + 1 = Fintype.card G.Edge := by
  obtain ⟨⟨e, i⟩, he⟩ := exists_endpoint_eq_of_valence_pos (G := G) (by omega : 0 < G.valence v)
  have := G.card_edge_eq v
  rw [filter_endpoint_eq_of_valence_eq_one hv he, card_singleton] at this
  exact this

/-- Contracting a tail does not change the first Betti number. -/
@[simp]
theorem firstBetti_contractTail : (G.contractTail hv).firstBetti = G.firstBetti := by
  have := (G.contractTail hv).firstBetti_add_card_vertex
  have := G.firstBetti_add_card_vertex
  have := card_vertex_contractTail hv
  have := card_edge_contractTail hv
  omega

/-- Contracting a tail lowers the arithmetic genus by the genus of the tail. -/
theorem arithmeticGenus_contractTail :
    (G.contractTail hv).arithmeticGenus + G.genus v = G.arithmeticGenus := by
  rw [arithmeticGenus_def, arithmeticGenus_def, firstBetti_contractTail,
    Fintype.sum_eq_add_sum_subtype_ne G.genus v, ← sum_vertex_contractTail hv G.genus]
  omega

/-- Contracting a tail removes one branch at the attachment and leaves the other valences
unchanged. -/
theorem valence_contractTail (u : G.Vertex) (hu : u ≠ v) :
    (G.contractTail hv).valence ⟨u, hu⟩ + (if G.attachment hv = u then 1 else 0) =
      G.valence u := by
  obtain ⟨⟨e, i⟩, he⟩ := exists_endpoint_eq_of_valence_pos (G := G) (by omega : 0 < G.valence v)
  rw [G.valence_eq_sum_add_sum v u, filter_endpoint_eq_of_valence_eq_one hv he, sum_singleton,
    card_endpoint_eq_of_endpoint_eq hu he, endpoint_rev_eq_attachment hv he, valence_eq_sum]
  simp

section Markings

variable [Fintype ι]

/-- Contracting a tail moves its markings to its attachment. -/
@[simp]
theorem numMarkings_contractTail (u : G.Vertex) (hu : u ≠ v) :
    (G.contractTail hv).numMarkings ⟨u, hu⟩ =
      G.numMarkings u + if G.attachment hv = u then G.numMarkings v else 0 := by
  classical
  simp only [numMarkings_def]
  split_ifs with hw
  · subst hw
    rw [← card_union_of_disjoint (disjoint_filter.mpr fun i _ h h' ↦ hu (h.symm.trans h')),
      ← filter_or]
    congr 1
    ext i
    by_cases hi : G.marking i = v <;> simp [hi, Subtype.ext_iff, Ne.symm hu]
  · congr 1
    ext i
    by_cases hi : G.marking i = v
    · simp [hi, Subtype.ext_iff, hw, Ne.symm hu]
    · simp [hi, Subtype.ext_iff]

/-- Contracting a tail changes only the log-canonical degree of its attachment, which changes by
the number of markings on the tail minus one. -/
@[simp]
theorem logCanonicalDegree_contractTail (u : G.Vertex) (hu : u ≠ v) :
    (G.contractTail hv).logCanonicalDegree ⟨u, hu⟩ =
      G.logCanonicalDegree u + if G.attachment hv = u then (G.numMarkings v : ℤ) - 1 else 0 := by
  have hval := valence_contractTail hv u hu
  rw [logCanonicalDegree_def, logCanonicalDegree_def, numMarkings_contractTail hv u hu]
  split_ifs at hval ⊢ <;> push_cast <;> omega

end Markings

end Tail

/-! ### Contracting a bridge -/

/-- The graph left after replacing a loopless vertex of valence two by an edge joining its
neighbours is connected: chains in `G` collapse onto it, the first edge at the vertex being
collapsed onto the first neighbour and the second carried to the new edge. -/
private lemma connected_contractBridge {v : G.Vertex} (hv : G.valence v = 2)
    (hloop : ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v) (x y : {w // w ≠ v}) :
    let f : Option {e // ∀ i, G.endpoint e i ≠ v} → Fin 2 → {w // w ≠ v} := fun e ↦
      e.elim (fun k ↦ ⟨G.bridgeNeighbor hv k, bridgeNeighbor_ne hv hloop k⟩)
        fun e i ↦ ⟨G.endpoint e.1 i, e.2 i⟩
    Relation.ReflTransGen (fun a b ↦ ∃ e, (f e 0 = a ∧ f e 1 = b) ∨ (f e 0 = b ∧ f e 1 = a))
      x y := by
  refine G.connected_of_surjective
    (fun w ↦ if h : w = v then ⟨G.bridgeNeighbor hv 0, bridgeNeighbor_ne hv hloop 0⟩
      else ⟨w, h⟩)
    (fun w ↦ ⟨w.1, by simp [w.2]⟩) (fun e ↦ ?_) x y
  by_cases he : ∀ i, G.endpoint e i ≠ v
  · exact .inr ⟨some ⟨e, he⟩, .inl ⟨by simp [he 0], by simp [he 1]⟩⟩
  · -- The edge `e` is one of the two edges at `v`.
    simp only [not_forall, not_not] at he
    obtain ⟨i, hi⟩ := he
    obtain ⟨k, hk⟩ := exists_eq_halfEdgeOfValenceEqTwo hv (h := (e, i)) hi
    have hrev : G.endpoint e i.rev = G.bridgeNeighbor hv k := by rw [bridgeNeighbor, hk]
    have hne := bridgeNeighbor_ne hv hloop k
    fin_cases k <;> fin_cases i
    · left; simp_all
    · left; simp_all
    · exact .inr ⟨none, .inl ⟨by simp_all, by simp_all⟩⟩
    · exact .inr ⟨none, .inr ⟨by simp_all, by simp_all⟩⟩

/-- The **contraction** of an unmarked loopless vertex `v` of valence two: `v` and its two edges are
deleted, and a new edge, the edge `none`, joins the two neighbours of `v`. When `v` is a rational
bridge, this is the dual graph of the curve obtained by contracting the bridge. -/
noncomputable abbrev contractBridge {v : G.Vertex} (hv : G.valence v = 2)
    (hloop : ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v) (hm : ∀ i, G.marking i ≠ v) :
    DualGraph.{u} ι where
  Vertex := {w // w ≠ v}
  vertexNonempty := ⟨⟨G.bridgeNeighbor hv 0, bridgeNeighbor_ne hv hloop 0⟩⟩
  Edge := Option {e // ∀ i, G.endpoint e i ≠ v}
  endpoint e := e.elim (fun k ↦ ⟨G.bridgeNeighbor hv k, bridgeNeighbor_ne hv hloop k⟩)
    fun e i ↦ ⟨G.endpoint e.1 i, e.2 i⟩
  genus w := G.genus w
  marking i := ⟨G.marking i, hm i⟩
  connected := by exact G.connected_contractBridge hv hloop

section Bridge

variable {G} {v : G.Vertex} (hv : G.valence v = 2)
  (hloop : ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v) (hm : ∀ i, G.marking i ≠ v)

/-- The new edge joins the two neighbours of the contracted vertex. -/
@[simp]
lemma endpoint_contractBridge_none (k : Fin 2) :
    (G.contractBridge hv hloop hm).endpoint none k =
      ⟨G.bridgeNeighbor hv k, bridgeNeighbor_ne hv hloop k⟩ :=
  rfl

@[simp]
lemma endpoint_contractBridge_some (e : {e // ∀ i, G.endpoint e i ≠ v}) (i : Fin 2) :
    (G.contractBridge hv hloop hm).endpoint (some e) i = ⟨G.endpoint e.1 i, e.2 i⟩ :=
  rfl

@[simp]
lemma genus_contractBridge (w : (G.contractBridge hv hloop hm).Vertex) :
    (G.contractBridge hv hloop hm).genus w = G.genus w.1 :=
  rfl

@[simp]
lemma marking_contractBridge (i : ι) :
    (G.contractBridge hv hloop hm).marking i = ⟨G.marking i, hm i⟩ :=
  rfl

/-- Contracting a bridge removes one vertex. -/
lemma card_vertex_contractBridge :
    Fintype.card (G.contractBridge hv hloop hm).Vertex + 1 = Fintype.card G.Vertex :=
  Fintype.card_option.symm.trans (Fintype.card_congr (Equiv.optionSubtypeNe v))

/-- A sum over the vertices of the contracted graph is the sum over the vertices other than `v`. -/
lemma sum_vertex_contractBridge {M : Type*} [AddCommMonoid M] (f : G.Vertex → M) :
    ∑ w : (G.contractBridge hv hloop hm).Vertex, f w.1 = ∑ w : {w // w ≠ v}, f w :=
  rfl

/-- The edges meeting a vertex of valence two are the edges of its two half-edges. -/
private lemma filter_endpoint_eq_of_valence_eq_two :
    (univ.filter fun e : G.Edge ↦ ∃ j, G.endpoint e j = v) =
      {(G.halfEdgeOfValenceEqTwo hv 0).1.1, (G.halfEdgeOfValenceEqTwo hv 1).1.1} := by
  ext e
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨k, hk⟩ := exists_eq_halfEdgeOfValenceEqTwo hv (h := (e, j)) hj
    fin_cases k
    · exact .inl (congrArg Prod.fst hk).symm
    · exact .inr (congrArg Prod.fst hk).symm
  · rintro (rfl | rfl)
    exacts [⟨_, (G.halfEdgeOfValenceEqTwo hv 0).2⟩, ⟨_, (G.halfEdgeOfValenceEqTwo hv 1).2⟩]

/-- Contracting a bridge replaces its two edges by one. -/
lemma card_edge_contractBridge :
    Fintype.card (G.contractBridge hv hloop hm).Edge + 1 = Fintype.card G.Edge := by
  have := G.card_edge_eq v
  rw [filter_endpoint_eq_of_valence_eq_two hv,
    card_pair (halfEdgeOfValenceEqTwo_fst_ne hv hloop)] at this
  rw [Fintype.card_option]
  omega

/-- Contracting a bridge does not change the first Betti number. -/
@[simp]
theorem firstBetti_contractBridge :
    (G.contractBridge hv hloop hm).firstBetti = G.firstBetti := by
  have := (G.contractBridge hv hloop hm).firstBetti_add_card_vertex
  have := G.firstBetti_add_card_vertex
  have := card_vertex_contractBridge hv hloop hm
  have := card_edge_contractBridge hv hloop hm
  omega

/-- Contracting a bridge lowers the arithmetic genus by the genus of the bridge. -/
theorem arithmeticGenus_contractBridge :
    (G.contractBridge hv hloop hm).arithmeticGenus + G.genus v = G.arithmeticGenus := by
  rw [arithmeticGenus_def, arithmeticGenus_def, firstBetti_contractBridge,
    Fintype.sum_eq_add_sum_subtype_ne G.genus v, ← sum_vertex_contractBridge hv hloop hm G.genus]
  omega

/-- Contracting a bridge does not change any valence: each neighbour trades a branch of an edge at
the bridge for a branch of the new edge. -/
@[simp]
theorem valence_contractBridge (u : G.Vertex) (hu : u ≠ v) :
    (G.contractBridge hv hloop hm).valence ⟨u, hu⟩ = G.valence u := by
  rw [G.valence_eq_sum_add_sum v u, filter_endpoint_eq_of_valence_eq_two hv,
    sum_pair (halfEdgeOfValenceEqTwo_fst_ne hv hloop),
    card_endpoint_eq_of_endpoint_eq hu (G.halfEdgeOfValenceEqTwo hv 0).2,
    card_endpoint_eq_of_endpoint_eq hu (G.halfEdgeOfValenceEqTwo hv 1).2, valence_eq_sum,
    Fintype.sum_option]
  simp [bridgeNeighbor, card_filter, Fin.sum_univ_two, -sum_boole]
  omega

/-- Contracting a bridge does not move any marking. -/
@[simp]
theorem numMarkings_contractBridge [Fintype ι] (u : G.Vertex) (hu : u ≠ v) :
    (G.contractBridge hv hloop hm).numMarkings ⟨u, hu⟩ = G.numMarkings u := by
  simp [numMarkings_def, Subtype.ext_iff]

/-- Contracting a bridge does not change any log-canonical degree. -/
@[simp]
theorem logCanonicalDegree_contractBridge [Fintype ι] (u : G.Vertex) (hu : u ≠ v) :
    (G.contractBridge hv hloop hm).logCanonicalDegree ⟨u, hu⟩ = G.logCanonicalDegree u := by
  rw [logCanonicalDegree_def, logCanonicalDegree_def, valence_contractBridge,
    numMarkings_contractBridge]

end Bridge

/-! ### Stabilization -/

variable [Fintype ι]

/-- A **stabilization step**: `H` is obtained from `G` by contracting a rational tail carrying at
most one marking or an unmarked rational bridge. These are the contractions of a component of
nonpositive log-canonical degree that again give the dual graph of a pointed nodal curve. -/
inductive StabilizationStep : DualGraph.{u} ι → DualGraph.{u} ι → Prop
  /-- Contract a rational tail carrying at most one marking. -/
  | contractTail (G : DualGraph.{u} ι) {v : G.Vertex} (hv : G.IsRationalTail v)
      (hm : G.numMarkings v ≤ 1) :
      StabilizationStep G (G.contractTail (G.isRationalTail_iff.mp hv).2)
  /-- Contract an unmarked rational bridge. -/
  | contractBridge (G : DualGraph.{u} ι) {v : G.Vertex} (hv : G.IsRationalBridge v)
      (hm : ∀ i, G.marking i ≠ v) :
      StabilizationStep G
        (G.contractBridge (G.isRationalBridge_iff.mp hv).2.1 (G.isRationalBridge_iff.mp hv).2.2 hm)

variable {G} {H : DualGraph.{u} ι}

namespace StabilizationStep

/-- A stabilization step preserves the arithmetic genus. -/
theorem arithmeticGenus_eq (h : StabilizationStep G H) : H.arithmeticGenus = G.arithmeticGenus := by
  cases h with
  | contractTail hv =>
    have := arithmeticGenus_contractTail (G.isRationalTail_iff.mp hv).2
    have := (G.isRationalTail_iff.mp hv).1
    omega
  | contractBridge hv hm =>
    have := arithmeticGenus_contractBridge (G.isRationalBridge_iff.mp hv).2.1
      (G.isRationalBridge_iff.mp hv).2.2 hm
    have := (G.isRationalBridge_iff.mp hv).1
    omega

/-- A stabilization step removes a vertex. -/
theorem card_vertex_lt (h : StabilizationStep G H) :
    Fintype.card H.Vertex < Fintype.card G.Vertex := by
  cases h with
  | contractTail hv => have := card_vertex_contractTail (G.isRationalTail_iff.mp hv).2; omega
  | contractBridge hv hm =>
    have := card_vertex_contractBridge (G.isRationalBridge_iff.mp hv).2.1
      (G.isRationalBridge_iff.mp hv).2.2 hm
    omega

/-- A stabilization step contracts a vertex of nonpositive log-canonical degree. -/
theorem exists_logCanonicalDegree_nonpos (h : StabilizationStep G H) :
    ∃ v, G.logCanonicalDegree v ≤ 0 := by
  cases h with
  | contractTail hv hm => exact ⟨_, by rw [hv.logCanonicalDegree_eq]; omega⟩
  | contractBridge hv hm =>
    refine ⟨_, by rw [hv.logCanonicalDegree_eq, numMarkings_def]; simp [hm]⟩

end StabilizationStep

/-- A stable graph admits no stabilization step. -/
theorem IsStable.not_stabilizationStep (hG : G.IsStable) : ¬ StabilizationStep G H := fun h ↦
  have ⟨v, hv⟩ := h.exists_logCanonicalDegree_nonpos
  (G.isStable_iff.mp hG v).not_ge hv

/-- Iterated stabilization steps preserve the arithmetic genus. -/
theorem arithmeticGenus_eq_of_reflTransGen (h : Relation.ReflTransGen StabilizationStep G H) :
    H.arithmeticGenus = G.arithmeticGenus := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact hstep.arithmeticGenus_eq.trans ih

variable (G)

/-- In the stable range `2g - 2 + n > 0`, a graph that is not stable admits a stabilization
step. A vertex of nonpositive log-canonical degree is a rational tail with at most one marking, a
rational bridge without markings, or the only vertex; in the last case its log-canonical degree is
`2g - 2 + n`. -/
theorem exists_stabilizationStep_of_not_isStable
    (hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι) (hG : ¬ G.IsStable) :
    ∃ H, StabilizationStep G H := by
  obtain ⟨v, hv⟩ : ∃ v, G.logCanonicalDegree v ≤ 0 := by
    simpa [isStable_iff, not_forall, not_lt] using hG
  have hw : ∃ w, w ≠ v := by
    by_contra! h
    have := G.logCanonicalDegree_eq_of_forall_eq h
    omega
  rcases isRationalTail_or_isRationalBridge_of_logCanonicalDegree_nonpos hv hw with
    ⟨ht, hm⟩ | ⟨hb, hm⟩
  · exact ⟨_, .contractTail G ht hm⟩
  · exact ⟨_, .contractBridge G hb hm⟩

/-- In the stable range `2g - 2 + n > 0`, a graph is stable exactly when it admits no
stabilization step. -/
theorem isStable_iff_forall_not_stabilizationStep
    (hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι) :
    G.IsStable ↔ ∀ H, ¬ StabilizationStep G H :=
  ⟨fun hG _ ↦ hG.not_stabilizationStep, fun h ↦ by_contra fun hG ↦
    have ⟨H, hH⟩ := G.exists_stabilizationStep_of_not_isStable hrange hG
    h H hH⟩

/-- **Stabilization terminates.** In the stable range `2g - 2 + n > 0`, iterating stabilization
steps from any graph reaches a stable graph, of the same arithmetic genus by
`TauCeti.DualGraph.arithmeticGenus_eq_of_reflTransGen`. Termination holds because every step
removes a vertex. -/
theorem exists_reflTransGen_stabilizationStep_isStable
    (hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι) :
    ∃ H, Relation.ReflTransGen StabilizationStep G H ∧ H.IsStable := by
  induction hn : Fintype.card G.Vertex using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    by_cases hG : G.IsStable
    · exact ⟨G, .refl, hG⟩
    · obtain ⟨H, hH⟩ := G.exists_stabilizationStep_of_not_isStable hrange hG
      obtain ⟨K, hK, hKs⟩ :=
        ih _ (hn ▸ hH.card_vertex_lt) H (by rw [hH.arithmeticGenus_eq]; exact hrange) rfl
      exact ⟨K, .head hH hK, hKs⟩

end DualGraph

end TauCeti
