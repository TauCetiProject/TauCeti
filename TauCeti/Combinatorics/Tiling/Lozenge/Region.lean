/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Lattice
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Regions of the triangular lattice

A region of the triangular lattice is a set `R` of faces, finite or infinite. This file defines
the vertices, edges, interior and boundary edges, boundary vertices and graphs of a region, the
union of its faces in `ℝ²`, and the region `facesOf V` spanned by a set `V` of vertices: the faces
with all three vertices in `V`, which is Aggarwal's induced-subgraph convention.

## Main definitions

* `TauCeti.regionVertices`, `TauCeti.regionEdges`: the vertices `V(R)` and edges `E(R)` of the
  faces of a region.
* `TauCeti.interiorEdges`, `TauCeti.boundaryEdges`: the edges with both faces in `R`, and the edges
  of `R` lying in a face outside `R`.
* `TauCeti.boundaryVertices`: the endpoints `∂R` of the boundary edges.
* `TauCeti.regionGraph`: the graph on `ℤ × ℤ` whose edges are the edges of `R`.
* `TauCeti.boundaryGraph`: the graph on the boundary vertices `∂R` whose edges are the boundary
  edges of `R`.
* `TauCeti.IsConnectedRegion`: any two vertices of `R` are joined in `regionGraph R`.
* `TauCeti.regionUnion`: the union `F(R) ⊆ ℝ²` of the closed triangles of the faces of `R`.
* `TauCeti.facesOf`: the faces with all three vertices in a set `V`.

## Main statements

* `TauCeti.regionVertices_eq`: the vertices of `R` are the endpoints of its edges.
* `TauCeti.regionGraph_adj`, `TauCeti.boundaryGraph_adj`: the edges of the two graphs.
* `TauCeti.isConnectedRegion_singleton`: a single face is a connected region, and
  `TauCeti.isConnectedRegion_iff_reachable` restates connectedness through the edges of `R`.
* `TauCeti.three_mul_card_eq_two_mul_ncard_interiorEdges_add_ncard_boundaryEdges`: for a finite
  region, `3 |R| = 2 |E°(R)| + |E∂(R)|`.
* `TauCeti.notMem_boundaryVertices_iff`: a vertex of `R` is not a boundary vertex exactly when
  all six faces at it lie in `R`.
* `TauCeti.regionEdges_vadd`, `TauCeti.regionEdges_rot` and their analogues: translations and the
  rotation `ρ` act compatibly with the constructions; on `F(R) ⊆ ℝ²`, `ρ` acts by the linear map
  `(x, y) ↦ (-y, x - y)` (`TauCeti.regionUnion_rot`).
* `TauCeti.boundaryVertices_facesOf`: when every vertex of `V` lies in a face of `facesOf V`,
  Aggarwal's boundary of `V` (its vertices adjacent to a vertex outside `V`) is
  `∂(facesOf V)`.

## References

* A. Aggarwal, *Universality for lozenge tiling local statistics*, Ann. of Math. 198 (2023),
  Section 1.2.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 1.
-/

public section

open Pointwise

namespace TauCeti

/-! ### The constructions -/

/-- The vertices `V(R)` of a region: the vertices of its faces. -/
def regionVertices (R : Set TriFace) : Set (ℤ × ℤ) :=
  {u | ∃ f ∈ R, u ∈ f.vertices}

/-- The edges `E(R)` of a region: the edges of its faces. -/
def regionEdges (R : Set TriFace) : Set TriEdge :=
  {e | ∃ f ∈ R, e ∈ f.edges}

/-- The interior edges `E°(R)` of a region: the edges both of whose faces lie in `R`. -/
def interiorEdges (R : Set TriFace) : Set TriEdge :=
  {e | ∀ f : TriFace, e ∈ f.edges → f ∈ R}

/-- The boundary edges `E∂(R)` of a region: its edges that are not interior, that is, lying in a
face outside `R`, so that exactly one of their two faces is in `R`. -/
def boundaryEdges (R : Set TriFace) : Set TriEdge :=
  regionEdges R \ interiorEdges R

/-- The boundary vertices `∂R` of a region: the endpoints of its boundary edges. -/
def boundaryVertices (R : Set TriFace) : Set (ℤ × ℤ) :=
  {u | ∃ e ∈ boundaryEdges R, u ∈ e.endpoints}

/-- The edge graph of a region: the simple graph on `ℤ × ℤ` whose edges are the segments of the
edges of `R`. Vertices outside `V(R)` are isolated. -/
def regionGraph (R : Set TriFace) : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.fromEdgeSet (TriEdge.endpoints '' regionEdges R)

/-- The boundary graph of a region: the simple graph on the boundary vertices `∂R` whose edges are
the segments of the boundary edges of `R`. -/
def boundaryGraph (R : Set TriFace) : SimpleGraph (boundaryVertices R) :=
  (SimpleGraph.fromEdgeSet (TriEdge.endpoints '' boundaryEdges R)).induce (boundaryVertices R)

/-- A region is connected when any two of its vertices are joined by a path of its edges. -/
def IsConnectedRegion (R : Set TriFace) : Prop :=
  ∀ u ∈ regionVertices R, ∀ u' ∈ regionVertices R, (regionGraph R).Reachable u u'

/-- The union `F(R) ⊆ ℝ²` of the closed triangles of the faces of a region, the convex hulls of
their vertices under `ℤ² ⊆ ℝ²`. -/
def regionUnion (R : Set TriFace) : Set (ℝ × ℝ) :=
  ⋃ f ∈ R, convexHull ℝ ((fun u : ℤ × ℤ => ((u.1 : ℝ), (u.2 : ℝ))) '' f.vertices)

/-- The region `Faces(V)` spanned by a set `V` of vertices: the faces with all three vertices in
`V`. -/
def facesOf (V : Set (ℤ × ℤ)) : Set TriFace :=
  {f | ∀ u ∈ f.vertices, u ∈ V}

variable {R S : Set TriFace} {e : TriEdge} {f : TriFace} {u u' : ℤ × ℤ}

theorem mem_regionVertices : u ∈ regionVertices R ↔ ∃ f ∈ R, u ∈ f.vertices := Iff.rfl

theorem mem_regionEdges : e ∈ regionEdges R ↔ ∃ f ∈ R, e ∈ f.edges := Iff.rfl

theorem mem_interiorEdges : e ∈ interiorEdges R ↔ ∀ f : TriFace, e ∈ f.edges → f ∈ R := Iff.rfl

theorem mem_boundaryEdges : e ∈ boundaryEdges R ↔ e ∈ regionEdges R ∧ ∃ f ∉ R, e ∈ f.edges := by
  simp only [boundaryEdges, Set.mem_sdiff, mem_interiorEdges, not_forall, exists_prop, and_comm]

theorem mem_boundaryVertices : u ∈ boundaryVertices R ↔ ∃ e ∈ boundaryEdges R, u ∈ e.endpoints :=
  Iff.rfl

theorem mem_facesOf {V : Set (ℤ × ℤ)} : f ∈ facesOf V ↔ ∀ u ∈ f.vertices, u ∈ V := Iff.rfl

theorem isConnectedRegion_def : IsConnectedRegion R ↔
    ∀ u ∈ regionVertices R, ∀ u' ∈ regionVertices R, (regionGraph R).Reachable u u' := Iff.rfl

theorem mem_regionUnion {x : ℝ × ℝ} : x ∈ regionUnion R ↔
    ∃ f ∈ R, x ∈ convexHull ℝ ((fun u : ℤ × ℤ => ((u.1 : ℝ), (u.2 : ℝ))) '' f.vertices) := by
  simp only [regionUnion, Set.mem_iUnion, exists_prop]

theorem regionUnion_def (R : Set TriFace) : regionUnion R =
    ⋃ f ∈ R, convexHull ℝ ((fun u : ℤ × ℤ => ((u.1 : ℝ), (u.2 : ℝ))) '' f.vertices) := (rfl)

theorem mem_regionEdges_iff : e ∈ regionEdges R ↔ e.whiteFace ∈ R ∨ e.blackFace ∈ R := by
  simp only [mem_regionEdges, TriFace.mem_edges_iff]
  constructor
  · rintro ⟨f, hf, rfl | rfl⟩ <;> simp [hf]
  · rintro (h | h) <;> exact ⟨_, h, by simp⟩

theorem mem_interiorEdges_iff : e ∈ interiorEdges R ↔ e.whiteFace ∈ R ∧ e.blackFace ∈ R := by
  simp only [mem_interiorEdges, TriFace.mem_edges_iff]
  exact ⟨fun h => ⟨h _ (Or.inl rfl), h _ (Or.inr rfl)⟩, by rintro ⟨h, h'⟩ f (rfl | rfl) <;> simpa⟩

/-- An edge lying in two distinct faces of `R` is an interior edge of `R`. -/
theorem mem_interiorEdges_of_mem_edges {g : TriFace} (hfg : f ≠ g) (hf : e ∈ f.edges)
    (hg : e ∈ g.edges) (hfR : f ∈ R) (hgR : g ∈ R) : e ∈ interiorEdges R :=
  mem_interiorEdges.2 fun _ hk =>
    (TriFace.eq_or_eq_of_mem_edges hfg hf hg hk).elim (· ▸ hfR) (· ▸ hgR)

/-- A boundary edge has exactly one of its two faces in `R`. -/
theorem mem_boundaryEdges_iff : e ∈ boundaryEdges R ↔ (e.whiteFace ∈ R ↔ e.blackFace ∉ R) := by
  simp only [mem_boundaryEdges, mem_regionEdges_iff, TriFace.mem_edges_iff]
  constructor
  · rintro ⟨h, f, hf, rfl | rfl⟩ <;> tauto
  · intro h
    by_cases hw : e.whiteFace ∈ R
    · exact ⟨Or.inl hw, _, h.1 hw, Or.inr rfl⟩
    · exact ⟨Or.inr (not_not.1 (h.not.1 hw)), _, hw, Or.inl rfl⟩

theorem interiorEdges_subset_regionEdges : interiorEdges R ⊆ regionEdges R := fun _ he =>
  mem_regionEdges_iff.2 (Or.inl (mem_interiorEdges_iff.1 he).1)

theorem boundaryEdges_subset_regionEdges : boundaryEdges R ⊆ regionEdges R := fun _ he => he.1

/-- An edge of a region is an interior edge or a boundary edge, and not both. -/
theorem notMem_boundaryEdges_iff (he : e ∈ regionEdges R) :
    e ∉ boundaryEdges R ↔ e ∈ interiorEdges R := by
  rw [mem_regionEdges_iff] at he
  rw [mem_boundaryEdges_iff, mem_interiorEdges_iff]
  tauto

theorem disjoint_interiorEdges_boundaryEdges : Disjoint (interiorEdges R) (boundaryEdges R) :=
  Set.disjoint_left.2 fun _ he hb =>
    (notMem_boundaryEdges_iff (interiorEdges_subset_regionEdges he)).2 he hb

theorem edges_subset_regionEdges (hf : f ∈ R) : (f.edges : Set TriEdge) ⊆ regionEdges R :=
  fun _ he => ⟨f, hf, he⟩

theorem regionEdges_mono (h : R ⊆ S) : regionEdges R ⊆ regionEdges S :=
  fun _ ⟨f, hf, he⟩ => ⟨f, h hf, he⟩

/-- A finite region has finitely many edges. -/
theorem finite_regionEdges (R : Finset TriFace) : (regionEdges (R : Set TriFace)).Finite :=
  (R.biUnion TriFace.edges).finite_toSet.subset fun _ ⟨f, hf, he⟩ =>
    Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨f, hf, he⟩)

theorem interiorEdges_mono (h : R ⊆ S) : interiorEdges R ⊆ interiorEdges S :=
  fun _ he f hf => h (he f hf)

theorem regionVertices_mono (h : R ⊆ S) : regionVertices R ⊆ regionVertices S :=
  fun _ ⟨f, hf, hu⟩ => ⟨f, h hf, hu⟩

/-- The vertices of a region are the endpoints of its edges. -/
theorem regionVertices_eq (R : Set TriFace) :
    regionVertices R = {u | ∃ e ∈ regionEdges R, u ∈ e.endpoints} := by
  ext u
  constructor
  · rintro ⟨f, hf, hu⟩
    obtain ⟨u', hu', hne⟩ := Finset.exists_mem_ne (by simp : 1 < f.vertices.card) u
    obtain ⟨e, he, hee⟩ := TriFace.exists_mem_edges_endpoints_eq hu hu' hne.symm
    exact ⟨e, ⟨f, hf, he⟩, hee ▸ Sym2.mem_mk_left u u'⟩
  · rintro ⟨e, ⟨f, hf, he⟩, hu⟩
    exact ⟨f, hf, TriFace.mem_vertices_of_mem_endpoints he hu⟩

theorem boundaryVertices_subset_regionVertices : boundaryVertices R ⊆ regionVertices R := by
  rw [regionVertices_eq]
  exact fun _ ⟨e, he, hu⟩ => ⟨e, he.1, hu⟩

/-- The graph whose edges are the endpoint pairs of a set of lattice edges: no endpoint pair is a
loop, so `SimpleGraph.fromEdgeSet` keeps all of them. -/
private theorem fromEdgeSet_endpoints_adj (E : Set TriEdge) :
    (SimpleGraph.fromEdgeSet (TriEdge.endpoints '' E)).Adj u u' ↔
      ∃ e ∈ E, e.endpoints = s(u, u') := by
  rw [SimpleGraph.fromEdgeSet_adj, Set.mem_image, and_iff_left_iff_imp]
  rintro ⟨e, -, he⟩ rfl
  exact e.not_isDiag_endpoints (he ▸ Sym2.mk_isDiag_iff.2 rfl)

/-- The edges of `regionGraph R` are the endpoint pairs of the edges of `R`. -/
theorem regionGraph_adj : (regionGraph R).Adj u u' ↔ ∃ e ∈ regionEdges R, e.endpoints = s(u, u') :=
  fromEdgeSet_endpoints_adj _

/-- The edges of `boundaryGraph R` are the endpoint pairs of the boundary edges of `R`. -/
theorem boundaryGraph_adj {u u' : boundaryVertices R} :
    (boundaryGraph R).Adj u u' ↔ ∃ e ∈ boundaryEdges R, e.endpoints = s(u.val, u'.val) := by
  rw [boundaryGraph, SimpleGraph.induce_adj, fromEdgeSet_endpoints_adj]

theorem regionGraph_mono (h : R ⊆ S) : regionGraph R ≤ regionGraph S := fun _ _ huu => by
  obtain ⟨e, he, h'⟩ := regionGraph_adj.1 huu
  exact regionGraph_adj.2 ⟨e, regionEdges_mono h he, h'⟩

theorem regionGraph_edgeSet (R : Set TriFace) :
    (regionGraph R).edgeSet = TriEdge.endpoints '' regionEdges R := by
  rw [regionGraph, SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
  rintro _ ⟨e, -, rfl⟩
  exact e.not_isDiag_endpoints

theorem v_mem_boundaryVertices (he : e ∈ boundaryEdges R) : e.v ∈ boundaryVertices R :=
  ⟨e, he, by simp⟩

theorem target_mem_boundaryVertices (he : e ∈ boundaryEdges R) :
    e.target ∈ boundaryVertices R :=
  ⟨e, he, by simp⟩

/-- The edges of `boundaryGraph R`, as pairs of points of `ℤ × ℤ`, are the endpoint pairs of the
boundary edges of `R`. -/
theorem boundaryGraph_edgeSet (R : Set TriFace) :
    Sym2.map Subtype.val '' (boundaryGraph R).edgeSet = TriEdge.endpoints '' boundaryEdges R := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    induction y using Sym2.ind with
    | h p p' =>
      obtain ⟨e, he, h⟩ := boundaryGraph_adj.1 hy
      exact ⟨e, he, by rw [h, Sym2.map_mk]⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨s(⟨e.v, v_mem_boundaryVertices he⟩, ⟨e.target, target_mem_boundaryVertices he⟩),
      boundaryGraph_adj.2 ⟨e, he, TriEdge.endpoints_def e⟩, (TriEdge.endpoints_def e).symm⟩

/-- The boundary graph is a subgraph of the edge graph induced on `∂R`. -/
theorem boundaryGraph_le_induce_regionGraph (R : Set TriFace) :
    boundaryGraph R ≤ (regionGraph R).induce (boundaryVertices R) := fun _ _ h => by
  obtain ⟨e, he, h⟩ := boundaryGraph_adj.1 h
  exact SimpleGraph.induce_adj.2 (regionGraph_adj.2 ⟨e, he.1, h⟩)

private theorem exists_adj_iff (E : Set TriEdge) :
    (∃ u', ∃ e ∈ E, e.endpoints = s(u, u')) ↔ ∃ e ∈ E, u ∈ e.endpoints := by
  constructor
  · rintro ⟨u', e, he, h⟩
    exact ⟨e, he, h ▸ Sym2.mem_mk_left u u'⟩
  · rintro ⟨e, he, hu⟩
    exact ⟨Sym2.Mem.other hu, e, he, (Sym2.other_spec hu).symm⟩

/-- The non-isolated vertices of `regionGraph R` are the vertices of `R`. -/
theorem regionGraph_support (R : Set TriFace) : (regionGraph R).support = regionVertices R := by
  ext u
  rw [SimpleGraph.mem_support, regionVertices_eq]
  simp only [regionGraph_adj]
  exact exists_adj_iff _

/-- `boundaryGraph R` has no isolated vertex. -/
theorem boundaryGraph_support (R : Set TriFace) : (boundaryGraph R).support = Set.univ := by
  refine Set.eq_univ_of_forall fun ⟨u, e, he, hu⟩ => ?_
  exact ⟨⟨_, e, he, Sym2.other_mem hu⟩, boundaryGraph_adj.2 ⟨e, he, (Sym2.other_spec hu).symm⟩⟩

/-! ### Connected regions -/

/-- The empty region is connected. -/
@[simp] theorem isConnectedRegion_empty : IsConnectedRegion ∅ :=
  fun _ ⟨f, hf, _⟩ => (Set.notMem_empty f hf).elim

/-- A single face is a connected region: any two of its vertices are joined by one of its
edges. -/
theorem isConnectedRegion_singleton (f : TriFace) : IsConnectedRegion {f} := by
  rintro u ⟨g, hg, hu⟩ u' ⟨g', hg', hu'⟩
  rw [Set.mem_singleton_iff] at hg hg'
  subst hg hg'
  by_cases h : u = u'
  · exact h ▸ SimpleGraph.Reachable.refl _
  · obtain ⟨e, he, hee⟩ := TriFace.exists_mem_edges_endpoints_eq hu hu' h
    exact (regionGraph_adj.2 ⟨e, ⟨_, Set.mem_singleton _, he⟩, hee⟩).reachable

private theorem reachable_v_of_mem_endpoints (he : e ∈ regionEdges R) (hu : u ∈ e.endpoints) :
    (regionGraph R).Reachable u e.v := by
  rcases TriEdge.mem_endpoints.1 hu with rfl | rfl
  · rfl
  · exact (regionGraph_adj.2 ⟨e, he, (TriEdge.endpoints_def e).trans Sym2.eq_swap⟩).reachable

/-- A region is connected exactly when the initial vertices of any two of its edges are joined in
its edge graph. -/
theorem isConnectedRegion_iff_reachable : IsConnectedRegion R ↔
    ∀ e ∈ regionEdges R, ∀ e' ∈ regionEdges R, (regionGraph R).Reachable e.v e'.v := by
  have hv : ∀ e ∈ regionEdges R, e.v ∈ regionVertices R := fun e he => by
    rw [regionVertices_eq]
    exact ⟨e, he, by simp⟩
  refine ⟨fun h e he e' he' => h _ (hv e he) _ (hv e' he'), fun h u hu u' hu' => ?_⟩
  rw [regionVertices_eq] at hu hu'
  obtain ⟨e, he, hue⟩ := hu
  obtain ⟨e', he', hue'⟩ := hu'
  exact ((reachable_v_of_mem_endpoints he hue).trans (h e he e' he')).trans
    (reachable_v_of_mem_endpoints he' hue').symm

theorem regionUnion_mono (h : R ⊆ S) : regionUnion R ⊆ regionUnion S :=
  Set.biUnion_subset_biUnion_left h

/-- The vertices of `R`, as points of `ℝ²`, lie in `F(R)`. -/
theorem mk_mem_regionUnion (hu : u ∈ regionVertices R) :
    ((u.1 : ℝ), (u.2 : ℝ)) ∈ regionUnion R := by
  obtain ⟨f, hf, hu⟩ := hu
  exact Set.mem_biUnion hf (subset_convexHull ℝ _ ⟨u, hu, rfl⟩)

/-! ### Counting edges of a finite region -/

/-- **Edge count of a finite region.** Each face has three edges, an interior edge lies in two
faces of `R` and a boundary edge in one: `3 |R| = 2 |E°(R)| + |E∂(R)|`. -/
theorem three_mul_card_eq_two_mul_ncard_interiorEdges_add_ncard_boundaryEdges
    (R : Finset TriFace) :
    3 * R.card =
      2 * (interiorEdges (R : Set TriFace)).ncard + (boundaryEdges (R : Set TriFace)).ncard := by
  -- Double count the incidences between the faces of `R` and the finite set `T` of their edges:
  -- each face has three edges, and an edge of `T` lies in two faces of `R` when it is interior
  -- and in one when it is a boundary edge.
  set T := R.biUnion TriFace.edges
  have hT : regionEdges (R : Set TriFace) = ↑T := by ext; simp [T, mem_regionEdges]
  have hint : interiorEdges (R : Set TriFace) =
      ↑(T.filter fun e => e.whiteFace ∈ R ∧ e.blackFace ∈ R) := by
    ext e
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_interiorEdges_iff]
    refine ⟨fun h => ⟨?_, h⟩, And.right⟩
    rw [← Finset.mem_coe, ← hT]
    exact mem_regionEdges_iff.2 (Or.inl h.1)
  have hbd : boundaryEdges (R : Set TriFace) =
      ↑(T.filter fun e => ¬(e.whiteFace ∈ R ∧ e.blackFace ∈ R)) := by
    rw [boundaryEdges, hint, hT, Finset.filter_not, Finset.coe_sdiff]
  rw [hint, hbd, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := R) (t := T) (r := fun f e => e ∈ f.edges)
  have habove : ∀ f ∈ R, (T.bipartiteAbove (fun f e => e ∈ f.edges) f).card = 3 := by
    intro f hf
    have : T.bipartiteAbove (fun f e => e ∈ f.edges) f = f.edges := by
      ext e
      simp only [Finset.bipartiteAbove, Finset.mem_filter]
      exact ⟨And.right, fun he => ⟨Finset.mem_biUnion.2 ⟨f, hf, he⟩, he⟩⟩
    rw [this, TriFace.card_edges]
  have hbelow : ∀ e ∈ T, (R.bipartiteBelow (fun f e => e ∈ f.edges) e).card =
      if e.whiteFace ∈ R ∧ e.blackFace ∈ R then 2 else 1 := by
    intro e he
    have hfil : R.bipartiteBelow (fun f e => e ∈ f.edges) e = e.faces.filter (· ∈ R) := by
      ext f
      simp [Finset.bipartiteBelow, and_comm]
    rw [hfil]
    have hw := e.whiteFace_ne_blackFace
    rw [← Finset.mem_coe, ← hT, mem_regionEdges_iff] at he
    rw [TriEdge.faces_def, Finset.filter_insert, Finset.filter_singleton]
    by_cases h₁ : e.whiteFace ∈ R <;> by_cases h₂ : e.blackFace ∈ R <;> simp_all
  rw [Finset.sum_congr rfl habove, Finset.sum_congr rfl hbelow, Finset.sum_ite] at hdc
  simp only [Finset.sum_const, smul_eq_mul] at hdc
  omega

/-! ### Boundary vertices and the six faces at a vertex -/

/-- A vertex of `R` is not a boundary vertex exactly when all six faces at it lie in `R`. -/
theorem notMem_boundaryVertices_iff (hu : u ∈ regionVertices R) :
    u ∉ boundaryVertices R ↔ ↑(vertexFaces u) ⊆ R := by
  constructor
  · intro hb
    have key : ∀ e : TriEdge, u ∈ e.endpoints → (e.whiteFace ∈ R ↔ e.blackFace ∈ R) := by
      intro e he
      by_contra h
      refine hb ⟨e, mem_boundaryEdges_iff.2 ?_, he⟩
      tauto
    obtain ⟨x, y⟩ := u
    -- Consecutive faces around `u = (x, y)` share an edge at `u`. With `W(·)`, `B(·)` the white
    -- and black faces, the five edges below link the six faces of `vertexFaces u` in a chain:
    -- `h₅ : W(u) ~ B(u - e₂)`, `h₁ : W(u) ~ B(u)`, `h₂ : B(u) ~ W(u - e₁)`,
    -- `h₃ : W(u - e₁) ~ B(u - e₁ - e₂)` and `h₄ : B(u - e₁ - e₂) ~ W(u - e₁ - e₂)`.
    have h₁ := key ⟨(x, y), 2⟩ (by simp)
    have h₂ := key ⟨(x, y), 1⟩ (by simp)
    have h₃ := key ⟨(x - 1, y), 0⟩ (by simp)
    have h₄ := key ⟨(x - 1, y - 1), 2⟩ (by simp)
    have h₅ := key ⟨(x, y), 0⟩ (by simp)
    simp only [TriEdge.whiteFace_mk, TriEdge.blackFace_mk] at h₁ h₂ h₃ h₄ h₅
    norm_num [Prod.ext_iff] at h₁ h₂ h₃ h₄ h₅
    have hall : ∀ g ∈ vertexFaces (x, y), (g ∈ R ↔ (⟨(x, y), true⟩ : TriFace) ∈ R) := by
      intro g hg
      simp only [vertexFaces_def, Finset.mem_insert, Finset.mem_singleton, Prod.mk_sub_mk,
        sub_zero] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Iff.rfl
      · exact h₂.trans h₁.symm
      · exact h₄.trans (h₃.symm.trans (h₂.trans h₁.symm))
      · exact h₁.symm
      · exact h₅.symm
      · exact h₃.symm.trans (h₂.trans h₁.symm)
    obtain ⟨g, hg, hug⟩ := hu
    rw [← mem_vertexFaces] at hug
    exact fun f hf => (hall f hf).2 ((hall g hug).1 hg)
  · rintro h ⟨e, hb, hu⟩
    obtain ⟨-, g, hg, he⟩ := mem_boundaryEdges.1 hb
    exact hg (h (mem_vertexFaces.2 (TriFace.mem_vertices_of_mem_endpoints he hu)))

/-! ### Regions spanned by vertex sets -/

theorem facesOf_mono {V W : Set (ℤ × ℤ)} (h : V ⊆ W) : facesOf V ⊆ facesOf W :=
  fun _ hf u hu => h (hf u hu)

/-- The vertices of `facesOf V` lie in `V`. -/
theorem regionVertices_facesOf_subset (V : Set (ℤ × ℤ)) : regionVertices (facesOf V) ⊆ V :=
  fun _ ⟨_, hf, hu⟩ => hf _ hu

/-- **Aggarwal's boundary.** When every vertex of `V` lies in a face of `facesOf V`, the boundary
vertices of `facesOf V` are the vertices of `V` joined by an edge of the lattice to a vertex
outside `V`. -/
theorem boundaryVertices_facesOf {V : Set (ℤ × ℤ)} (hV : V ⊆ regionVertices (facesOf V)) :
    boundaryVertices (facesOf V) =
      {u ∈ V | ∃ e : TriEdge, ∃ u' ∉ V, e.endpoints = s(u, u')} := by
  ext u
  constructor
  · rintro ⟨e, hb, hu⟩
    obtain ⟨⟨f, hf, he⟩, g, hg, heg⟩ := mem_boundaryEdges.1 hb
    have huV : u ∈ V := hf u (TriFace.mem_vertices_of_mem_endpoints he hu)
    obtain ⟨u', hu', hu'V⟩ : ∃ u' ∈ g.vertices, u' ∉ V := by
      by_contra! h
      exact hg h
    have hne : u ≠ u' := fun h => hu'V (h ▸ huV)
    obtain ⟨e', -, he'⟩ := TriFace.exists_mem_edges_endpoints_eq
      (TriFace.mem_vertices_of_mem_endpoints heg hu) hu' hne
    exact ⟨huV, e', u', hu'V, he'⟩
  · rintro ⟨huV, e, u', hu'V, he⟩
    by_contra hb
    have hsub := (notMem_boundaryVertices_iff (hV huV)).1 hb
    have hwu : u ∈ e.whiteFace.vertices :=
      TriFace.mem_vertices_of_mem_endpoints e.mem_whiteFace_edges (he ▸ Sym2.mem_mk_left u u')
    exact hu'V (hsub (mem_vertexFaces.2 hwu) u'
      (TriFace.mem_vertices_of_mem_endpoints e.mem_whiteFace_edges (he ▸ Sym2.mem_mk_right u u')))

/-! ### Symmetries -/

/- The constructions are transported along a permutation `φ` of the faces, `ψ` of the edges and `χ`
of the vertices compatible with incidence. The translation and rotation lemmas below instantiate
these with `AddAction.toPerm w` and `latticeRot.toEquiv`, whose coercions to functions are
definitionally `(w +ᵥ ·)` and `latticeRot`, so that `AddAction.toPerm w '' s` is `w +ᵥ s` and
`latticeRot.toEquiv '' s` is `latticeRot '' s` by definition. -/

section Transfer

variable (φ : Equiv.Perm TriFace) (ψ : Equiv.Perm TriEdge) (χ : Equiv.Perm (ℤ × ℤ))
  (hψ : ∀ e f, ψ e ∈ (φ f).edges ↔ e ∈ f.edges)
  (hχ : ∀ e, (ψ e).endpoints = e.endpoints.map χ)
  (hφ : ∀ f u, χ u ∈ (φ f).vertices ↔ u ∈ f.vertices)

include hψ in
private theorem regionEdges_image : regionEdges (φ '' R) = ψ '' regionEdges R := by
  ext e
  obtain ⟨e, rfl⟩ := ψ.surjective e
  rw [ψ.injective.mem_set_image]
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, he⟩
    exact ⟨f, hf, (hψ e f).1 he⟩
  · rintro ⟨f, hf, he⟩
    exact ⟨φ f, Set.mem_image_of_mem φ hf, (hψ e f).2 he⟩

include hψ in
private theorem interiorEdges_image : interiorEdges (φ '' R) = ψ '' interiorEdges R := by
  ext e
  obtain ⟨e, rfl⟩ := ψ.surjective e
  simp only [ψ.injective.mem_set_image, mem_interiorEdges]
  refine ⟨fun h f hf => ?_, fun h g hg => ?_⟩
  · simpa [φ.injective.mem_set_image] using h (φ f) ((hψ e f).2 hf)
  · obtain ⟨g, rfl⟩ := φ.surjective g
    exact Set.mem_image_of_mem φ (h g ((hψ e g).1 hg))

include hψ in
private theorem boundaryEdges_image : boundaryEdges (φ '' R) = ψ '' boundaryEdges R := by
  ext e
  obtain ⟨e, rfl⟩ := ψ.surjective e
  simp only [ψ.injective.mem_set_image, mem_boundaryEdges, regionEdges_image φ ψ hψ]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨g, hg, he⟩
    obtain ⟨g, rfl⟩ := φ.surjective g
    exact ⟨g, fun h => hg (Set.mem_image_of_mem φ h), (hψ e g).1 he⟩
  · rintro ⟨f, hf, he⟩
    exact ⟨φ f, by simpa [φ.injective.mem_set_image] using hf, (hψ e f).2 he⟩

include hχ in
private theorem mem_endpoints_image (E : Set TriEdge) :
    (∃ e ∈ ψ '' E, χ u ∈ e.endpoints) ↔ ∃ e ∈ E, u ∈ e.endpoints := by
  rw [Set.exists_mem_image]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  rw [hχ, Sym2.mem_map]
  exact ⟨fun ⟨u', hu', h⟩ => χ.injective h ▸ hu', fun h => ⟨u, h, rfl⟩⟩

include hψ hχ in
private theorem boundaryVertices_image : boundaryVertices (φ '' R) = χ '' boundaryVertices R := by
  ext u
  obtain ⟨u, rfl⟩ := χ.surjective u
  simp only [χ.injective.mem_set_image, mem_boundaryVertices, boundaryEdges_image φ ψ hψ]
  exact mem_endpoints_image ψ χ hχ _

include hψ hχ in
private theorem regionGraph_adj_image :
    (regionGraph (φ '' R)).Adj (χ u) (χ u') ↔ (regionGraph R).Adj u u' := by
  simp only [regionGraph_adj, regionEdges_image φ ψ hψ, Set.exists_mem_image, hχ]
  simp [← Sym2.map_mk, Sym2.map.injective χ.injective |>.eq_iff]

include hψ hχ in
private theorem boundaryGraph_adj_image {p p' : boundaryVertices R}
    {q q' : boundaryVertices (φ '' R)} (hq : q.val = χ p.val) (hq' : q'.val = χ p'.val) :
    (boundaryGraph (φ '' R)).Adj q q' ↔ (boundaryGraph R).Adj p p' := by
  simp only [boundaryGraph_adj, boundaryEdges_image φ ψ hψ, Set.exists_mem_image, hχ, hq, hq']
  simp [← Sym2.map_mk, Sym2.map.injective χ.injective |>.eq_iff]

include hφ in
private theorem regionVertices_image : regionVertices (φ '' R) = χ '' regionVertices R := by
  ext u
  obtain ⟨u, rfl⟩ := χ.surjective u
  rw [χ.injective.mem_set_image]
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, hu⟩
    exact ⟨f, hf, (hφ f u).1 hu⟩
  · rintro ⟨f, hf, hu⟩
    exact ⟨φ f, Set.mem_image_of_mem φ hf, (hφ f u).2 hu⟩

include hφ in
private theorem facesOf_image (V : Set (ℤ × ℤ)) : facesOf (χ '' V) = φ '' facesOf V := by
  ext f
  obtain ⟨f, rfl⟩ := φ.surjective f
  simp only [φ.injective.mem_set_image, mem_facesOf]
  refine ⟨fun h u hu => ?_, fun h u hu => ?_⟩
  · simpa [χ.injective.mem_set_image] using h (χ u) ((hφ f u).2 hu)
  · obtain ⟨u, rfl⟩ := χ.surjective u
    exact Set.mem_image_of_mem χ (h u ((hφ f u).1 hu))

include hψ hχ hφ in
private theorem isConnectedRegion_image : IsConnectedRegion (φ '' R) ↔ IsConnectedRegion R := by
  let iso : regionGraph R ≃g regionGraph (φ '' R) := ⟨χ, regionGraph_adj_image φ ψ χ hψ hχ⟩
  simp only [IsConnectedRegion, regionVertices_image φ χ hφ, Set.forall_mem_image]
  exact forall₂_congr fun u _ => forall₂_congr fun u' _ => iso.reachable_iff

include hφ in
private theorem regionUnion_image (L : (ℝ × ℝ) →ᵃ[ℝ] ℝ × ℝ)
    (hL : ∀ u : ℤ × ℤ, L ((u.1 : ℝ), (u.2 : ℝ)) = (((χ u).1 : ℝ), ((χ u).2 : ℝ))) :
    regionUnion (φ '' R) = L '' regionUnion R := by
  have hv (f : TriFace) : ((φ f).vertices : Set (ℤ × ℤ)) = χ '' f.vertices := by
    ext u
    obtain ⟨u, rfl⟩ := χ.surjective u
    simp [hφ]
  simp only [regionUnion_def, Set.biUnion_image, Set.image_iUnion₂, AffineMap.image_convexHull,
    hv, Set.image_image, hL]

end Transfer

section Translation

variable (w : ℤ × ℤ)

private theorem endpoints_toPerm (e : TriEdge) :
    ((AddAction.toPerm w : Equiv.Perm TriEdge) e).endpoints =
      e.endpoints.map (AddAction.toPerm w : Equiv.Perm (ℤ × ℤ)) := by
  simp [vadd_eq_add]

private theorem vadd_mem_vertices_vadd (f : TriFace) (u : ℤ × ℤ) :
    (AddAction.toPerm w : Equiv.Perm (ℤ × ℤ)) u ∈
      ((AddAction.toPerm w : Equiv.Perm TriFace) f).vertices ↔ u ∈ f.vertices := by
  simp

@[simp] theorem regionEdges_vadd (R : Set TriFace) : regionEdges (w +ᵥ R) = w +ᵥ regionEdges R :=
  regionEdges_image (AddAction.toPerm w) (AddAction.toPerm w)
    fun _ _ => TriEdge.vadd_mem_edges_vadd

@[simp] theorem interiorEdges_vadd (R : Set TriFace) :
    interiorEdges (w +ᵥ R) = w +ᵥ interiorEdges R :=
  interiorEdges_image (AddAction.toPerm w) (AddAction.toPerm w)
    fun _ _ => TriEdge.vadd_mem_edges_vadd

@[simp] theorem boundaryEdges_vadd (R : Set TriFace) :
    boundaryEdges (w +ᵥ R) = w +ᵥ boundaryEdges R :=
  boundaryEdges_image (AddAction.toPerm w) (AddAction.toPerm w)
    fun _ _ => TriEdge.vadd_mem_edges_vadd

@[simp] theorem regionVertices_vadd (R : Set TriFace) :
    regionVertices (w +ᵥ R) = w +ᵥ regionVertices R :=
  regionVertices_image (AddAction.toPerm w) (AddAction.toPerm w)
    (vadd_mem_vertices_vadd w)

@[simp] theorem boundaryVertices_vadd (R : Set TriFace) :
    boundaryVertices (w +ᵥ R) = w +ᵥ boundaryVertices R :=
  boundaryVertices_image (AddAction.toPerm w) (AddAction.toPerm w) (AddAction.toPerm w)
    (fun _ _ => TriEdge.vadd_mem_edges_vadd) (endpoints_toPerm w)

@[simp] theorem isConnectedRegion_vadd_iff (R : Set TriFace) :
    IsConnectedRegion (w +ᵥ R) ↔ IsConnectedRegion R :=
  isConnectedRegion_image (AddAction.toPerm w) (AddAction.toPerm w) (AddAction.toPerm w)
    (fun _ _ => TriEdge.vadd_mem_edges_vadd) (endpoints_toPerm w)
    (vadd_mem_vertices_vadd w)

@[simp] theorem regionGraph_adj_vadd (R : Set TriFace) :
    (regionGraph (w +ᵥ R)).Adj (w + u) (w + u') ↔ (regionGraph R).Adj u u' :=
  regionGraph_adj_image (AddAction.toPerm w) (AddAction.toPerm w) (AddAction.toPerm w)
    (fun _ _ => TriEdge.vadd_mem_edges_vadd) (endpoints_toPerm w)

theorem boundaryGraph_adj_vadd {R : Set TriFace} {p p' : boundaryVertices R}
    {q q' : boundaryVertices (w +ᵥ R)} (hq : q.val = w + p.val) (hq' : q'.val = w + p'.val) :
    (boundaryGraph (w +ᵥ R)).Adj q q' ↔ (boundaryGraph R).Adj p p' :=
  boundaryGraph_adj_image (AddAction.toPerm w) (AddAction.toPerm w) (AddAction.toPerm w)
    (fun _ _ => TriEdge.vadd_mem_edges_vadd) (endpoints_toPerm w) hq hq'

@[simp] theorem facesOf_vadd (V : Set (ℤ × ℤ)) : facesOf (w +ᵥ V) = w +ᵥ facesOf V :=
  facesOf_image (AddAction.toPerm w) (AddAction.toPerm w) (vadd_mem_vertices_vadd w) V

/-- Translating a region by `w` translates `F(R)` by `w ∈ ℤ² ⊆ ℝ²`. -/
@[simp] theorem regionUnion_vadd (R : Set TriFace) :
    regionUnion (w +ᵥ R) = ((w.1 : ℝ), (w.2 : ℝ)) +ᵥ regionUnion R := by
  refine (regionUnion_image (AddAction.toPerm w) (AddAction.toPerm w) (vadd_mem_vertices_vadd w)
    (AffineEquiv.constVAdd ℝ (ℝ × ℝ) ((w.1 : ℝ), (w.2 : ℝ))).toAffineMap
    (fun u => by simp [vadd_eq_add])).trans ?_
  rw [← Set.image_vadd]
  exact congrArg (· '' _) (funext fun p => by simp)

end Translation

section Rotation

private theorem latticeRot_mem_vertices_rot (f : TriFace) (u : ℤ × ℤ) :
    latticeRot.toEquiv u ∈ (TriFace.rot f).vertices ↔ u ∈ f.vertices := by
  rw [TriFace.vertices_rot, Finset.mem_map]
  exact ⟨fun ⟨u', hu', h⟩ => latticeRot.injective h ▸ hu', fun h => ⟨u, h, rfl⟩⟩

@[simp] theorem regionEdges_rot (R : Set TriFace) :
    regionEdges (TriFace.rot '' R) = TriEdge.rot '' regionEdges R :=
  regionEdges_image _ _ (fun _ _ => TriEdge.rot_mem_edges_rot)

@[simp] theorem interiorEdges_rot (R : Set TriFace) :
    interiorEdges (TriFace.rot '' R) = TriEdge.rot '' interiorEdges R :=
  interiorEdges_image _ _ (fun _ _ => TriEdge.rot_mem_edges_rot)

@[simp] theorem boundaryEdges_rot (R : Set TriFace) :
    boundaryEdges (TriFace.rot '' R) = TriEdge.rot '' boundaryEdges R :=
  boundaryEdges_image _ _ (fun _ _ => TriEdge.rot_mem_edges_rot)

@[simp] theorem regionVertices_rot (R : Set TriFace) :
    regionVertices (TriFace.rot '' R) = latticeRot '' regionVertices R :=
  regionVertices_image (χ := latticeRot.toEquiv) _ latticeRot_mem_vertices_rot

@[simp] theorem boundaryVertices_rot (R : Set TriFace) :
    boundaryVertices (TriFace.rot '' R) = latticeRot '' boundaryVertices R :=
  boundaryVertices_image (χ := latticeRot.toEquiv) _ _
    (fun _ _ => TriEdge.rot_mem_edges_rot) TriEdge.endpoints_rot

theorem regionGraph_adj_rot (R : Set TriFace) :
    (regionGraph (TriFace.rot '' R)).Adj (latticeRot u) (latticeRot u') ↔
      (regionGraph R).Adj u u' :=
  regionGraph_adj_image (χ := latticeRot.toEquiv) _ _
    (fun _ _ => TriEdge.rot_mem_edges_rot) TriEdge.endpoints_rot

theorem boundaryGraph_adj_rot {R : Set TriFace} {p p' : boundaryVertices R}
    {q q' : boundaryVertices (TriFace.rot '' R)} (hq : q.val = latticeRot p.val)
    (hq' : q'.val = latticeRot p'.val) :
    (boundaryGraph (TriFace.rot '' R)).Adj q q' ↔ (boundaryGraph R).Adj p p' :=
  boundaryGraph_adj_image (χ := latticeRot.toEquiv) _ _
    (fun _ _ => TriEdge.rot_mem_edges_rot) TriEdge.endpoints_rot
    hq hq'

@[simp] theorem isConnectedRegion_rot_iff (R : Set TriFace) :
    IsConnectedRegion (TriFace.rot '' R) ↔ IsConnectedRegion R :=
  isConnectedRegion_image (χ := latticeRot.toEquiv) _ _
    (fun _ _ => TriEdge.rot_mem_edges_rot) TriEdge.endpoints_rot
    latticeRot_mem_vertices_rot

theorem facesOf_rot (V : Set (ℤ × ℤ)) : facesOf (latticeRot '' V) = TriFace.rot '' facesOf V :=
  facesOf_image (χ := latticeRot.toEquiv) _ latticeRot_mem_vertices_rot V

/-- The rotation `ρ` acts on `F(R) ⊆ ℝ²` by the linear map `(x, y) ↦ (-y, x - y)` extending
`latticeRot`. -/
@[simp] theorem regionUnion_rot (R : Set TriFace) :
    regionUnion (TriFace.rot '' R) = (fun p : ℝ × ℝ => (-p.2, p.1 - p.2)) '' regionUnion R :=
  (regionUnion_image (χ := latticeRot.toEquiv) _ latticeRot_mem_vertices_rot
    ((-LinearMap.snd ℝ ℝ ℝ).prod (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ)).toAffineMap
    (fun u => by simp)).trans (congrArg (· '' _) (funext fun p => by simp))

end Rotation

end TauCeti
