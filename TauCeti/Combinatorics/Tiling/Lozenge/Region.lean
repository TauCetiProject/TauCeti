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

* `TauCeti.TriEdge.endpoints`: the unordered pair of endpoints of an edge.
* `TauCeti.regionVertices`, `TauCeti.regionEdges`: the vertices `V(R)` and edges `E(R)` of the
  faces of a region.
* `TauCeti.interiorEdges`, `TauCeti.boundaryEdges`: the edges with both faces in `R`, and the edges
  of `R` lying in a face outside `R`.
* `TauCeti.boundaryVertices`: the endpoints `∂R` of the boundary edges.
* `TauCeti.regionGraph`, `TauCeti.boundaryGraph`: the graphs on `ℤ × ℤ` whose edges are the edges
  and the boundary edges of `R`.
* `TauCeti.IsConnectedRegion`: any two vertices of `R` are joined in `regionGraph R`.
* `TauCeti.regionUnion`: the union `F(R) ⊆ ℝ²` of the closed triangles of the faces of `R`.
* `TauCeti.facesOf`: the faces with all three vertices in a set `V`.

## Main statements

* `TauCeti.regionVertices_eq`: the vertices of `R` are the endpoints of its edges.
* `TauCeti.regionGraph_adj`, `TauCeti.boundaryGraph_adj`: the edges of the two graphs.
* `TauCeti.three_mul_card_eq`: for a finite region, `3 |R| = 2 |E°(R)| + |E∂(R)|`.
* `TauCeti.notMem_boundaryVertices_iff`: a vertex of `R` is not a boundary vertex exactly when
  all six faces at it lie in `R`.
* `TauCeti.regionEdges_vadd`, `TauCeti.regionEdges_rot` and their analogues: translations and the
  rotation `ρ` act compatibly with the constructions (for `F(R)`, `TauCeti.regionUnion_vadd`
  covers translations).
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

namespace TriEdge

/-- The unordered pair `s(v, v + e_k)` of endpoints of an edge. -/
def endpoints (e : TriEdge) : Sym2 (ℤ × ℤ) := s(e.v, e.target)

theorem endpoints_def (e : TriEdge) : e.endpoints = s(e.v, e.target) := (rfl)

@[simp] theorem mem_endpoints {e : TriEdge} {u : ℤ × ℤ} :
    u ∈ e.endpoints ↔ u = e.v ∨ u = e.target := Sym2.mem_iff

theorem v_ne_target (e : TriEdge) : e.v ≠ e.target := by
  obtain ⟨⟨x, y⟩, k⟩ := e
  fin_cases k <;> simp [Prod.ext_iff]

theorem not_isDiag_endpoints (e : TriEdge) : ¬e.endpoints.IsDiag :=
  Sym2.mk_isDiag_iff.not.2 e.v_ne_target

@[simp] theorem endpoints_vadd (w : ℤ × ℤ) (e : TriEdge) :
    (w +ᵥ e).endpoints = e.endpoints.map (w + ·) := by
  simp [endpoints]

@[simp] theorem endpoints_rot (e : TriEdge) : (rot e).endpoints = e.endpoints.map latticeRot := by
  simp only [endpoints, rot_v, target_rot, Sym2.map_mk]
  split_ifs
  · rfl
  · exact Sym2.eq_swap

/-- An edge is determined by its endpoints. -/
theorem endpoints_injective : Function.Injective endpoints := by
  rintro ⟨⟨x, y⟩, k⟩ ⟨⟨x', y'⟩, k'⟩ h
  fin_cases k <;> fin_cases k' <;> simp [endpoints, TriEdge.ext_iff] at h ⊢ <;>
    omega

end TriEdge

namespace TriFace

/-- Two distinct vertices of a face are the endpoints of an edge of the face. -/
theorem exists_mem_edges_endpoints_eq {f : TriFace} {u u' : ℤ × ℤ} (hu : u ∈ f.vertices)
    (hu' : u' ∈ f.vertices) (h : u ≠ u') : ∃ e ∈ f.edges, e.endpoints = s(u, u') := by
  obtain ⟨⟨a, b⟩, c⟩ := f
  cases c <;> simp only [vertices_mk_true, vertices_mk_false, Finset.mem_insert,
    Finset.mem_singleton] at hu hu' <;>
    rcases hu with rfl | rfl | rfl <;> rcases hu' with rfl | rfl | rfl <;>
    first
    | exact absurd rfl h
    | simp [TriEdge.endpoints, Prod.ext_iff]

/-- The endpoints of an edge of a face are vertices of the face. -/
theorem mem_vertices_of_mem_endpoints {f : TriFace} {e : TriEdge} {u : ℤ × ℤ}
    (he : e ∈ f.edges) (hu : u ∈ e.endpoints) : u ∈ f.vertices := by
  rcases TriEdge.mem_endpoints.1 hu with rfl | rfl
  exacts [v_mem_vertices_of_mem_edges he, target_mem_vertices_of_mem_edges he]

end TriFace

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

/-- The boundary edges `E∂(R)` of a region: its edges lying in a face outside `R`, so that exactly
one of their two faces is in `R`. -/
def boundaryEdges (R : Set TriFace) : Set TriEdge :=
  {e | e ∈ regionEdges R ∧ ∃ f ∉ R, e ∈ f.edges}

/-- The boundary vertices `∂R` of a region: the endpoints of its boundary edges. -/
def boundaryVertices (R : Set TriFace) : Set (ℤ × ℤ) :=
  {u | ∃ e ∈ boundaryEdges R, u ∈ e.endpoints}

/-- The edge graph of a region: the simple graph on `ℤ × ℤ` whose edges are the segments of the
edges of `R`. Vertices outside `V(R)` are isolated. -/
def regionGraph (R : Set TriFace) : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.fromRel fun u u' => ∃ e ∈ regionEdges R, e.v = u ∧ e.target = u'

/-- The boundary graph of a region: the simple graph on `ℤ × ℤ` whose edges are the segments of the
boundary edges of `R`. Vertices outside `∂R` are isolated. -/
def boundaryGraph (R : Set TriFace) : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.fromRel fun u u' => ∃ e ∈ boundaryEdges R, e.v = u ∧ e.target = u'

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

theorem mem_boundaryEdges : e ∈ boundaryEdges R ↔ e ∈ regionEdges R ∧ ∃ f ∉ R, e ∈ f.edges :=
  Iff.rfl

theorem mem_boundaryVertices : u ∈ boundaryVertices R ↔ ∃ e ∈ boundaryEdges R, u ∈ e.endpoints :=
  Iff.rfl

theorem mem_facesOf {V : Set (ℤ × ℤ)} : f ∈ facesOf V ↔ ∀ u ∈ f.vertices, u ∈ V := Iff.rfl

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

theorem interiorEdges_mono (h : R ⊆ S) : interiorEdges R ⊆ interiorEdges S :=
  fun _ he f hf => h (he f hf)

/-- The vertices of a region are the endpoints of its edges. -/
theorem regionVertices_eq (R : Set TriFace) :
    regionVertices R = {u | ∃ e ∈ regionEdges R, u ∈ e.endpoints} := by
  ext u
  constructor
  · rintro ⟨f, hf, hu⟩
    obtain ⟨u', hu', hne⟩ : ∃ u' ∈ f.vertices, u ≠ u' := by
      by_contra! h
      have := Finset.card_le_one.2 fun a ha b hb => (h a ha).symm.trans (h b hb)
      simp at this
    obtain ⟨e, he, hee⟩ := TriFace.exists_mem_edges_endpoints_eq hu hu' hne
    exact ⟨e, ⟨f, hf, he⟩, hee ▸ Sym2.mem_mk_left u u'⟩
  · rintro ⟨e, ⟨f, hf, he⟩, hu⟩
    exact ⟨f, hf, TriFace.mem_vertices_of_mem_endpoints he hu⟩

theorem boundaryVertices_subset_regionVertices : boundaryVertices R ⊆ regionVertices R := by
  rw [regionVertices_eq]
  exact fun _ ⟨e, he, hu⟩ => ⟨e, he.1, hu⟩

private theorem fromRel_edges_adj (E : Set TriEdge) :
    (SimpleGraph.fromRel fun u u' => ∃ e ∈ E, e.v = u ∧ e.target = u').Adj u u' ↔
      ∃ e ∈ E, e.endpoints = s(u, u') := by
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨e, he, rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩⟩
    exacts [⟨e, he, rfl⟩, ⟨e, he, Sym2.eq_swap⟩]
  · rintro ⟨e, he, h⟩
    refine ⟨fun huu => e.not_isDiag_endpoints (h ▸ huu ▸ Sym2.mk_isDiag_iff.2 rfl), ?_⟩
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [Or.inl ⟨e, he, rfl, rfl⟩, Or.inr ⟨e, he, rfl, rfl⟩]

/-- The edges of `regionGraph R` are the endpoint pairs of the edges of `R`. -/
theorem regionGraph_adj : (regionGraph R).Adj u u' ↔ ∃ e ∈ regionEdges R, e.endpoints = s(u, u') :=
  fromRel_edges_adj _

/-- The edges of `boundaryGraph R` are the endpoint pairs of the boundary edges of `R`. -/
theorem boundaryGraph_adj :
    (boundaryGraph R).Adj u u' ↔ ∃ e ∈ boundaryEdges R, e.endpoints = s(u, u') :=
  fromRel_edges_adj _

theorem regionGraph_edgeSet (R : Set TriFace) :
    (regionGraph R).edgeSet = TriEdge.endpoints '' regionEdges R := by
  ext ⟨u, u'⟩
  simp [regionGraph_adj]

theorem boundaryGraph_edgeSet (R : Set TriFace) :
    (boundaryGraph R).edgeSet = TriEdge.endpoints '' boundaryEdges R := by
  ext ⟨u, u'⟩
  simp [boundaryGraph_adj]

theorem boundaryGraph_le_regionGraph (R : Set TriFace) : boundaryGraph R ≤ regionGraph R :=
  fun _ _ h => by
    obtain ⟨e, he, h⟩ := boundaryGraph_adj.1 h
    exact regionGraph_adj.2 ⟨e, he.1, h⟩

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

/-- The non-isolated vertices of `boundaryGraph R` are the boundary vertices of `R`. -/
theorem boundaryGraph_support (R : Set TriFace) :
    (boundaryGraph R).support = boundaryVertices R := by
  ext u
  rw [SimpleGraph.mem_support]
  simp only [boundaryGraph_adj]
  exact exists_adj_iff _

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
theorem three_mul_card_eq (R : Finset TriFace) :
    3 * R.card =
      2 * (interiorEdges (R : Set TriFace)).ncard + (boundaryEdges (R : Set TriFace)).ncard := by
  set T := R.biUnion TriFace.edges
  have hT : ∀ e, e ∈ T ↔ e ∈ regionEdges (R : Set TriFace) := by simp [T, mem_regionEdges]
  have hint : interiorEdges (R : Set TriFace) =
      ↑(T.filter fun e => e.whiteFace ∈ R ∧ e.blackFace ∈ R) := by
    ext e
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, hT, mem_interiorEdges_iff, Finset.mem_coe]
    exact ⟨fun h => ⟨mem_regionEdges_iff.2 (Or.inl h.1), h⟩, And.right⟩
  have hbd : boundaryEdges (R : Set TriFace) =
      ↑(T.filter fun e => ¬(e.whiteFace ∈ R ∧ e.blackFace ∈ R)) := by
    ext e
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, hT]
    constructor
    · intro h
      exact ⟨h.1, fun hp => (notMem_boundaryEdges_iff h.1).2 (mem_interiorEdges_iff.2 hp) h⟩
    · rintro ⟨h, hp⟩
      by_contra hb
      exact hp (mem_interiorEdges_iff.1 ((notMem_boundaryEdges_iff h).1 hb))
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
    rw [hT, mem_regionEdges_iff] at he
    rw [TriEdge.faces_def, Finset.filter_insert, Finset.filter_singleton]
    by_cases h₁ : e.whiteFace ∈ R <;> by_cases h₂ : e.blackFace ∈ R <;> simp_all
  rw [Finset.sum_congr rfl habove, Finset.sum_congr rfl hbelow, Finset.sum_const, smul_eq_mul,
    Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one,
    mul_comm] at hdc
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
    have h₁ := key ⟨(x, y), 2⟩ (by simp)
    have h₂ := key ⟨(x, y), 1⟩ (by simp)
    have h₃ := key ⟨(x - 1, y), 0⟩ (by simp)
    have h₄ := key ⟨(x - 1, y - 1), 2⟩ (by simp)
    have h₆ := key ⟨(x, y), 0⟩ (by simp)
    simp only [TriEdge.whiteFace_mk, TriEdge.blackFace_mk] at h₁ h₂ h₃ h₄ h₆
    norm_num [Prod.ext_iff] at h₁ h₂ h₃ h₄ h₆
    have hall : ∀ g ∈ vertexFaces (x, y), (g ∈ R ↔ (⟨(x, y), true⟩ : TriFace) ∈ R) := by
      intro g hg
      simp only [vertexFaces_def, Finset.mem_insert, Finset.mem_singleton, Prod.mk_sub_mk,
        sub_zero] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Iff.rfl
      · exact h₂.trans h₁.symm
      · exact h₄.trans (h₃.symm.trans (h₂.trans h₁.symm))
      · exact h₁.symm
      · exact h₆.symm
      · exact h₃.symm.trans (h₂.trans h₁.symm)
    obtain ⟨g, hg, hug⟩ := hu
    rw [← mem_vertexFaces] at hug
    exact fun f hf => (hall f hf).2 ((hall g hug).1 hg)
  · rintro h ⟨e, ⟨-, g, hg, he⟩, hu⟩
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
  · rintro ⟨e, ⟨⟨f, hf, he⟩, g, hg, heg⟩, hu⟩
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
private theorem boundaryGraph_adj_image :
    (boundaryGraph (φ '' R)).Adj (χ u) (χ u') ↔ (boundaryGraph R).Adj u u' := by
  simp only [boundaryGraph_adj, boundaryEdges_image φ ψ hψ, Set.exists_mem_image, hχ]
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

end Transfer

section Translation

variable (w : ℤ × ℤ)

private theorem vadd_mem_edges_vadd (e : TriEdge) (f : TriFace) :
    (AddAction.toPerm w : Equiv.Perm TriEdge) e ∈
      ((AddAction.toPerm w : Equiv.Perm TriFace) f).edges ↔ e ∈ f.edges := by
  simp

private theorem endpoints_toPerm (e : TriEdge) :
    ((AddAction.toPerm w : Equiv.Perm TriEdge) e).endpoints =
      e.endpoints.map (AddAction.toPerm w : Equiv.Perm (ℤ × ℤ)) := by
  simp [vadd_eq_add]

private theorem vadd_mem_vertices_vadd (f : TriFace) (u : ℤ × ℤ) :
    (AddAction.toPerm w : Equiv.Perm (ℤ × ℤ)) u ∈
      ((AddAction.toPerm w : Equiv.Perm TriFace) f).vertices ↔ u ∈ f.vertices := by
  simp

theorem regionEdges_vadd (R : Set TriFace) : regionEdges (w +ᵥ R) = w +ᵥ regionEdges R :=
  regionEdges_image (AddAction.toPerm w) (AddAction.toPerm w) (vadd_mem_edges_vadd w)

theorem interiorEdges_vadd (R : Set TriFace) : interiorEdges (w +ᵥ R) = w +ᵥ interiorEdges R :=
  interiorEdges_image (AddAction.toPerm w) (AddAction.toPerm w) (vadd_mem_edges_vadd w)

theorem boundaryEdges_vadd (R : Set TriFace) : boundaryEdges (w +ᵥ R) = w +ᵥ boundaryEdges R :=
  boundaryEdges_image (AddAction.toPerm w) (AddAction.toPerm w) (vadd_mem_edges_vadd w)

theorem regionVertices_vadd (R : Set TriFace) :
    regionVertices (w +ᵥ R) = w +ᵥ regionVertices R :=
  regionVertices_image (AddAction.toPerm w) (AddAction.toPerm w)
    (vadd_mem_vertices_vadd w)

theorem boundaryVertices_vadd (R : Set TriFace) :
    boundaryVertices (w +ᵥ R) = w +ᵥ boundaryVertices R :=
  boundaryVertices_image (AddAction.toPerm w) (AddAction.toPerm w) (AddAction.toPerm w)
    (vadd_mem_edges_vadd w) (endpoints_toPerm w)

theorem regionGraph_adj_vadd (R : Set TriFace) :
    (regionGraph (w +ᵥ R)).Adj (w + u) (w + u') ↔ (regionGraph R).Adj u u' :=
  regionGraph_adj_image (AddAction.toPerm w) (AddAction.toPerm w) (AddAction.toPerm w)
    (vadd_mem_edges_vadd w) (endpoints_toPerm w)

theorem boundaryGraph_adj_vadd (R : Set TriFace) :
    (boundaryGraph (w +ᵥ R)).Adj (w + u) (w + u') ↔ (boundaryGraph R).Adj u u' :=
  boundaryGraph_adj_image (AddAction.toPerm w) (AddAction.toPerm w) (AddAction.toPerm w)
    (vadd_mem_edges_vadd w) (endpoints_toPerm w)

theorem facesOf_vadd (V : Set (ℤ × ℤ)) : facesOf (w +ᵥ V) = w +ᵥ facesOf V :=
  facesOf_image (AddAction.toPerm w) (AddAction.toPerm w) (vadd_mem_vertices_vadd w) V

/-- Translating a region by `w` translates `F(R)` by `w ∈ ℤ² ⊆ ℝ²`. -/
theorem regionUnion_vadd (R : Set TriFace) :
    regionUnion (w +ᵥ R) = ((w.1 : ℝ), (w.2 : ℝ)) +ᵥ regionUnion R := by
  rw [regionUnion_def, regionUnion_def, ← Set.image_vadd, Set.biUnion_image, Set.vadd_set_iUnion₂]
  refine Set.iUnion₂_congr fun f _ => ?_
  rw [← convexHull_vadd, TriFace.vertices_vadd, Finset.coe_vadd_finset, ← Set.image_vadd,
    Set.image_image, ← Set.image_vadd, Set.image_image]
  congr 2
  funext u
  simp [vadd_eq_add]

end Translation

section Rotation

private theorem rot_mem_edges_rot' (e : TriEdge) (f : TriFace) :
    TriEdge.rot e ∈ (TriFace.rot f).edges ↔ e ∈ f.edges :=
  TriEdge.rot_mem_edges_rot

private theorem latticeRot_mem_vertices_rot (f : TriFace) (u : ℤ × ℤ) :
    latticeRot.toEquiv u ∈ (TriFace.rot f).vertices ↔ u ∈ f.vertices := by
  rw [TriFace.vertices_rot, Finset.mem_map]
  exact ⟨fun ⟨u', hu', h⟩ => latticeRot.injective h ▸ hu', fun h => ⟨u, h, rfl⟩⟩

theorem regionEdges_rot (R : Set TriFace) :
    regionEdges (TriFace.rot '' R) = TriEdge.rot '' regionEdges R :=
  regionEdges_image _ _ rot_mem_edges_rot'

theorem interiorEdges_rot (R : Set TriFace) :
    interiorEdges (TriFace.rot '' R) = TriEdge.rot '' interiorEdges R :=
  interiorEdges_image _ _ rot_mem_edges_rot'

theorem boundaryEdges_rot (R : Set TriFace) :
    boundaryEdges (TriFace.rot '' R) = TriEdge.rot '' boundaryEdges R :=
  boundaryEdges_image _ _ rot_mem_edges_rot'

theorem regionVertices_rot (R : Set TriFace) :
    regionVertices (TriFace.rot '' R) = latticeRot '' regionVertices R :=
  regionVertices_image (χ := latticeRot.toEquiv) _ latticeRot_mem_vertices_rot

theorem boundaryVertices_rot (R : Set TriFace) :
    boundaryVertices (TriFace.rot '' R) = latticeRot '' boundaryVertices R :=
  boundaryVertices_image (χ := latticeRot.toEquiv) _ _ rot_mem_edges_rot' TriEdge.endpoints_rot

theorem regionGraph_adj_rot (R : Set TriFace) :
    (regionGraph (TriFace.rot '' R)).Adj (latticeRot u) (latticeRot u') ↔
      (regionGraph R).Adj u u' :=
  regionGraph_adj_image (χ := latticeRot.toEquiv) _ _ rot_mem_edges_rot' TriEdge.endpoints_rot

theorem boundaryGraph_adj_rot (R : Set TriFace) :
    (boundaryGraph (TriFace.rot '' R)).Adj (latticeRot u) (latticeRot u') ↔
      (boundaryGraph R).Adj u u' :=
  boundaryGraph_adj_image (χ := latticeRot.toEquiv) _ _ rot_mem_edges_rot' TriEdge.endpoints_rot

theorem facesOf_rot (V : Set (ℤ × ℤ)) : facesOf (latticeRot '' V) = TriFace.rot '' facesOf V :=
  facesOf_image (χ := latticeRot.toEquiv) _ latticeRot_mem_vertices_rot V

end Rotation

end TauCeti
