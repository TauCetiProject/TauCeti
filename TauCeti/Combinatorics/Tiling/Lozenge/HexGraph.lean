/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Lattice
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
import Mathlib.Data.Int.Interval

/-!
# The dual hexagonal graph of the triangular lattice

The dual graph of the triangular lattice has the faces of the lattice as vertices, two faces being
adjacent when they are distinct and share an edge. It is the hexagonal (honeycomb) lattice, and a
lozenge tiling of a region of the triangular lattice is a perfect matching of the subgraph of this
graph induced by the region: a lozenge is the union of the two faces of an edge.

The graph is defined as `hexGraph`, `SimpleGraph.fromRel` of the relation "some edge lies in both
faces". Its edges are in bijection with the edges of the triangular lattice, an edge `e`
corresponding to the pair of its white and its black face.

## Main definitions

* `TauCeti.hexGraph`: the dual hexagonal graph on `TriFace`.
* `TauCeti.TriEdge.dualEdge`: the edge of `hexGraph` crossing an edge of the lattice.
* `TauCeti.TriEdge.equivHexGraphEdgeSet`: the bijection from the edges of the lattice onto the
  edge set of `hexGraph`.
* `TauCeti.hexGraphTranslation`, `TauCeti.hexGraphRot`: translations and the rotation `ρ` as
  automorphisms of `hexGraph`.
* `TauCeti.vertexCycle`: the six faces at a vertex, as a closed walk of `hexGraph`.

## Main statements

* `TauCeti.hexGraph_neighborFinset_mk_true`, `TauCeti.hexGraph_neighborFinset_mk_false`: the
  three neighbours of a white and of a black face.
* `TauCeti.hexGraph_isRegularOfDegree`: `hexGraph` is `3`-regular.
* `TauCeti.hexGraph_isBipartiteWith`: `hexGraph` is bipartite, with the white and the black faces
  as parts.
* `TauCeti.existsUnique_mem_edges_of_hexGraph_adj`: adjacent faces share a unique edge.
* `TauCeti.TriEdge.equivHexGraphEdgeSet_vadd`, `TauCeti.TriEdge.equivHexGraphEdgeSet_rot`: the
  bijection between the edges of the lattice and of `hexGraph` commutes with translations and `ρ`.
* `TauCeti.vertexCycle_isCycle`, `TauCeti.toFinset_support_vertexCycle`: the six faces at a vertex
  form a `6`-cycle of `hexGraph`.
* `TauCeti.hexGraph_existsUnique_infinite_supp_of_finite`: for finite `R`, exactly one component
  of the faces outside `R` is infinite.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 2.
* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009), Section 1.1.
-/

public section

open Pointwise

namespace TauCeti

/-- The dual hexagonal graph `hexGraph`: its vertices are the faces of the triangular lattice, two
faces being adjacent when they are distinct and share an edge. -/
def hexGraph : SimpleGraph TriFace :=
  SimpleGraph.fromRel fun f g => ∃ e, e ∈ f.edges ∧ e ∈ g.edges

theorem hexGraph_adj {f g : TriFace} :
    hexGraph.Adj f g ↔ f ≠ g ∧ ∃ e, e ∈ f.edges ∧ e ∈ g.edges := by
  rw [hexGraph, SimpleGraph.fromRel_adj]
  refine and_congr_right fun _ => ⟨?_, Or.inl⟩
  rintro (⟨e, h₁, h₂⟩ | ⟨e, h₁, h₂⟩)
  exacts [⟨e, h₁, h₂⟩, ⟨e, h₂, h₁⟩]

/-- Adjacent faces have opposite colours. -/
theorem isWhite_ne_of_hexGraph_adj {f g : TriFace} (h : hexGraph.Adj f g) :
    f.isWhite ≠ g.isWhite := by
  obtain ⟨hfg, e, hf, hg⟩ := hexGraph_adj.1 h
  exact TriFace.isWhite_ne_of_mem_edges hfg hf hg

/-- Adjacent faces share a unique edge. -/
theorem existsUnique_mem_edges_of_hexGraph_adj {f g : TriFace} (h : hexGraph.Adj f g) :
    ∃! e, e ∈ f.edges ∧ e ∈ g.edges := by
  obtain ⟨hfg, e, hf, hg⟩ := hexGraph_adj.1 h
  exact ⟨e, ⟨hf, hg⟩, fun e' he' =>
    TriFace.eq_of_mem_edges_of_mem_edges hfg he'.1 he'.2 hf hg⟩

namespace TriEdge

/-- The white and the black face of an edge are adjacent in `hexGraph`. -/
theorem hexGraph_adj_whiteFace_blackFace (e : TriEdge) : hexGraph.Adj e.whiteFace e.blackFace :=
  hexGraph_adj.2 ⟨e.whiteFace_ne_blackFace, e, e.mem_whiteFace_edges, e.mem_blackFace_edges⟩

/-- The edge of `hexGraph` crossing the edge `e` of the triangular lattice: the pair of its white
and its black face. -/
def dualEdge (e : TriEdge) : Sym2 TriFace := s(e.whiteFace, e.blackFace)

theorem dualEdge_def (e : TriEdge) : e.dualEdge = s(e.whiteFace, e.blackFace) := (rfl)

/-- The faces joined by the edge of `hexGraph` crossing `e` are exactly the faces containing
`e`. -/
@[simp] theorem mem_dualEdge {e : TriEdge} {f : TriFace} : f ∈ e.dualEdge ↔ e ∈ f.edges := by
  rw [dualEdge, Sym2.mem_iff, TriFace.mem_edges_iff]

theorem dualEdge_mem_edgeSet (e : TriEdge) : e.dualEdge ∈ hexGraph.edgeSet :=
  e.hexGraph_adj_whiteFace_blackFace

/-- The edge of `hexGraph` crossing `e` joins two faces exactly when they are distinct and both
contain `e`. -/
theorem dualEdge_eq_iff {e : TriEdge} {f g : TriFace} :
    e.dualEdge = s(f, g) ↔ f ≠ g ∧ e ∈ f.edges ∧ e ∈ g.edges := by
  rw [dualEdge, Sym2.eq_iff]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    exacts [⟨e.whiteFace_ne_blackFace, e.mem_whiteFace_edges, e.mem_blackFace_edges⟩,
      ⟨e.whiteFace_ne_blackFace.symm, e.mem_blackFace_edges, e.mem_whiteFace_edges⟩]
  · rintro ⟨hfg, hf, hg⟩
    rcases TriFace.mem_edges_iff.1 hf with rfl | rfl <;>
      rcases TriFace.mem_edges_iff.1 hg with rfl | rfl
    exacts [absurd rfl hfg, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, absurd rfl hfg]

theorem dualEdge_injective : Function.Injective dualEdge := fun e e' h => by
  have hw : e ∈ e'.whiteFace.edges := mem_dualEdge.1 (h ▸ mem_dualEdge.2 e'.mem_whiteFace_edges)
  have hb : e ∈ e'.blackFace.edges := mem_dualEdge.1 (h ▸ mem_dualEdge.2 e'.mem_blackFace_edges)
  exact eq_of_whiteFace_eq_of_blackFace_eq
    (eq_whiteFace_of_mem_edges hw (by simp)).symm (eq_blackFace_of_mem_edges hb (by simp)).symm

@[simp] theorem dualEdge_vadd (w : ℤ × ℤ) (e : TriEdge) :
    (w +ᵥ e).dualEdge = e.dualEdge.map (w +ᵥ ·) := by
  simp [dualEdge]

@[simp] theorem dualEdge_rot (e : TriEdge) : (rot e).dualEdge = e.dualEdge.map TriFace.rot := by
  simp [dualEdge]

end TriEdge

/-- The edges of `hexGraph` are exactly the edges crossing the edges of the triangular lattice. -/
theorem hexGraph_edgeSet : hexGraph.edgeSet = Set.range TriEdge.dualEdge := by
  ext s
  induction s using Sym2.ind with
  | _ f g =>
    rw [SimpleGraph.mem_edgeSet, hexGraph_adj, Set.mem_range]
    exact ⟨fun ⟨hfg, e, hf, hg⟩ => ⟨e, TriEdge.dualEdge_eq_iff.2 ⟨hfg, hf, hg⟩⟩,
      fun ⟨e, he⟩ => (TriEdge.dualEdge_eq_iff.1 he).imp_right fun h => ⟨e, h⟩⟩

/-- The bijection from the edges of the triangular lattice onto the edges of `hexGraph`, sending
an edge to the pair of faces containing it. -/
noncomputable def TriEdge.equivHexGraphEdgeSet : TriEdge ≃ hexGraph.edgeSet :=
  Equiv.ofBijective (fun e => ⟨e.dualEdge, e.dualEdge_mem_edgeSet⟩)
    ⟨fun _ _ h => TriEdge.dualEdge_injective (congrArg Subtype.val h), fun s => by
      have hs : (s : Sym2 TriFace) ∈ Set.range TriEdge.dualEdge := by
        rw [← hexGraph_edgeSet]
        exact s.property
      obtain ⟨e, he⟩ := hs
      exact ⟨e, Subtype.ext he⟩⟩

@[simp] theorem TriEdge.coe_equivHexGraphEdgeSet (e : TriEdge) :
    (TriEdge.equivHexGraphEdgeSet e : Sym2 TriFace) = e.dualEdge := (rfl)

/-- The inverse of `TriEdge.equivHexGraphEdgeSet` sends an edge of `hexGraph` to the edge of the
lattice shared by its two faces. -/
theorem TriEdge.equivHexGraphEdgeSet_symm_mem_edges (s : hexGraph.edgeSet) {f : TriFace}
    (hf : f ∈ (s : Sym2 TriFace)) : TriEdge.equivHexGraphEdgeSet.symm s ∈ f.edges := by
  obtain ⟨e, rfl⟩ := TriEdge.equivHexGraphEdgeSet.surjective s
  rw [Equiv.symm_apply_apply]
  rwa [TriEdge.coe_equivHexGraphEdgeSet, TriEdge.mem_dualEdge] at hf

/-! ### Neighbours and degrees -/

/-- A white face is adjacent exactly to the black faces of its edges. -/
theorem hexGraph_adj_iff_of_isWhite {f g : TriFace} (hf : f.isWhite = true) :
    hexGraph.Adj f g ↔ ∃ e ∈ f.edges, g = e.blackFace := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨-, e, hfe, hge⟩ := hexGraph_adj.1 h
    have hg : g.isWhite = false := by simpa [hf] using (isWhite_ne_of_hexGraph_adj h).symm
    exact ⟨e, hfe, TriEdge.eq_blackFace_of_mem_edges hge hg⟩
  · rintro ⟨e, he, rfl⟩
    rw [TriEdge.eq_whiteFace_of_mem_edges he hf]
    exact e.hexGraph_adj_whiteFace_blackFace

/-- A black face is adjacent exactly to the white faces of its edges. -/
theorem hexGraph_adj_iff_of_isWhite_eq_false {f g : TriFace} (hf : f.isWhite = false) :
    hexGraph.Adj f g ↔ ∃ e ∈ f.edges, g = e.whiteFace := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨-, e, hfe, hge⟩ := hexGraph_adj.1 h
    have hg : g.isWhite = true := by simpa [hf] using (isWhite_ne_of_hexGraph_adj h).symm
    exact ⟨e, hfe, TriEdge.eq_whiteFace_of_mem_edges hge hg⟩
  · rintro ⟨e, he, rfl⟩
    rw [TriEdge.eq_blackFace_of_mem_edges he hf]
    exact e.hexGraph_adj_whiteFace_blackFace.symm

/-- The neighbours of the white face `W(v)` are `B(v)`, `B(v - e₂)` and `B(v + e₁)`, across the
edges `(v, 3)`, `(v, 1)` and `(v + e₁, 2)`. -/
theorem hexGraph_neighborSet_mk_true (v : ℤ × ℤ) :
    hexGraph.neighborSet ⟨v, true⟩ = {⟨v, false⟩, ⟨v - (0, 1), false⟩, ⟨v + (1, 0), false⟩} := by
  ext g
  rw [SimpleGraph.mem_neighborSet, hexGraph_adj_iff_of_isWhite rfl]
  simp
  tauto

/-- The neighbours of the black face `B(v)` are `W(v)`, `W(v - e₁)` and `W(v + e₂)`, across the
edges `(v, 3)`, `(v, 2)` and `(v + e₂, 1)`. -/
theorem hexGraph_neighborSet_mk_false (v : ℤ × ℤ) :
    hexGraph.neighborSet ⟨v, false⟩ = {⟨v, true⟩, ⟨v - (1, 0), true⟩, ⟨v + (0, 1), true⟩} := by
  ext g
  rw [SimpleGraph.mem_neighborSet, hexGraph_adj_iff_of_isWhite_eq_false rfl]
  simp
  tauto

/-- The neighbours of a face are the other faces of its edges. -/
instance : hexGraph.LocallyFinite := fun f =>
  Fintype.ofFinset ((f.edges.biUnion TriEdge.faces).erase f) fun g => by
    rw [Finset.mem_erase, Finset.mem_biUnion, SimpleGraph.mem_neighborSet, hexGraph_adj, ne_comm]
    simp only [TriEdge.mem_faces]

/-- The neighbours of the white face `W(v)` are `B(v)`, `B(v - e₂)` and `B(v + e₁)`, as a
`Finset`. -/
theorem hexGraph_neighborFinset_mk_true (v : ℤ × ℤ) :
    hexGraph.neighborFinset ⟨v, true⟩ = {⟨v, false⟩, ⟨v - (0, 1), false⟩, ⟨v + (1, 0), false⟩} := by
  ext g
  rw [SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_neighborSet, hexGraph_neighborSet_mk_true]
  simp

/-- The neighbours of the black face `B(v)` are `W(v)`, `W(v - e₁)` and `W(v + e₂)`, as a
`Finset`. -/
theorem hexGraph_neighborFinset_mk_false (v : ℤ × ℤ) :
    hexGraph.neighborFinset ⟨v, false⟩ = {⟨v, true⟩, ⟨v - (1, 0), true⟩, ⟨v + (0, 1), true⟩} := by
  ext g
  rw [SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_neighborSet,
    hexGraph_neighborSet_mk_false]
  simp

@[simp] theorem hexGraph_degree (f : TriFace) : hexGraph.degree f = 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  obtain ⟨⟨x, y⟩, c⟩ := f
  cases c
  · rw [hexGraph_neighborFinset_mk_false, Finset.card_eq_three]
    exact ⟨_, _, _, by simp; omega, by simp, by simp, rfl⟩
  · rw [hexGraph_neighborFinset_mk_true, Finset.card_eq_three]
    exact ⟨_, _, _, by simp; omega, by simp, by simp, rfl⟩

/-- `hexGraph` is `3`-regular. -/
theorem hexGraph_isRegularOfDegree : hexGraph.IsRegularOfDegree 3 :=
  hexGraph_degree

/-- `hexGraph` is bipartite, with the white and the black faces as parts. -/
theorem hexGraph_isBipartiteWith :
    hexGraph.IsBipartiteWith {f | f.isWhite = true} {f | f.isWhite = false} where
  disjoint := Set.disjoint_left.2 fun f h₁ h₂ => by simp_all
  mem_of_adj f g h := by
    have := isWhite_ne_of_hexGraph_adj h
    cases hf : f.isWhite <;> cases hg : g.isWhite <;> simp_all

theorem hexGraph_isBipartite : hexGraph.IsBipartite :=
  hexGraph_isBipartiteWith.isBipartite

/-! ### Symmetries -/

/-- A permutation of the faces that carries the edges of each face onto the edges of its image,
along a permutation of the edges, preserves adjacency in `hexGraph`. -/
private theorem hexGraph_adj_apply_iff (σ : Equiv.Perm TriFace) (τ : Equiv.Perm TriEdge)
    (h : ∀ f e, τ e ∈ (σ f).edges ↔ e ∈ f.edges) {f g : TriFace} :
    hexGraph.Adj (σ f) (σ g) ↔ hexGraph.Adj f g := by
  rw [hexGraph_adj, hexGraph_adj, σ.injective.ne_iff]
  refine and_congr_right fun _ => ⟨fun ⟨e, hf, hg⟩ => ⟨τ.symm e, ?_, ?_⟩,
    fun ⟨e, hf, hg⟩ => ⟨τ e, (h f e).2 hf, (h g e).2 hg⟩⟩
  · rwa [← h, Equiv.apply_symm_apply]
  · rwa [← h, Equiv.apply_symm_apply]

@[simp] theorem hexGraph_adj_vadd_iff (w : ℤ × ℤ) {f g : TriFace} :
    hexGraph.Adj (w +ᵥ f) (w +ᵥ g) ↔ hexGraph.Adj f g :=
  hexGraph_adj_apply_iff (AddAction.toPerm w) (AddAction.toPerm w) fun f e => by
    simp only [AddAction.toPerm_apply, TriFace.edges_vadd, Finset.vadd_mem_vadd_finset_iff]

@[simp] theorem hexGraph_adj_rot_iff {f g : TriFace} :
    hexGraph.Adj (TriFace.rot f) (TriFace.rot g) ↔ hexGraph.Adj f g :=
  hexGraph_adj_apply_iff _ TriEdge.rot fun _ _ => TriEdge.rot_mem_edges_rot

/-- The translations of `ℤ²` act on `hexGraph` by graph automorphisms. The group `ℤ × ℤ` is
written multiplicatively, as the automorphisms `hexGraph ≃g hexGraph` form a multiplicative
group. -/
def hexGraphTranslation : Multiplicative (ℤ × ℤ) →* (hexGraph ≃g hexGraph) where
  toFun w := ⟨AddAction.toPerm w.toAdd, hexGraph_adj_vadd_iff w.toAdd⟩
  map_one' := RelIso.ext fun f => zero_vadd (ℤ × ℤ) f
  map_mul' w w' := RelIso.ext fun f => add_vadd w.toAdd w'.toAdd f

@[simp] theorem hexGraphTranslation_apply (w : Multiplicative (ℤ × ℤ)) (f : TriFace) :
    hexGraphTranslation w f = w.toAdd +ᵥ f := (rfl)

@[simp] theorem hexGraphTranslation_symm_apply (w : Multiplicative (ℤ × ℤ)) (f : TriFace) :
    (hexGraphTranslation w).symm f = -w.toAdd +ᵥ f := (rfl)

/-- The rotation `ρ` acts on `hexGraph` by a graph automorphism. -/
def hexGraphRot : hexGraph ≃g hexGraph :=
  ⟨TriFace.rot, hexGraph_adj_rot_iff⟩

@[simp] theorem hexGraphRot_apply (f : TriFace) : hexGraphRot f = TriFace.rot f := (rfl)

@[simp] theorem hexGraphRot_symm_apply (f : TriFace) :
    hexGraphRot.symm f = TriFace.rot.symm f := (rfl)

/-- The bijection `TriEdge.equivHexGraphEdgeSet` commutes with translations. -/
@[simp] theorem TriEdge.equivHexGraphEdgeSet_vadd (w : ℤ × ℤ) (e : TriEdge) :
    TriEdge.equivHexGraphEdgeSet (w +ᵥ e) =
      (hexGraphTranslation (.ofAdd w)).mapEdgeSet (TriEdge.equivHexGraphEdgeSet e) :=
  Subtype.ext (TriEdge.dualEdge_vadd w e)

/-- The bijection `TriEdge.equivHexGraphEdgeSet` commutes with the rotation `ρ`. -/
@[simp] theorem TriEdge.equivHexGraphEdgeSet_rot (e : TriEdge) :
    TriEdge.equivHexGraphEdgeSet (TriEdge.rot e) =
      hexGraphRot.mapEdgeSet (TriEdge.equivHexGraphEdgeSet e) :=
  Subtype.ext (TriEdge.dualEdge_rot e)

/-! ### The hexagon at a vertex -/

/-- Distinct faces sharing an edge are adjacent. -/
theorem hexGraph_adj_of_mem_edges {f g : TriFace} {e : TriEdge} (hfg : f ≠ g)
    (hf : e ∈ f.edges) (hg : e ∈ g.edges) : hexGraph.Adj f g :=
  hexGraph_adj.2 ⟨hfg, e, hf, hg⟩

/-- The six faces at the vertex `v`, traversed as a closed walk of `hexGraph`:
`W(v) – B(v) – W(v - e₁) – B(v - e₃) – W(v - e₃) – B(v - e₂) – W(v)`, through the edges `(v, 3)`,
`(v, 2)`, `(v - e₁, 1)`, `(v - e₃, 3)`, `(v - e₂, 2)` and `(v, 1)`. -/
def vertexCycle (v : ℤ × ℤ) : hexGraph.Walk ⟨v, true⟩ ⟨v, true⟩ :=
  .cons (v := ⟨v, false⟩)
    (hexGraph_adj_of_mem_edges (e := ⟨v, 2⟩) (by simp) (by simp) (by simp)) <|
  .cons (v := ⟨v - (1, 0), true⟩)
    (hexGraph_adj_of_mem_edges (e := ⟨v, 1⟩) (by simp) (by simp) (by simp)) <|
  .cons (v := ⟨v - (1, 1), false⟩)
    (hexGraph_adj_of_mem_edges (e := ⟨v - (1, 0), 0⟩) (by simp) (by simp)
      (by simp [Prod.ext_iff])) <|
  .cons (v := ⟨v - (1, 1), true⟩)
    (hexGraph_adj_of_mem_edges (e := ⟨v - (1, 1), 2⟩) (by simp) (by simp) (by simp)) <|
  .cons (v := ⟨v - (0, 1), false⟩)
    (hexGraph_adj_of_mem_edges (e := ⟨v - (0, 1), 1⟩) (by simp)
      (by simp [Prod.ext_iff]) (by simp)) <|
  .cons (hexGraph_adj_of_mem_edges (e := ⟨v, 0⟩) (by simp) (by simp) (by simp)) .nil

@[simp] theorem length_vertexCycle (v : ℤ × ℤ) : (vertexCycle v).length = 6 := (rfl)

/-- The six faces at a vertex form a cycle of `hexGraph`. -/
theorem vertexCycle_isCycle (v : ℤ × ℤ) : (vertexCycle v).IsCycle := by
  obtain ⟨x, y⟩ := v
  simp [vertexCycle, SimpleGraph.Walk.cons_isCycle_iff]
  omega

/-- The cycle `vertexCycle v` passes through exactly the six faces containing `v`. -/
theorem toFinset_support_vertexCycle (v : ℤ × ℤ) :
    (vertexCycle v).support.toFinset = vertexFaces v := by
  obtain ⟨x, y⟩ := v
  ext ⟨⟨a, b⟩, c⟩
  cases c <;> simp [vertexCycle] <;> omega

/-! ### Components outside a finite set -/

/-- A finite set of faces lies in a box: there is `N ≥ 0` with `|v.1| ≤ N` and `|v.2| ≤ N` for the
lower-left vertex `v` of every face of `R`. -/
private theorem exists_abs_le_of_finite {R : Set TriFace} (hR : R.Finite) :
    ∃ N : ℤ, 0 ≤ N ∧ ∀ f ∈ R, |f.v.1| ≤ N ∧ |f.v.2| ≤ N := by
  obtain ⟨N, hN⟩ := (hR.image fun f : TriFace => max |f.v.1| |f.v.2|).bddAbove
  refine ⟨max N 0, le_max_right _ _, fun f hf => ?_⟩
  have h := (hN ⟨f, hf, rfl⟩).trans (le_max_left N 0)
  exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

/-- The faces at positions in the box `[-N, N]²` form a finite set. -/
private theorem finite_setOf_abs_le (N : ℤ) :
    {f : TriFace | |f.v.1| ≤ N ∧ |f.v.2| ≤ N}.Finite := by
  refine (((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).prod
    (Set.finite_univ (α := Bool))).image (fun p => (⟨p.1, p.2⟩ : TriFace)) |>.subset ?_
  rintro ⟨v, b⟩ ⟨h₁, h₂⟩
  exact ⟨(v, b), ⟨⟨abs_le.1 h₁, abs_le.1 h₂⟩, trivial⟩, rfl⟩

section Far

variable {S : Set TriFace}

/-- Reachability in the graph of faces of `S`, for faces given as elements of `TriFace`. -/
private def ReachIn (S : Set TriFace) (f g : TriFace) : Prop :=
  ∃ (hf : f ∈ S) (hg : g ∈ S), (hexGraph.induce S).Reachable ⟨f, hf⟩ ⟨g, hg⟩

private theorem ReachIn.refl {f : TriFace} (hf : f ∈ S) : ReachIn S f f := ⟨hf, hf, .rfl⟩

private theorem ReachIn.trans {f g k : TriFace} (h₁ : ReachIn S f g) (h₂ : ReachIn S g k) :
    ReachIn S f k := by
  obtain ⟨hf, hg, r₁⟩ := h₁
  obtain ⟨hg', hk, r₂⟩ := h₂
  exact ⟨hf, hk, r₁.trans r₂⟩

private theorem ReachIn.symm {f g : TriFace} (h : ReachIn S f g) : ReachIn S g f := by
  obtain ⟨hf, hg, h⟩ := h
  exact ⟨hg, hf, h.symm⟩

private theorem reachIn_of_adj {f g : TriFace} (hf : f ∈ S) (hg : g ∈ S) (h : hexGraph.Adj f g) :
    ReachIn S f g :=
  ⟨hf, hg, (SimpleGraph.induce_adj.2 h).reachable⟩

/-- Faces `g a` and `g b` along a line `g : ℤ → TriFace` are joined when consecutive faces are. -/
private theorem reachIn_line {g : ℤ → TriFace} (hg : ∀ k, ReachIn S (g k) (g (k + 1)))
    (a b : ℤ) : ReachIn S (g a) (g b) := by
  have h : ∀ (a : ℤ) (n : ℕ), ReachIn S (g a) (g (a + n)) := fun a n => by
    induction n with
    | zero => simpa using ReachIn.refl (hg a).1
    | succ n ih => exact ih.trans (by simpa [add_assoc] using hg (a + n))
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ := Int.le.dest hab
    exact h a n
  · obtain ⟨n, rfl⟩ := Int.le.dest hab
    exact (h b n).symm

/-- `W(x, y)` and `W(x + 1, y)` are joined through `B(x + 1, y)`. -/
private theorem reachIn_white_add_one_fst {x y : ℤ} (h : ∀ b, (⟨(x, y), b⟩ : TriFace) ∈ S)
    (h' : ∀ b, (⟨(x + 1, y), b⟩ : TriFace) ∈ S) :
    ReachIn S ⟨(x, y), true⟩ ⟨(x + 1, y), true⟩ := by
  refine (reachIn_of_adj (h true) (h' false) ?_).trans (reachIn_of_adj (h' false) (h' true) ?_)
  · rw [← SimpleGraph.mem_neighborSet, hexGraph_neighborSet_mk_true]
    simp
  · rw [← SimpleGraph.mem_neighborSet, hexGraph_neighborSet_mk_false]
    simp

/-- `W(x, y)` and `W(x, y + 1)` are joined through `B(x, y)`. -/
private theorem reachIn_white_add_one_snd {x y : ℤ} (h : ∀ b, (⟨(x, y), b⟩ : TriFace) ∈ S)
    (h' : ∀ b, (⟨(x, y + 1), b⟩ : TriFace) ∈ S) :
    ReachIn S ⟨(x, y), true⟩ ⟨(x, y + 1), true⟩ := by
  refine (reachIn_of_adj (h true) (h false) ?_).trans (reachIn_of_adj (h false) (h' true) ?_)
  · rw [← SimpleGraph.mem_neighborSet, hexGraph_neighborSet_mk_true]
    simp
  · rw [← SimpleGraph.mem_neighborSet, hexGraph_neighborSet_mk_false]
    simp

/-- Every face at a position outside the box `[-N, N]²` is joined to `W(N + 1, N + 1)` by faces at
positions outside the box. -/
private theorem reachIn_far {N : ℤ} (hNN : N < |N + 1|)
    (hS : ∀ u : ℤ × ℤ, (N < |u.1| ∨ N < |u.2|) → ∀ b, (⟨u, b⟩ : TriFace) ∈ S)
    (f : TriFace) (hf : N < |f.v.1| ∨ N < |f.v.2|) :
    ReachIn S f ⟨(N + 1, N + 1), true⟩ := by
  obtain ⟨⟨x, y⟩, c⟩ := f
  have hwhite : ReachIn S ⟨(x, y), c⟩ ⟨(x, y), true⟩ := by
    cases c
    · refine reachIn_of_adj (hS _ hf false) (hS _ hf true) ?_
      rw [← SimpleGraph.mem_neighborSet, hexGraph_neighborSet_mk_false]
      simp
    · exact ReachIn.refl (hS _ hf true)
  have hrow {y : ℤ} (hy : N < |y|) (a b : ℤ) :
      ReachIn S ⟨(a, y), true⟩ ⟨(b, y), true⟩ :=
    reachIn_line (g := fun x => ⟨(x, y), true⟩)
      (fun _ => reachIn_white_add_one_fst (hS _ (Or.inr hy)) (hS _ (Or.inr hy))) a b
  have hcol {x : ℤ} (hx : N < |x|) (a b : ℤ) :
      ReachIn S ⟨(x, a), true⟩ ⟨(x, b), true⟩ :=
    reachIn_line (g := fun y => ⟨(x, y), true⟩)
      (fun _ => reachIn_white_add_one_snd (hS _ (Or.inl hx)) (hS _ (Or.inl hx))) a b
  refine hwhite.trans ?_
  rcases hf with hx | hy
  · exact (hcol hx y (N + 1)).trans (hrow hNN x (N + 1))
  · exact (hrow hy x (N + 1)).trans (hcol hNN y (N + 1))

end Far

/-- **Exactly one infinite component.** For finite `R`, exactly one component of the graph of faces
outside `R`, adjacent when they share an edge, is infinite: the one containing every face far from
`R`. -/
theorem hexGraph_existsUnique_infinite_supp_of_finite {R : Set TriFace} (hR : R.Finite) :
    ∃! c : hexGraph.ComponentCompl R, c.supp.Infinite := by
  obtain ⟨N, hN, hRN⟩ := exists_abs_le_of_finite hR
  have hP : ∀ u : ℤ × ℤ, (N < |u.1| ∨ N < |u.2|) → ∀ b, (⟨u, b⟩ : TriFace) ∈ Rᶜ := by
    intro u hu b hb
    have := hRN _ hb
    rcases hu with hu | hu
    · exact absurd this.1 (not_le.2 hu)
    · exact absurd this.2 (not_le.2 hu)
  have hNN : N < |N + 1| := by rw [abs_of_pos (by omega)]; omega
  have hhub : (⟨(N + 1, N + 1), true⟩ : TriFace) ∉ R := hP _ (Or.inl hNN) true
  have hfar : ∀ f : TriFace, (N < |f.v.1| ∨ N < |f.v.2|) → f ∈ hexGraph.componentComplMk hhub := by
    intro f hf
    obtain ⟨hfR, _, hr⟩ := reachIn_far hNN hP f hf
    exact ⟨hfR, SimpleGraph.ConnectedComponent.sound hr⟩
  refine ⟨hexGraph.componentComplMk hhub, ?_, fun c hc => ?_⟩
  · have : Infinite TriFace := Infinite.of_injective (fun v : ℤ × ℤ => (⟨v, true⟩ : TriFace))
      fun a b h => by simpa using congrArg TriFace.v h
    refine (finite_setOf_abs_le N).infinite_compl.mono fun f hf => hfar f ?_
    by_contra! H
    exact hf H
  · obtain ⟨f, ⟨_, rfl⟩, hf⟩ : ∃ f ∈ c, N < |f.v.1| ∨ N < |f.v.2| := by
      by_contra! H
      exact hc ((finite_setOf_abs_le N).subset H)
    obtain ⟨_, h⟩ := hfar f hf
    exact h

end TauCeti
