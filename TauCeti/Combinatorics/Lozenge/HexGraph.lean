/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Lozenge.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fintype.Fin

/-!
# The dual hexagonal graph of the triangular lattice

The dual hexagonal graph `hexGraph` has the faces of the triangular lattice as vertices, two faces
being adjacent when they are distinct and share an edge. The white face `W(v)` is adjacent exactly
to `B(v)`, `B(v - e₂)` and `B(v + e₁)` (`hexGraph_adj_white`), and the black face `B(v)` exactly to
`W(v)`, `W(v - e₁)` and `W(v + e₂)` (`hexGraph_adj_black`). The graph is `3`-regular
(`hexGraph_isRegularOfDegree`) and bipartite, with the white and black faces as parts
(`hexGraph_isBipartiteWith`). Adjacent faces share a unique edge, and sending an edge of the
lattice to its white and black faces is a bijection `TriEdge.equivHexGraphEdgeSet` from `TriEdge`
onto the edge set of `hexGraph`. Translations (`hexGraphTranslate`) and the rotation `ρ`
(`hexGraphRotate`) act by graph automorphisms, and the six faces at a vertex form a `6`-cycle
(`isCycle_hexCycleAt`).

A lozenge tiling of a region is the same as a perfect matching (a dimer covering) of the
corresponding subgraph of `hexGraph`, which is how the dimer model enters the study of lozenge
tilings.
-/

public section

namespace TauCeti

open SimpleGraph

/-- The dual hexagonal graph on the faces of the triangular lattice: two faces are adjacent when
they are distinct and share an edge. -/
def hexGraph : SimpleGraph TriFace :=
  SimpleGraph.fromRel fun f g => ∃ e, e ∈ f.edges ∧ e ∈ g.edges

/-- Two faces are adjacent when they are distinct and share an edge. -/
theorem hexGraph_adj {f g : TriFace} :
    hexGraph.Adj f g ↔ f ≠ g ∧ ∃ e, e ∈ f.edges ∧ e ∈ g.edges := by
  simp only [hexGraph, fromRel_adj, and_congr_right_iff]
  exact fun _ => or_iff_left_of_imp fun ⟨e, h₁, h₂⟩ => ⟨e, h₂, h₁⟩

/-- Two faces are adjacent exactly when they are the white and the black face of an edge. -/
theorem hexGraph_adj_iff_exists {f g : TriFace} :
    hexGraph.Adj f g ↔ ∃ e : TriEdge,
      (f = e.whiteFace ∧ g = e.blackFace) ∨ (f = e.blackFace ∧ g = e.whiteFace) := by
  rw [hexGraph_adj]
  constructor
  · rintro ⟨hfg, e, hf, hg⟩
    rw [TriFace.mem_edges_iff] at hf hg
    refine ⟨e, ?_⟩
    rcases hf with rfl | rfl <;> rcases hg with rfl | rfl <;> simp_all
  · rintro ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨e.whiteFace_ne_blackFace, e, e.mem_edges_whiteFace, e.mem_edges_blackFace⟩
    · exact ⟨e.whiteFace_ne_blackFace.symm, e, e.mem_edges_blackFace, e.mem_edges_whiteFace⟩

/-- The white and the black face of an edge are adjacent. -/
theorem TriEdge.hexGraph_adj (e : TriEdge) : hexGraph.Adj e.whiteFace e.blackFace :=
  hexGraph_adj_iff_exists.2 ⟨e, Or.inl ⟨rfl, rfl⟩⟩

/-- `W(v)` is adjacent exactly to `B(v)`, `B(v - e₂)` and `B(v + e₁)`, across the edges `(v, 3)`,
`(v, 1)` and `(v + e₁, 2)`. -/
theorem hexGraph_adj_white (v : ℤ × ℤ) (g : TriFace) :
    hexGraph.Adj ⟨v, true⟩ g ↔
      g = ⟨v, false⟩ ∨ g = ⟨v - (0, 1), false⟩ ∨ g = ⟨v + (1, 0), false⟩ := by
  rw [hexGraph_adj_iff_exists]
  constructor
  · rintro ⟨⟨⟨a, b⟩, k⟩, h⟩
    obtain ⟨c, d⟩ := v
    obtain ⟨⟨x, y⟩, _ | _⟩ := g <;> fin_cases k <;>
      simp [TriFace.ext_iff, Prod.ext_iff] at h ⊢ <;>
      omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨v, 2⟩, Or.inl ⟨by simp [TriFace.ext_iff], by simp [TriFace.ext_iff]⟩⟩
    · exact ⟨⟨v, 0⟩, Or.inl ⟨by simp [TriFace.ext_iff], by simp [TriFace.ext_iff]⟩⟩
    · exact ⟨⟨v + (1, 0), 1⟩, Or.inl ⟨by simp [TriFace.ext_iff], by simp [TriFace.ext_iff]⟩⟩

/-- `B(v)` is adjacent exactly to `W(v)`, `W(v - e₁)` and `W(v + e₂)`, across the edges `(v, 3)`,
`(v, 2)` and `(v + e₂, 1)`. -/
theorem hexGraph_adj_black (v : ℤ × ℤ) (g : TriFace) :
    hexGraph.Adj ⟨v, false⟩ g ↔
      g = ⟨v, true⟩ ∨ g = ⟨v - (1, 0), true⟩ ∨ g = ⟨v + (0, 1), true⟩ := by
  rw [hexGraph_adj_iff_exists]
  constructor
  · rintro ⟨⟨⟨a, b⟩, k⟩, h⟩
    obtain ⟨c, d⟩ := v
    obtain ⟨⟨x, y⟩, _ | _⟩ := g <;> fin_cases k <;>
      simp [TriFace.ext_iff, Prod.ext_iff] at h ⊢ <;>
      omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨v, 2⟩, Or.inr ⟨by simp [TriFace.ext_iff], by simp [TriFace.ext_iff]⟩⟩
    · exact ⟨⟨v, 1⟩, Or.inr ⟨by simp [TriFace.ext_iff], by simp [TriFace.ext_iff]⟩⟩
    · exact ⟨⟨v + (0, 1), 0⟩, Or.inr ⟨by simp [TriFace.ext_iff], by simp [TriFace.ext_iff]⟩⟩

/-- The three neighbours of a face in `hexGraph`. -/
def TriFace.neighbors (f : TriFace) : Finset TriFace :=
  if f.isWhite then {⟨f.v, false⟩, ⟨f.v - (0, 1), false⟩, ⟨f.v + (1, 0), false⟩}
  else {⟨f.v, true⟩, ⟨f.v - (1, 0), true⟩, ⟨f.v + (0, 1), true⟩}

/-- The neighbours of a face are the faces adjacent to it. -/
@[simp] theorem TriFace.mem_neighbors {f g : TriFace} : g ∈ f.neighbors ↔ hexGraph.Adj f g := by
  obtain ⟨v, _ | _⟩ := f
  · simp [neighbors, hexGraph_adj_black]
  · simp [neighbors, hexGraph_adj_white]

/-- The dual hexagonal graph is locally finite. -/
instance instLocallyFiniteHexGraph : hexGraph.LocallyFinite := fun f =>
  Fintype.ofFinset f.neighbors fun _ => TriFace.mem_neighbors

/-- The neighbour finset of a face is `TriFace.neighbors`. -/
@[simp] theorem hexGraph_neighborFinset (f : TriFace) :
    hexGraph.neighborFinset f = f.neighbors := by
  ext g
  simp [TriFace.mem_neighbors]

/-- The dual hexagonal graph is `3`-regular. -/
theorem hexGraph_isRegularOfDegree : hexGraph.IsRegularOfDegree 3 := fun f => by
  rw [← card_neighborFinset_eq_degree, hexGraph_neighborFinset]
  obtain ⟨⟨a, b⟩, _ | _⟩ := f <;>
  · rw [TriFace.neighbors, Finset.card_eq_three]
    refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;> simp [TriFace.ext_iff, eq_sub_iff_add_eq]

/-- The dual hexagonal graph is bipartite, with the white and the black faces as parts. -/
theorem hexGraph_isBipartiteWith :
    hexGraph.IsBipartiteWith {f | f.isWhite = true} {f | f.isWhite = false} where
  disjoint := Set.disjoint_left.2 fun f h₁ h₂ => by simp_all
  mem_of_adj f g h := by
    obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hexGraph_adj_iff_exists.1 h <;> simp

/-- The dual hexagonal graph is bipartite. -/
theorem hexGraph_isBipartite : hexGraph.IsBipartite :=
  hexGraph_isBipartiteWith.isBipartite

/-- Adjacent faces share a unique edge. -/
theorem existsUnique_mem_edges_of_hexGraph_adj {f g : TriFace} (h : hexGraph.Adj f g) :
    ∃! e, e ∈ f.edges ∧ e ∈ g.edges := by
  obtain ⟨hfg, e, hf, hg⟩ := hexGraph_adj.1 h
  exact ⟨e, ⟨hf, hg⟩, fun e' ⟨hf', hg'⟩ =>
    TriFace.eq_of_mem_edges_of_mem_edges hfg hf' hg' hf hg⟩

/-- Sending an edge of the triangular lattice to the pair of its white and black faces is a
bijection from `TriEdge` onto the edge set of `hexGraph`. -/
noncomputable def TriEdge.equivHexGraphEdgeSet : TriEdge ≃ hexGraph.edgeSet :=
  Equiv.ofBijective (fun e => ⟨s(e.whiteFace, e.blackFace), e.hexGraph_adj⟩) <| by
    constructor
    · intro e e' h
      have h := congrArg Subtype.val h
      simp only [Sym2.eq_iff] at h
      rcases h with ⟨hw, hb⟩ | ⟨hw, -⟩
      · exact TriEdge.eq_of_whiteFace_eq_of_blackFace_eq hw hb
      · simpa using congrArg TriFace.isWhite hw
    · rintro ⟨z, hz⟩
      induction z using Sym2.ind with
      | _ f g =>
        obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hexGraph_adj_iff_exists.1 hz
        · exact ⟨e, rfl⟩
        · exact ⟨e, Subtype.ext Sym2.eq_swap⟩

/-- An edge corresponds to the pair of its white and black faces. -/
@[simp] theorem TriEdge.equivHexGraphEdgeSet_apply (e : TriEdge) :
    (e.equivHexGraphEdgeSet : Sym2 TriFace) = s(e.whiteFace, e.blackFace) := (rfl)

/-- Translation by `w` is an automorphism of `hexGraph`. -/
def hexGraphTranslate (w : ℤ × ℤ) : hexGraph ≃g hexGraph where
  toEquiv := AddAction.toPerm w
  map_rel_iff' {f g} := by
    simp only [AddAction.toPerm_apply, hexGraph_adj, ne_eq, vadd_left_cancel_iff]
    refine and_congr_right fun _ => ⟨fun ⟨e, h₁, h₂⟩ => ⟨-w +ᵥ e, ?_, ?_⟩,
      fun ⟨e, h₁, h₂⟩ => ⟨w +ᵥ e, (TriFace.vadd_mem_edges_vadd w e f).2 h₁,
        (TriFace.vadd_mem_edges_vadd w e g).2 h₂⟩⟩
    · rwa [← TriFace.vadd_mem_edges_vadd w, vadd_neg_vadd]
    · rwa [← TriFace.vadd_mem_edges_vadd w, vadd_neg_vadd]

/-- The automorphism `hexGraphTranslate w` is translation by `w`. -/
@[simp] theorem hexGraphTranslate_apply (w : ℤ × ℤ) (f : TriFace) :
    hexGraphTranslate w f = w +ᵥ f := (rfl)

/-- The rotation `ρ` of order three, as a permutation of the faces. -/
def TriFace.rotateEquiv : TriFace ≃ TriFace where
  toFun := rotate
  invFun f := f.rotate.rotate
  left_inv := rotate_rotate_rotate
  right_inv := rotate_rotate_rotate

/-- The permutation `TriFace.rotateEquiv` is the rotation of faces. -/
@[simp] theorem TriFace.rotateEquiv_apply (f : TriFace) : rotateEquiv f = f.rotate := (rfl)

/-- The inverse of `TriFace.rotateEquiv` is the rotation applied twice. -/
@[simp] theorem TriFace.rotateEquiv_symm_apply (f : TriFace) :
    rotateEquiv.symm f = f.rotate.rotate := (rfl)

/-- The rotation `ρ` is an automorphism of `hexGraph`. -/
def hexGraphRotate : hexGraph ≃g hexGraph where
  toEquiv := TriFace.rotateEquiv
  map_rel_iff' {f g} := by
    simp only [TriFace.rotateEquiv_apply, hexGraph_adj, ne_eq,
      TriFace.rotate_injective.eq_iff]
    refine and_congr_right fun _ => ⟨fun ⟨e, h₁, h₂⟩ => ⟨e.rotate.rotate, ?_, ?_⟩,
      fun ⟨e, h₁, h₂⟩ => ⟨e.rotate, (TriFace.rotate_mem_edges_rotate e f).2 h₁,
        (TriFace.rotate_mem_edges_rotate e g).2 h₂⟩⟩
    · rwa [← TriFace.rotate_mem_edges_rotate, TriEdge.rotate_rotate_rotate]
    · rwa [← TriFace.rotate_mem_edges_rotate, TriEdge.rotate_rotate_rotate]

/-- The automorphism `hexGraphRotate` is the rotation of faces. -/
@[simp] theorem hexGraphRotate_apply (f : TriFace) : hexGraphRotate f = f.rotate := (rfl)

/-- The closed walk `W(u) – B(u) – W(u - e₁) – B(u - e₃) – W(u - e₃) – B(u - e₂) – W(u)` through
the six faces at the vertex `u`, across the six edges at `u`. -/
def hexCycleAt (u : ℤ × ℤ) : hexGraph.Walk ⟨u, true⟩ ⟨u, true⟩ :=
  have h₁ : hexGraph.Adj ⟨u, true⟩ ⟨u, false⟩ := (hexGraph_adj_white u _).2 (Or.inl rfl)
  have h₂ : hexGraph.Adj ⟨u, false⟩ ⟨u - (1, 0), true⟩ :=
    (hexGraph_adj_black u _).2 (Or.inr (Or.inl rfl))
  have h₃ : hexGraph.Adj ⟨u - (1, 0), true⟩ ⟨u - (1, 1), false⟩ :=
    (hexGraph_adj_white _ _).2 (Or.inr (Or.inl (by simp [TriFace.ext_iff, Prod.ext_iff])))
  have h₄ : hexGraph.Adj ⟨u - (1, 1), false⟩ ⟨u - (1, 1), true⟩ :=
    (hexGraph_adj_black _ _).2 (Or.inl rfl)
  have h₅ : hexGraph.Adj ⟨u - (1, 1), true⟩ ⟨u - (0, 1), false⟩ :=
    (hexGraph_adj_white _ _).2 (Or.inr (Or.inr (by simp [TriFace.ext_iff, Prod.ext_iff])))
  have h₆ : hexGraph.Adj ⟨u - (0, 1), false⟩ ⟨u, true⟩ :=
    (hexGraph_adj_black _ _).2 (Or.inr (Or.inr (by simp)))
  .cons h₁ <| .cons h₂ <| .cons h₃ <| .cons h₄ <| .cons h₅ <| .cons h₆ .nil

/-- The six faces at a vertex form a `6`-cycle of `hexGraph`. -/
theorem isCycle_hexCycleAt (u : ℤ × ℤ) : (hexCycleAt u).IsCycle := by
  obtain ⟨a, b⟩ := u
  simp [hexCycleAt, Walk.cons_isCycle_iff, Walk.isPath_def, TriFace.ext_iff, Prod.ext_iff,
    eq_sub_iff_add_eq]

/-- The cycle at the vertex `u` passes through the six faces containing `u`. -/
theorem support_hexCycleAt (u : ℤ × ℤ) :
    (hexCycleAt u).support = [⟨u, true⟩, ⟨u, false⟩, ⟨u - (1, 0), true⟩, ⟨u - (1, 1), false⟩,
      ⟨u - (1, 1), true⟩, ⟨u - (0, 1), false⟩, ⟨u, true⟩] :=
  (rfl)

/-- The cycle of faces at a vertex has length `6`. -/
theorem length_hexCycleAt (u : ℤ × ℤ) : (hexCycleAt u).length = 6 := (rfl)

end TauCeti
