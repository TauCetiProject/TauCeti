/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The triangular lattice: edges, faces and symmetries

The triangular lattice `𝕋` has vertex set `ℤ × ℤ` and positive directions `e₁ = (1,0)`,
`e₂ = (0,1)`, `e₃ = (1,1)`. Every edge is the segment from a vertex `v` to `v + e_k` for exactly
one pair `(v, k)`, and every face is either the white triangle `W(v) = {v, v + e₁, v + e₃}` or
the black triangle `B(v) = {v, v + e₂, v + e₃}`. This is the lattice of Aggarwal's universality
paper, drawn on `ℤ²` rather than with angles `π/3`; lozenge tilings of regions of `𝕋` are the
perfect matchings of the dual hexagonal graph, whose vertices are the faces of `𝕋`.

This file fixes the carriers and their incidence, and the symmetries of the coloured lattice:
the translations by `ℤ²` and the rotation `ρ(x, y) = (-y, x - y)` of order three.

## Main definitions

* `TauCeti.latticeDir`: the directions `e₁, e₂, e₃`, indexed by `Fin 3`.
* `TauCeti.TriEdge`: an edge `(v, k)`, the segment from `v` to `TriEdge.target = v + e_k`.
* `TauCeti.TriFace`: a face `W(v)` or `B(v)`, with its vertices `TriFace.vertices`, its edges
  `TriFace.edges` and its edge of direction `k`, `TriFace.edge`.
* `TauCeti.TriEdge.whiteFace`, `TauCeti.TriEdge.blackFace`, `TauCeti.TriEdge.faces`: the two faces
  containing an edge.
* `TauCeti.vertexFaces`: the six faces containing a vertex.
* The additive actions of `ℤ × ℤ` by translation on edges, faces and configurations
  `TriEdge → Bool` (the last one Mathlib's `arrowAddAction`).
* `TauCeti.latticeRot`, `TauCeti.TriEdge.rot`, `TauCeti.TriFace.rot`: the rotation `ρ` on vertices,
  edges and faces.

## Main statements

* `TauCeti.TriFace.mem_edges_iff`: an edge lies exactly in its white and its black face.
* `TauCeti.TriFace.mem_edges_iff_edge_eq`, `TauCeti.TriFace.card_edges`: a face has one edge of
  each direction.
* `TauCeti.TriFace.eq_of_mem_edges_of_mem_edges`, `TauCeti.TriFace.isWhite_ne_of_mem_edges`: two
  distinct faces share at most one edge, and faces sharing an edge have opposite colours.
* `TauCeti.mem_vertexFaces`, `TauCeti.card_vertexFaces`: exactly six faces contain a vertex.
* `TauCeti.TriEdge.vadd_eq_self_iff`, `TauCeti.TriFace.vadd_eq_self_iff`: translations act freely.
* `TauCeti.setOf_vadd_eq_true`: the edge set of a translated configuration is the translated edge
  set.
* `TauCeti.addOrderOf_latticeRot`, `TauCeti.TriEdge.orderOf_rot`, `TauCeti.TriFace.orderOf_rot`: `ρ`
  has order three on vertices, edges and faces; `TauCeti.TriFace.edges_rot` and
  `TauCeti.TriFace.vertices_rot` say it preserves incidence, and `TauCeti.TriEdge.rot_vadd` and
  `TauCeti.TriFace.rot_vadd` that it commutes with translations up to `ρ` on the translation
  vector.

## References

* A. Aggarwal, *Universality for lozenge tiling local statistics*, Ann. of Math. 198 (2023),
  Section 1.2.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 1.
-/

public section

open Pointwise

namespace TauCeti

/-- The positive directions `e₁ = (1,0)`, `e₂ = (0,1)`, `e₃ = (1,1)` of the triangular lattice on
`ℤ × ℤ`. The direction `k ∈ {1, 2, 3}` is stored as the index `k - 1 : Fin 3`. -/
def latticeDir : Fin 3 → ℤ × ℤ := ![(1, 0), (0, 1), (1, 1)]

@[simp] theorem latticeDir_zero : latticeDir 0 = (1, 0) := (rfl)

@[simp] theorem latticeDir_one : latticeDir 1 = (0, 1) := (rfl)

@[simp] theorem latticeDir_two : latticeDir 2 = (1, 1) := (rfl)

/-- An edge of the triangular lattice: the segment from `v` to `v + latticeDir k`. Every edge of
the lattice has exactly one such name. -/
@[ext]
structure TriEdge where
  /-- The initial vertex. -/
  v : ℤ × ℤ
  /-- The direction, `0, 1, 2` for `e₁, e₂, e₃`. -/
  k : Fin 3
  deriving DecidableEq, Countable

/-- A face of the triangular lattice: the white face `W(v) = {v, v + e₁, v + e₃}` when `isWhite`,
the black face `B(v) = {v, v + e₂, v + e₃}` otherwise. -/
@[ext]
structure TriFace where
  /-- The lower-left vertex. -/
  v : ℤ × ℤ
  /-- The colour: `true` for a white face, `false` for a black one. -/
  isWhite : Bool
  deriving DecidableEq, Countable

namespace TriEdge

/-- The final vertex `v + e_k` of an edge. -/
def target (e : TriEdge) : ℤ × ℤ := e.v + latticeDir e.k

@[simp] theorem target_mk (v : ℤ × ℤ) (k : Fin 3) : (⟨v, k⟩ : TriEdge).target = v + latticeDir k :=
  (rfl)

theorem v_ne_target (e : TriEdge) : e.v ≠ e.target := by
  obtain ⟨⟨x, y⟩, k⟩ := e
  fin_cases k <;> simp [Prod.ext_iff]

/-- The white face containing an edge: `W(v)` for `(v, 1)` and `(v, 3)`, and `W(v - e₁)` for
`(v, 2)`. -/
def whiteFace (e : TriEdge) : TriFace := ⟨if e.k = 1 then e.v - (1, 0) else e.v, true⟩

/-- The black face containing an edge: `B(v - e₂)` for `(v, 1)`, and `B(v)` for `(v, 2)` and
`(v, 3)`. -/
def blackFace (e : TriEdge) : TriFace := ⟨if e.k = 0 then e.v - (0, 1) else e.v, false⟩

/-- The two faces containing an edge, its white face and its black face. -/
def faces (e : TriEdge) : Finset TriFace := {e.whiteFace, e.blackFace}

theorem faces_def (e : TriEdge) : e.faces = {e.whiteFace, e.blackFace} := (rfl)

@[simp] theorem whiteFace_mk (v : ℤ × ℤ) (k : Fin 3) :
    (⟨v, k⟩ : TriEdge).whiteFace = ⟨if k = 1 then v - (1, 0) else v, true⟩ := (rfl)

@[simp] theorem blackFace_mk (v : ℤ × ℤ) (k : Fin 3) :
    (⟨v, k⟩ : TriEdge).blackFace = ⟨if k = 0 then v - (0, 1) else v, false⟩ := (rfl)

@[simp] theorem whiteFace_isWhite (e : TriEdge) : e.whiteFace.isWhite = true := (rfl)

@[simp] theorem blackFace_isWhite (e : TriEdge) : e.blackFace.isWhite = false := (rfl)

theorem whiteFace_ne_blackFace (e : TriEdge) : e.whiteFace ≠ e.blackFace :=
  fun h => by simpa using congrArg TriFace.isWhite h

@[simp] theorem card_faces (e : TriEdge) : e.faces.card = 2 :=
  Finset.card_pair e.whiteFace_ne_blackFace

end TriEdge

namespace TriFace

/-- The three vertices of a face: `v, v + e₁, v + e₃` for `W(v)` and `v, v + e₂, v + e₃` for
`B(v)`. -/
def vertices (f : TriFace) : Finset (ℤ × ℤ) :=
  if f.isWhite then {f.v, f.v + (1, 0), f.v + (1, 1)} else {f.v, f.v + (0, 1), f.v + (1, 1)}

/-- The three edges of a face: `(v,1)`, `(v+e₁,2)`, `(v,3)` for `W(v)` and `(v,2)`, `(v+e₂,1)`,
`(v,3)` for `B(v)`. -/
def edges (f : TriFace) : Finset TriEdge :=
  if f.isWhite then {⟨f.v, 0⟩, ⟨f.v + (1, 0), 1⟩, ⟨f.v, 2⟩}
  else {⟨f.v, 1⟩, ⟨f.v + (0, 1), 0⟩, ⟨f.v, 2⟩}

/-- The edge of direction `k` of a face. -/
def edge (f : TriFace) (k : Fin 3) : TriEdge :=
  ⟨if f.isWhite then (if k = 1 then f.v + (1, 0) else f.v)
    else (if k = 0 then f.v + (0, 1) else f.v), k⟩

@[simp] theorem vertices_mk_true (v : ℤ × ℤ) :
    (⟨v, true⟩ : TriFace).vertices = {v, v + (1, 0), v + (1, 1)} := (rfl)

@[simp] theorem vertices_mk_false (v : ℤ × ℤ) :
    (⟨v, false⟩ : TriFace).vertices = {v, v + (0, 1), v + (1, 1)} := (rfl)

@[simp] theorem edges_mk_true (v : ℤ × ℤ) :
    (⟨v, true⟩ : TriFace).edges = {⟨v, 0⟩, ⟨v + (1, 0), 1⟩, ⟨v, 2⟩} := (rfl)

@[simp] theorem edges_mk_false (v : ℤ × ℤ) :
    (⟨v, false⟩ : TriFace).edges = {⟨v, 1⟩, ⟨v + (0, 1), 0⟩, ⟨v, 2⟩} := (rfl)

@[simp] theorem edge_mk_true (v : ℤ × ℤ) (k : Fin 3) :
    (⟨v, true⟩ : TriFace).edge k = ⟨if k = 1 then v + (1, 0) else v, k⟩ := (rfl)

@[simp] theorem edge_mk_false (v : ℤ × ℤ) (k : Fin 3) :
    (⟨v, false⟩ : TriFace).edge k = ⟨if k = 0 then v + (0, 1) else v, k⟩ := (rfl)

@[simp] theorem edge_k (f : TriFace) (k : Fin 3) : (f.edge k).k = k := (rfl)

/-- **Incidence of edges and faces.** An edge lies in exactly two faces, its white face and its
black face. -/
theorem mem_edges_iff {f : TriFace} {e : TriEdge} :
    e ∈ f.edges ↔ f = e.whiteFace ∨ f = e.blackFace := by
  obtain ⟨⟨a, b⟩, c⟩ := f
  obtain ⟨⟨x, y⟩, k⟩ := e
  fin_cases k <;> cases c <;>
    simp [TriEdge.whiteFace, TriEdge.blackFace, TriEdge.ext_iff, TriFace.ext_iff] <;> omega

/-- A face has exactly one edge of each direction: its edges are the `f.edge k`. -/
theorem mem_edges_iff_edge_eq {f : TriFace} {e : TriEdge} : e ∈ f.edges ↔ f.edge e.k = e := by
  obtain ⟨⟨a, b⟩, c⟩ := f
  obtain ⟨⟨x, y⟩, k⟩ := e
  fin_cases k <;> cases c <;> simp [edge, TriEdge.ext_iff] <;> omega

theorem edge_mem_edges (f : TriFace) (k : Fin 3) : f.edge k ∈ f.edges :=
  mem_edges_iff_edge_eq.2 rfl

theorem edge_injective (f : TriFace) : Function.Injective f.edge :=
  fun k k' h => by simpa using congrArg TriEdge.k h

/-- A face has three edges. -/
@[simp] theorem card_edges (f : TriFace) : f.edges.card = 3 := by
  have : f.edges = Finset.univ.image f.edge := by
    ext e
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨e.k, mem_edges_iff_edge_eq.1 h⟩,
      fun ⟨k, hk⟩ => hk ▸ f.edge_mem_edges k⟩
  rw [this, Finset.card_image_of_injective _ f.edge_injective, Finset.card_univ, Fintype.card_fin]

@[simp] theorem card_vertices (f : TriFace) : f.vertices.card = 3 := by
  obtain ⟨⟨a, b⟩, c⟩ := f
  cases c <;> rw [Finset.card_eq_three] <;>
    exact ⟨_, _, _, by simp, by simp, by simp, rfl⟩

/-- Two faces sharing an edge and differing are of opposite colours. -/
theorem isWhite_ne_of_mem_edges {f g : TriFace} {e : TriEdge} (hfg : f ≠ g) (hf : e ∈ f.edges)
    (hg : e ∈ g.edges) : f.isWhite ≠ g.isWhite := by
  rw [mem_edges_iff] at hf hg
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl <;> simp_all

/-- Three faces containing an edge: the third is one of two distinct ones, since an edge lies in
exactly two faces. -/
theorem eq_or_eq_of_mem_edges {e : TriEdge} {f g h : TriFace} (hfg : f ≠ g)
    (hf : e ∈ f.edges) (hg : e ∈ g.edges) (hh : e ∈ h.edges) : h = f ∨ h = g := by
  rw [mem_edges_iff] at hf hg hh
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl <;> rcases hh with rfl | rfl <;>
    simp_all

/-- Two distinct faces share at most one edge. -/
theorem eq_of_mem_edges_of_mem_edges {f g : TriFace} {e e' : TriEdge} (hfg : f ≠ g)
    (hef : e ∈ f.edges) (heg : e ∈ g.edges) (hef' : e' ∈ f.edges) (heg' : e' ∈ g.edges) :
    e = e' := by
  obtain ⟨⟨a, b⟩, c⟩ := f
  obtain ⟨⟨a', b'⟩, c'⟩ := g
  obtain ⟨⟨x, y⟩, k⟩ := e
  obtain ⟨⟨x', y'⟩, k'⟩ := e'
  cases c <;> cases c' <;> fin_cases k <;> fin_cases k' <;>
    simp [TriEdge.ext_iff, TriFace.ext_iff] at hfg hef heg hef' heg' ⊢ <;> omega

theorem card_edges_inter_le_one {f g : TriFace} (hfg : f ≠ g) : (f.edges ∩ g.edges).card ≤ 1 :=
  Finset.card_le_one.2 fun _ he _ he' => by
    rw [Finset.mem_inter] at he he'
    exact eq_of_mem_edges_of_mem_edges hfg he.1 he.2 he'.1 he'.2

/-- The initial vertex of an edge of a face is a vertex of the face. -/
theorem v_mem_vertices_of_mem_edges {f : TriFace} {e : TriEdge} (he : e ∈ f.edges) :
    e.v ∈ f.vertices := by
  obtain ⟨⟨a, b⟩, c⟩ := f
  obtain ⟨⟨x, y⟩, k⟩ := e
  cases c <;> fin_cases k <;> simp [TriEdge.ext_iff] at he ⊢ <;> omega

/-- The final vertex `e.target` of an edge of a face is a vertex of the face. -/
theorem target_mem_vertices_of_mem_edges {f : TriFace} {e : TriEdge} (he : e ∈ f.edges) :
    e.target ∈ f.vertices := by
  obtain ⟨⟨a, b⟩, c⟩ := f
  obtain ⟨⟨x, y⟩, k⟩ := e
  cases c <;> fin_cases k <;> simp [TriEdge.ext_iff] at he ⊢ <;> omega

end TriFace

namespace TriEdge

@[simp] theorem mem_whiteFace_edges (e : TriEdge) : e ∈ e.whiteFace.edges :=
  TriFace.mem_edges_iff.2 (Or.inl rfl)

@[simp] theorem mem_blackFace_edges (e : TriEdge) : e ∈ e.blackFace.edges :=
  TriFace.mem_edges_iff.2 (Or.inr rfl)

@[simp] theorem mem_faces {e : TriEdge} {f : TriFace} : f ∈ e.faces ↔ e ∈ f.edges := by
  rw [TriFace.mem_edges_iff, faces, Finset.mem_insert, Finset.mem_singleton]

/-- An edge is determined by its two faces. -/
theorem eq_of_whiteFace_eq_of_blackFace_eq {e e' : TriEdge} (hw : e.whiteFace = e'.whiteFace)
    (hb : e.blackFace = e'.blackFace) : e = e' :=
  TriFace.eq_of_mem_edges_of_mem_edges e.whiteFace_ne_blackFace e.mem_whiteFace_edges
    e.mem_blackFace_edges (hw ▸ e'.mem_whiteFace_edges) (hb ▸ e'.mem_blackFace_edges)

/-- The white face of an edge is the unique white face containing it. -/
theorem eq_whiteFace_of_mem_edges {e : TriEdge} {f : TriFace} (he : e ∈ f.edges)
    (hf : f.isWhite = true) : f = e.whiteFace := by
  rcases TriFace.mem_edges_iff.1 he with h | rfl
  · exact h
  · simp at hf

/-- The black face of an edge is the unique black face containing it. -/
theorem eq_blackFace_of_mem_edges {e : TriEdge} {f : TriFace} (he : e ∈ f.edges)
    (hf : f.isWhite = false) : f = e.blackFace := by
  rcases TriFace.mem_edges_iff.1 he with rfl | h
  · simp at hf
  · exact h

/-- An edge is determined by its lozenge. -/
theorem faces_injective : Function.Injective faces := by
  intro e e' h
  have hw : e.whiteFace ∈ e'.faces := h ▸ mem_faces.2 e.mem_whiteFace_edges
  have hb : e.blackFace ∈ e'.faces := h ▸ mem_faces.2 e.mem_blackFace_edges
  rw [faces_def, Finset.mem_insert, Finset.mem_singleton] at hw hb
  refine eq_of_whiteFace_eq_of_blackFace_eq (hw.resolve_right fun h' => ?_)
    (hb.resolve_left fun h' => ?_)
  · simpa using congrArg TriFace.isWhite h'
  · simpa using congrArg TriFace.isWhite h'

end TriEdge

/-- An edge of a face also lies in a second face. -/
theorem TriFace.exists_ne_mem_edges {e : TriEdge} {f : TriFace} (he : e ∈ f.edges) :
    ∃ g, g ≠ f ∧ e ∈ g.edges := by
  rcases mem_edges_iff.1 he with rfl | rfl
  exacts [⟨_, e.whiteFace_ne_blackFace.symm, e.mem_blackFace_edges⟩,
    ⟨_, e.whiteFace_ne_blackFace, e.mem_whiteFace_edges⟩]

/-! ### The six faces at a vertex -/

/-- The six faces containing the vertex `v`: `W(v)`, `W(v - e₁)`, `W(v - e₃)`, `B(v)`,
`B(v - e₂)` and `B(v - e₃)`. -/
def vertexFaces (v : ℤ × ℤ) : Finset TriFace :=
  {⟨v, true⟩, ⟨v - (1, 0), true⟩, ⟨v - (1, 1), true⟩,
    ⟨v, false⟩, ⟨v - (0, 1), false⟩, ⟨v - (1, 1), false⟩}

theorem vertexFaces_def (v : ℤ × ℤ) :
    vertexFaces v = {⟨v, true⟩, ⟨v - (1, 0), true⟩, ⟨v - (1, 1), true⟩,
      ⟨v, false⟩, ⟨v - (0, 1), false⟩, ⟨v - (1, 1), false⟩} := (rfl)

/-- The faces in `vertexFaces v` are exactly those having `v` as a vertex. -/
@[simp] theorem mem_vertexFaces {v : ℤ × ℤ} {f : TriFace} :
    f ∈ vertexFaces v ↔ v ∈ f.vertices := by
  obtain ⟨⟨a, b⟩, c⟩ := f
  obtain ⟨x, y⟩ := v
  cases c <;> simp [vertexFaces] <;> omega

/-! ### Translations -/

namespace TriEdge

/-- `ℤ²` acts on edges by translation, `w +ᵥ (v, k) = (w + v, k)`. -/
instance : AddAction (ℤ × ℤ) TriEdge where
  vadd w e := ⟨w + e.v, e.k⟩
  zero_vadd e := TriEdge.ext (zero_add e.v) rfl
  add_vadd w w' e := TriEdge.ext (add_assoc w w' e.v) rfl

@[simp] theorem vadd_mk (w v : ℤ × ℤ) (k : Fin 3) : w +ᵥ (⟨v, k⟩ : TriEdge) = ⟨w + v, k⟩ := (rfl)

@[simp] theorem vadd_v (w : ℤ × ℤ) (e : TriEdge) : (w +ᵥ e).v = w + e.v := (rfl)

@[simp] theorem vadd_k (w : ℤ × ℤ) (e : TriEdge) : (w +ᵥ e).k = e.k := (rfl)

@[simp] theorem target_vadd (w : ℤ × ℤ) (e : TriEdge) : (w +ᵥ e).target = w + e.target :=
  add_assoc w e.v _

/-- Translations act freely on edges. -/
theorem vadd_eq_self_iff {w : ℤ × ℤ} {e : TriEdge} : w +ᵥ e = e ↔ w = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ zero_vadd _ e⟩
  simpa using congrArg TriEdge.v h

end TriEdge

namespace TriFace

/-- `ℤ²` acts on faces by translation, `w +ᵥ W(v) = W(w + v)` and `w +ᵥ B(v) = B(w + v)`. -/
instance : AddAction (ℤ × ℤ) TriFace where
  vadd w f := ⟨w + f.v, f.isWhite⟩
  zero_vadd f := TriFace.ext (zero_add f.v) rfl
  add_vadd w w' f := TriFace.ext (add_assoc w w' f.v) rfl

@[simp] theorem vadd_mk (w v : ℤ × ℤ) (c : Bool) : w +ᵥ (⟨v, c⟩ : TriFace) = ⟨w + v, c⟩ := (rfl)

@[simp] theorem vadd_v (w : ℤ × ℤ) (f : TriFace) : (w +ᵥ f).v = w + f.v := (rfl)

/-- Translations preserve colours. -/
@[simp] theorem vadd_isWhite (w : ℤ × ℤ) (f : TriFace) : (w +ᵥ f).isWhite = f.isWhite := (rfl)

/-- Translations act freely on faces. -/
theorem vadd_eq_self_iff {w : ℤ × ℤ} {f : TriFace} : w +ᵥ f = f ↔ w = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ zero_vadd _ f⟩
  simpa using congrArg TriFace.v h

@[simp] theorem edge_vadd (w : ℤ × ℤ) (f : TriFace) (k : Fin 3) :
    (w +ᵥ f).edge k = w +ᵥ f.edge k := by
  ext <;> simp only [edge, vadd_v, vadd_isWhite, TriEdge.vadd_v, TriEdge.vadd_k] <;>
    split_ifs <;> simp [add_assoc]

@[simp] theorem edges_vadd (w : ℤ × ℤ) (f : TriFace) : (w +ᵥ f).edges = w +ᵥ f.edges := by
  obtain ⟨v, c⟩ := f
  cases c <;> simp [Finset.vadd_finset_insert, add_assoc]

@[simp] theorem vertices_vadd (w : ℤ × ℤ) (f : TriFace) : (w +ᵥ f).vertices = w +ᵥ f.vertices := by
  obtain ⟨v, c⟩ := f
  cases c <;> simp [Finset.vadd_finset_insert, vadd_eq_add, add_assoc]

end TriFace

namespace TriEdge

@[simp] theorem whiteFace_vadd (w : ℤ × ℤ) (e : TriEdge) :
    (w +ᵥ e).whiteFace = w +ᵥ e.whiteFace := by
  refine TriFace.ext ?_ rfl
  simp only [whiteFace, vadd_v, vadd_k, TriFace.vadd_v]
  split_ifs <;> abel

@[simp] theorem blackFace_vadd (w : ℤ × ℤ) (e : TriEdge) :
    (w +ᵥ e).blackFace = w +ᵥ e.blackFace := by
  refine TriFace.ext ?_ rfl
  simp only [blackFace, vadd_v, vadd_k, TriFace.vadd_v]
  split_ifs <;> abel

@[simp] theorem faces_vadd (w : ℤ × ℤ) (e : TriEdge) : (w +ᵥ e).faces = w +ᵥ e.faces := by
  simp [faces, Finset.vadd_finset_insert]

end TriEdge

@[simp] theorem vertexFaces_add (w v : ℤ × ℤ) : vertexFaces (w + v) = w +ᵥ vertexFaces v := by
  simp [vertexFaces, Finset.vadd_finset_insert, add_sub_assoc]

/-- Exactly six faces contain a vertex. -/
@[simp] theorem card_vertexFaces (v : ℤ × ℤ) : (vertexFaces v).card = 6 := by
  rw [← add_zero v, vertexFaces_add, Finset.card_vadd_finset]
  decide

/-- `ℤ²` acts on configurations `ω : TriEdge → Bool` by `(w +ᵥ ω) e = ω (-w +ᵥ e)`
(Mathlib's `arrowAddAction`), so that the edge set of `w +ᵥ ω` is the translate by `w` of the
edge set of `ω` (`setOf_vadd_eq_true`). -/
instance : AddAction (ℤ × ℤ) (TriEdge → Bool) := arrowAddAction

@[simp] theorem vadd_config_apply (w : ℤ × ℤ) (ω : TriEdge → Bool) (e : TriEdge) :
    (w +ᵥ ω) e = ω (-w +ᵥ e) := (rfl)

/-- The edge set of a translated configuration is the translated edge set. -/
theorem setOf_vadd_eq_true (w : ℤ × ℤ) (ω : TriEdge → Bool) :
    {e | (w +ᵥ ω) e = true} = w +ᵥ {e | ω e = true} := by
  ext e
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simp only [Set.mem_ofPred_eq, vadd_config_apply]

/-! ### The rotation of order three -/

/-- The rotation `ρ(x, y) = (-y, x - y)` of `ℤ²`. It maps `e₁ ↦ e₂ ↦ -e₃` and `e₃ ↦ -e₁`, and
has order three. -/
def latticeRot : ℤ × ℤ ≃+ ℤ × ℤ where
  toFun p := (-p.2, p.1 - p.2)
  invFun p := (p.2 - p.1, -p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp <;> abel

@[simp] theorem latticeRot_apply (p : ℤ × ℤ) : latticeRot p = (-p.2, p.1 - p.2) := (rfl)

@[simp] theorem latticeRot_symm_apply (p : ℤ × ℤ) :
    latticeRot.symm p = (p.2 - p.1, -p.1) := (rfl)

theorem latticeRot_latticeDir_zero : latticeRot (latticeDir 0) = latticeDir 1 := (rfl)

theorem latticeRot_latticeDir_one : latticeRot (latticeDir 1) = -latticeDir 2 := (rfl)

theorem latticeRot_latticeDir_two : latticeRot (latticeDir 2) = -latticeDir 0 := (rfl)

theorem latticeRot_latticeRot_latticeRot (p : ℤ × ℤ) :
    latticeRot (latticeRot (latticeRot p)) = p :=
  Prod.ext (by simp) (by simp; ring)

/-- `ρ` has order three in the additive group `AddAut (ℤ × ℤ)` (whose addition is
composition). -/
theorem addOrderOf_latticeRot : addOrderOf (latticeRot : AddAut (ℤ × ℤ)) = 3 := by
  refine addOrderOf_eq_prime (AddEquiv.ext fun p => ?_) fun h => ?_
  · simp only [succ_nsmul, zero_nsmul, zero_add, AddAut.add_apply]
    exact latticeRot_latticeRot_latticeRot p
  · simpa using congrArg (fun φ : AddAut (ℤ × ℤ) => φ (1, 0)) h

namespace TriEdge

/-- The rotation `ρ` on edges. It maps the segment from `v` to `v + e_k` onto the segment between
`ρ v` and `ρ (v + e_k)`, of direction `k + 1`; since `ρ e₁ = e₂` is positive while `ρ e₂ = -e₃`
and `ρ e₃ = -e₁` are negative, the initial vertex of the image is `ρ v` for `k = 1` and
`ρ (v + e_k)` otherwise (`TriEdge.rot_v`, `TriEdge.target_rot`). -/
def rot : Equiv.Perm TriEdge where
  toFun e := ⟨if e.k = 0 then latticeRot e.v else latticeRot e.target, e.k + 1⟩
  invFun e := ⟨latticeRot.symm (if e.k = 1 then e.v else e.v + latticeDir e.k), e.k + 2⟩
  left_inv e := by
    obtain ⟨⟨x, y⟩, k⟩ := e
    fin_cases k
    · simp +decide
    · simp +decide [TriEdge.ext_iff]
      omega
    · simp +decide
  right_inv e := by
    obtain ⟨⟨x, y⟩, k⟩ := e
    fin_cases k
    · simp +decide [TriEdge.ext_iff]
      omega
    · simp +decide
    · simp +decide

theorem rot_apply (e : TriEdge) :
    rot e = ⟨if e.k = 0 then latticeRot e.v else latticeRot e.target, e.k + 1⟩ := (rfl)

theorem rot_symm_apply (e : TriEdge) :
    rot.symm e = ⟨latticeRot.symm (if e.k = 1 then e.v else e.v + latticeDir e.k), e.k + 2⟩ :=
  (rfl)

/-- `ρ` sends the edges of direction `k` to direction `k + 1`. -/
@[simp] theorem rot_k (e : TriEdge) : (rot e).k = e.k + 1 := (rfl)

/-- The initial vertex of `ρ e` is `ρ v` for `k = 1` and `ρ (v + e_k)` otherwise. -/
@[simp] theorem rot_v (e : TriEdge) :
    (rot e).v = if e.k = 0 then latticeRot e.v else latticeRot e.target := (rfl)

/-- The final vertex of `ρ e` is `ρ (v + e_k)` for `k = 1` and `ρ v` otherwise, so `ρ e` is the
segment between `ρ v` and `ρ (v + e_k)`. -/
@[simp] theorem target_rot (e : TriEdge) :
    (rot e).target = if e.k = 0 then latticeRot e.target else latticeRot e.v := by
  obtain ⟨⟨x, y⟩, k⟩ := e
  fin_cases k <;> simp [rot_apply] <;> omega

theorem rot_pow_three : rot ^ 3 = 1 := by
  ext ⟨⟨x, y⟩, k⟩ <;> fin_cases k <;> simp +decide [pow_succ, rot_apply] <;> omega

/-- `ρ` has order three on edges. -/
theorem orderOf_rot : orderOf rot = 3 := by
  refine orderOf_eq_prime rot_pow_three fun h => ?_
  simpa [rot_apply] using congrArg (fun φ : Equiv.Perm TriEdge => (φ ⟨0, 0⟩).k) h

/-- `ρ` commutes with translations up to `ρ` on the translation vector. -/
@[simp] theorem rot_vadd (w : ℤ × ℤ) (e : TriEdge) : rot (w +ᵥ e) = latticeRot w +ᵥ rot e := by
  ext <;> simp [rot_apply] <;> split_ifs <;> simp <;> abel

end TriEdge

namespace TriFace

/-- The rotation `ρ` on faces: `ρ W(v) = W(ρ v - e₁)` and `ρ B(v) = B(ρ v - e₃)`. -/
def rot : Equiv.Perm TriFace where
  toFun f := ⟨latticeRot f.v - if f.isWhite then (1, 0) else (1, 1), f.isWhite⟩
  invFun f := ⟨latticeRot.symm (f.v + if f.isWhite then (1, 0) else (1, 1)), f.isWhite⟩
  left_inv f := by
    obtain ⟨⟨x, y⟩, c⟩ := f
    cases c <;> simp
  right_inv f := by
    obtain ⟨⟨x, y⟩, c⟩ := f
    cases c <;> simp
    all_goals ring

theorem rot_apply (f : TriFace) :
    rot f = ⟨latticeRot f.v - if f.isWhite then (1, 0) else (1, 1), f.isWhite⟩ := (rfl)

theorem rot_symm_apply (f : TriFace) :
    rot.symm f = ⟨latticeRot.symm (f.v + if f.isWhite then (1, 0) else (1, 1)), f.isWhite⟩ :=
  (rfl)

@[simp] theorem rot_mk_true (v : ℤ × ℤ) :
    rot ⟨v, true⟩ = ⟨latticeRot v - (1, 0), true⟩ := (rfl)

@[simp] theorem rot_mk_false (v : ℤ × ℤ) :
    rot ⟨v, false⟩ = ⟨latticeRot v - (1, 1), false⟩ := (rfl)

@[simp] theorem rot_v (f : TriFace) :
    (rot f).v = latticeRot f.v - if f.isWhite then (1, 0) else (1, 1) := (rfl)

/-- `ρ` preserves colours. -/
@[simp] theorem rot_isWhite (f : TriFace) : (rot f).isWhite = f.isWhite := (rfl)

theorem rot_pow_three : rot ^ 3 = 1 := by
  ext ⟨⟨x, y⟩, c⟩ <;> cases c <;> simp [pow_succ, rot_apply] <;> omega

/-- `ρ` has order three on faces. -/
theorem orderOf_rot : orderOf rot = 3 := by
  refine orderOf_eq_prime rot_pow_three fun h => ?_
  simpa [rot_apply] using congrArg (fun φ : Equiv.Perm TriFace => (φ ⟨0, true⟩).v) h

/-- `ρ` commutes with translations up to `ρ` on the translation vector. -/
@[simp] theorem rot_vadd (w : ℤ × ℤ) (f : TriFace) : rot (w +ᵥ f) = latticeRot w +ᵥ rot f := by
  ext <;> simp [rot_apply] <;> split_ifs <;> simp <;> abel

/-- `ρ` maps the vertices of a face onto the vertices of its image. -/
@[simp] theorem vertices_rot (f : TriFace) :
    (rot f).vertices = f.vertices.map latticeRot.toEquiv.toEmbedding := by
  obtain ⟨⟨x, y⟩, c⟩ := f
  ext ⟨p, q⟩
  cases c <;> simp [rot_apply] <;> omega

/-- `ρ` maps the edges of a face onto the edges of its image. -/
@[simp] theorem edges_rot (f : TriFace) :
    (rot f).edges = f.edges.map (TriEdge.rot).toEmbedding := by
  obtain ⟨⟨x, y⟩, c⟩ := f
  ext ⟨⟨p, q⟩, j⟩
  cases c <;> fin_cases j <;> simp [rot_apply, TriEdge.rot_apply, TriEdge.ext_iff] <;> omega

/-- The edge of direction `k` of the image of a face under `ρ` is the image of the edge of
direction `k - 1` of the face. -/
@[simp] theorem edge_rot (f : TriFace) (k : Fin 3) :
    (rot f).edge k = TriEdge.rot (f.edge (k - 1)) := by
  have h : TriEdge.rot (f.edge (k - 1)) ∈ (rot f).edges := by
    rw [edges_rot, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    exact f.edge_mem_edges _
  rwa [mem_edges_iff_edge_eq, TriEdge.rot_k, edge_k, sub_add_cancel] at h

end TriFace

namespace TriEdge

theorem rot_mem_edges_rot {e : TriEdge} {f : TriFace} :
    rot e ∈ (TriFace.rot f).edges ↔ e ∈ f.edges := by
  rw [TriFace.edges_rot, Finset.mem_map_equiv, Equiv.symm_apply_apply]

@[simp] theorem whiteFace_rot (e : TriEdge) : (rot e).whiteFace = TriFace.rot e.whiteFace :=
  (eq_whiteFace_of_mem_edges (rot_mem_edges_rot.2 e.mem_whiteFace_edges) (by simp)).symm

@[simp] theorem blackFace_rot (e : TriEdge) : (rot e).blackFace = TriFace.rot e.blackFace :=
  (eq_blackFace_of_mem_edges (rot_mem_edges_rot.2 e.mem_blackFace_edges) (by simp)).symm

@[simp] theorem faces_rot (e : TriEdge) : (rot e).faces = e.faces.map TriFace.rot.toEmbedding := by
  simp [faces]

end TriEdge

/-- `ρ` maps the six faces at a vertex onto the six faces at its image. -/
theorem vertexFaces_rot (v : ℤ × ℤ) :
    vertexFaces (latticeRot v) = (vertexFaces v).map TriFace.rot.toEmbedding := by
  ext f
  obtain ⟨g, rfl⟩ := TriFace.rot.surjective f
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_vertexFaces, mem_vertexFaces,
    TriFace.vertices_rot, Finset.mem_map_equiv]
  simp

end TauCeti
