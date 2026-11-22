/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The triangular lattice: vertices, edges, faces and symmetries

The triangular lattice `𝕋` has vertex set `ℤ × ℤ` and positive directions `e₁ = (1, 0)`,
`e₂ = (0, 1)` and `e₃ = (1, 1)` (`latticeDir`, indexed by `Fin 3`, so the direction `k ∈ {1, 2, 3}`
is stored as `k - 1`). Every edge has exactly one name `(v, k)`, the segment from `v` to
`v + e_k` (`TriEdge`). The faces are the white triangles `W(v) = {v, v + e₁, v + e₃}` and the
black triangles `B(v) = {v, v + e₂, v + e₃}` (`TriFace`); their edges are `TriFace.edges`.

We prove that every edge lies in exactly one white face `TriEdge.whiteFace` and one black face
`TriEdge.blackFace` (`TriFace.mem_edges_iff`), that every face has one edge of each direction,
that two distinct faces share at most one edge, and that exactly six faces contain a vertex.
`ℤ × ℤ` acts freely by translation on edges and faces, and on configurations `TriEdge → Bool`
through Mathlib's `arrowAddAction`. The rotation `ρ(x, y) = (-y, x - y)` (`latticeRotation`) of
order three acts on edges and faces, preserving colours and cycling the directions.

Lozenge tilings are unions of pairs of adjacent faces of this lattice, so these definitions are the
combinatorial setting for lozenge tilings and the dimer model on the dual hexagonal graph. The
conventions follow Aggarwal (2023), Section 1.2.
-/

public section

open scoped Pointwise

namespace TauCeti

/-! ### Directions and the rotation -/

/-- The positive directions `e₁ = (1,0)`, `e₂ = (0,1)`, `e₃ = (1,1)` of the triangular lattice on
`ℤ × ℤ`. The direction `k ∈ {1, 2, 3}` is stored as the index `k - 1 : Fin 3`. -/
def latticeDir : Fin 3 → ℤ × ℤ := ![(1, 0), (0, 1), (1, 1)]

/-- The direction `e₁ = (1, 0)`. -/
@[simp] theorem latticeDir_zero : latticeDir 0 = (1, 0) := (rfl)
/-- The direction `e₂ = (0, 1)`. -/
@[simp] theorem latticeDir_one : latticeDir 1 = (0, 1) := (rfl)
/-- The direction `e₃ = (1, 1)`. -/
@[simp] theorem latticeDir_two : latticeDir 2 = (1, 1) := (rfl)

/-- The rotation `ρ(x, y) = (-y, x - y)` of the triangular lattice, of order three. -/
def latticeRotation : ℤ × ℤ ≃+ ℤ × ℤ where
  toFun u := (-u.2, u.1 - u.2)
  invFun u := (u.2 - u.1, -u.1)
  left_inv u := by ext <;> simp
  right_inv u := by ext <;> simp
  map_add' u u' := by ext <;> simp <;> abel

/-- The rotation sends `(x, y)` to `(-y, x - y)`. -/
@[simp] theorem latticeRotation_apply (u : ℤ × ℤ) : latticeRotation u = (-u.2, u.1 - u.2) := (rfl)

/-- The inverse rotation sends `(x, y)` to `(y - x, -x)`. -/
@[simp] theorem latticeRotation_symm_apply (u : ℤ × ℤ) :
    latticeRotation.symm u = (u.2 - u.1, -u.1) := (rfl)

/-- The rotation has order three. -/
theorem latticeRotation_latticeRotation_latticeRotation (u : ℤ × ℤ) :
    latticeRotation (latticeRotation (latticeRotation u)) = u := by
  ext
  · simp
  · simp
    abel

/-- `ρ e₁ = e₂`, `ρ e₂ = -e₃` and `ρ e₃ = -e₁`. -/
theorem latticeRotation_latticeDir :
    latticeRotation (latticeDir 0) = latticeDir 1 ∧
      latticeRotation (latticeDir 1) = -latticeDir 2 ∧
      latticeRotation (latticeDir 2) = -latticeDir 0 := by
  simp

/-! ### Edges -/

/-- An edge of the triangular lattice: the segment from `v` to `v + latticeDir k`. Every edge has
exactly one such name. -/
@[ext]
structure TriEdge where
  /-- The initial vertex. -/
  v : ℤ × ℤ
  /-- The direction, `0, 1, 2` for the directions `e₁, e₂, e₃`. -/
  k : Fin 3
  deriving DecidableEq

namespace TriEdge

/-- The final vertex `v + e_k` of an edge. -/
def target (e : TriEdge) : ℤ × ℤ := e.v + latticeDir e.k

/-- The final vertex of `(v, k)` is `v + e_k`. -/
theorem target_def (e : TriEdge) : e.target = e.v + latticeDir e.k := (rfl)

/-- `ℤ²` acts on edges by translation, `w +ᵥ (v, k) = (w + v, k)`. -/
instance instAddActionTriEdge : AddAction (ℤ × ℤ) TriEdge where
  vadd w e := ⟨w + e.v, e.k⟩
  zero_vadd e := TriEdge.ext (zero_add e.v) rfl
  add_vadd w w' e := TriEdge.ext (add_assoc w w' e.v) rfl

/-- Translation moves the initial vertex of an edge. -/
@[simp] theorem vadd_v (w : ℤ × ℤ) (e : TriEdge) : (w +ᵥ e).v = w + e.v := rfl

/-- Translations preserve directions. -/
@[simp] theorem vadd_k (w : ℤ × ℤ) (e : TriEdge) : (w +ᵥ e).k = e.k := rfl

/-- Translation moves the final vertex of an edge. -/
@[simp] theorem vadd_target (w : ℤ × ℤ) (e : TriEdge) : (w +ᵥ e).target = w + e.target := by
  simp [target, add_assoc]

/-- Translations act freely on edges. -/
instance instIsCancelVAddTriEdge : IsCancelVAdd (ℤ × ℤ) TriEdge where
  left_cancel' w e e' h :=
    TriEdge.ext (by simpa using congrArg TriEdge.v h) (by simpa using congrArg TriEdge.k h)
  right_cancel' w w' e h := by simpa using congrArg TriEdge.v h

/-- The rotation `ρ` on edges: the image of the segment from `v` to `v + e_k` is the segment
between `ρ v` and `ρ (v + e_k)`, which has direction `k + 1`. -/
def rotate (e : TriEdge) : TriEdge :=
  ⟨latticeRotation e.v - ![0, (1, 1), (1, 0)] e.k, e.k + 1⟩

/-- The initial vertex of the rotation of an edge. -/
@[simp] theorem rotate_v (e : TriEdge) :
    e.rotate.v = latticeRotation e.v - ![0, (1, 1), (1, 0)] e.k := (rfl)

/-- `ρ` sends direction `k` to direction `k + 1`. -/
@[simp] theorem rotate_k (e : TriEdge) : e.rotate.k = e.k + 1 := (rfl)

/-- The rotation of an edge joins the rotations of its endpoints. -/
theorem rotate_endpoints (e : TriEdge) :
    ({e.rotate.v, e.rotate.target} : Set (ℤ × ℤ)) =
      {latticeRotation e.v, latticeRotation e.target} := by
  obtain ⟨⟨a, b⟩, k⟩ := e
  fin_cases k <;>
    · simp only [rotate, target]
      ext ⟨x, y⟩
      simp [Prod.ext_iff]
      omega

/-- The rotation has order three on edges. -/
@[simp] theorem rotate_rotate_rotate (e : TriEdge) : e.rotate.rotate.rotate = e := by
  obtain ⟨⟨a, b⟩, k⟩ := e
  fin_cases k <;> simp [rotate, TriEdge.ext_iff, Prod.ext_iff] <;> omega

/-- The rotation is injective on edges. -/
theorem rotate_injective : Function.Injective rotate := fun e e' h => by
  simpa using congrArg (fun e => e.rotate.rotate) h

/-- The rotation commutes with translations up to the rotation of the translation vector. -/
theorem rotate_vadd (w : ℤ × ℤ) (e : TriEdge) :
    (w +ᵥ e).rotate = latticeRotation w +ᵥ e.rotate := by
  simp only [rotate, TriEdge.ext_iff, vadd_v, vadd_k, map_add, and_true]
  abel

end TriEdge

/-! ### Faces -/

/-- A face of the triangular lattice: the white face `W(v) = {v, v + e₁, v + e₃}` when `isWhite`,
the black face `B(v) = {v, v + e₂, v + e₃}` otherwise. -/
@[ext]
structure TriFace where
  /-- The lower-left vertex. -/
  v : ℤ × ℤ
  /-- The colour. -/
  isWhite : Bool
  deriving DecidableEq

namespace TriFace

/-- The three vertices of a face: `v, v + e₁, v + e₃` for `W(v)` and `v, v + e₂, v + e₃`
for `B(v)`. -/
def vertices (f : TriFace) : Finset (ℤ × ℤ) :=
  if f.isWhite then {f.v, f.v + (1, 0), f.v + (1, 1)} else {f.v, f.v + (0, 1), f.v + (1, 1)}

/-- The three edges of a face: `(v,1)`, `(v+e₁,2)`, `(v,3)` for `W(v)` and `(v,2)`, `(v+e₂,1)`,
`(v,3)` for `B(v)`. -/
def edges (f : TriFace) : Finset TriEdge :=
  if f.isWhite then {⟨f.v, 0⟩, ⟨f.v + (1, 0), 1⟩, ⟨f.v, 2⟩}
  else {⟨f.v, 1⟩, ⟨f.v + (0, 1), 0⟩, ⟨f.v, 2⟩}

/-- `ℤ²` acts on faces by translation, `w +ᵥ W(v) = W(w + v)` and `w +ᵥ B(v) = B(w + v)`. -/
instance instAddActionTriFace : AddAction (ℤ × ℤ) TriFace where
  vadd w f := ⟨w + f.v, f.isWhite⟩
  zero_vadd f := TriFace.ext (zero_add f.v) rfl
  add_vadd w w' f := TriFace.ext (add_assoc w w' f.v) rfl

/-- Translation moves the lower-left vertex of a face. -/
@[simp] theorem vadd_v (w : ℤ × ℤ) (f : TriFace) : (w +ᵥ f).v = w + f.v := rfl

/-- Translations preserve colours. -/
@[simp] theorem vadd_isWhite (w : ℤ × ℤ) (f : TriFace) : (w +ᵥ f).isWhite = f.isWhite := rfl

/-- Translations act freely on faces. -/
instance instIsCancelVAddTriFace : IsCancelVAdd (ℤ × ℤ) TriFace where
  left_cancel' w f f' h :=
    TriFace.ext (by simpa using congrArg TriFace.v h) (by simpa using congrArg TriFace.isWhite h)
  right_cancel' w w' f h := by simpa using congrArg TriFace.v h

/-- The rotation `ρ` on faces: `W(v) ↦ W(ρ v - e₁)` and `B(v) ↦ B(ρ v - e₃)`. -/
def rotate (f : TriFace) : TriFace :=
  ⟨latticeRotation f.v - if f.isWhite then (1, 0) else (1, 1), f.isWhite⟩

/-- The base vertex of the rotation of a face. -/
@[simp] theorem rotate_v (f : TriFace) :
    f.rotate.v = latticeRotation f.v - if f.isWhite then (1, 0) else (1, 1) := (rfl)

/-- The rotation preserves colours. -/
@[simp] theorem rotate_isWhite (f : TriFace) : f.rotate.isWhite = f.isWhite := (rfl)

/-- The rotation has order three on faces. -/
@[simp] theorem rotate_rotate_rotate (f : TriFace) : f.rotate.rotate.rotate = f := by
  obtain ⟨⟨a, b⟩, _ | _⟩ := f <;> simp [rotate, TriFace.ext_iff, Prod.ext_iff] <;> omega

/-- The rotation is injective on faces. -/
theorem rotate_injective : Function.Injective rotate := fun f f' h => by
  simpa using congrArg (fun f => f.rotate.rotate) h

/-- The rotation commutes with translations up to the rotation of the translation vector. -/
theorem rotate_vadd (w : ℤ × ℤ) (f : TriFace) :
    (w +ᵥ f).rotate = latticeRotation w +ᵥ f.rotate := by
  simp only [rotate, TriFace.ext_iff, vadd_v, vadd_isWhite, map_add, and_true]
  abel

/-- The vertices of a rotated face are the rotations of its vertices. -/
theorem vertices_rotate (f : TriFace) : f.rotate.vertices = f.vertices.image latticeRotation := by
  obtain ⟨⟨a, b⟩, _ | _⟩ := f <;>
    · ext ⟨x, y⟩
      simp [rotate, vertices, Prod.ext_iff]
      omega

/-- Exactly six faces contain a given vertex `u`: `W(u)`, `W(u - e₁)`, `W(u - e₃)`, `B(u)`,
`B(u - e₂)` and `B(u - e₃)`. -/
theorem mem_vertices_iff (u : ℤ × ℤ) (f : TriFace) :
    u ∈ f.vertices ↔ f ∈ ({⟨u, true⟩, ⟨u - (1, 0), true⟩, ⟨u - (1, 1), true⟩,
      ⟨u, false⟩, ⟨u - (0, 1), false⟩, ⟨u - (1, 1), false⟩} : Finset TriFace) := by
  obtain ⟨⟨a, b⟩, _ | _⟩ := f <;>
    · obtain ⟨x, y⟩ := u
      simp [vertices, TriFace.ext_iff, Prod.ext_iff]
      omega

end TriFace

namespace TriEdge

/-- The white face containing an edge: `W(v)` for `(v, 1)`, `W(v - e₁)` for `(v, 2)` and `W(v)`
for `(v, 3)`. -/
def whiteFace (e : TriEdge) : TriFace := ⟨e.v - ![0, (1, 0), 0] e.k, true⟩

/-- The black face containing an edge: `B(v - e₂)` for `(v, 1)`, `B(v)` for `(v, 2)` and `B(v)`
for `(v, 3)`. -/
def blackFace (e : TriEdge) : TriFace := ⟨e.v - ![(0, 1), 0, 0] e.k, false⟩

/-- The base vertex of the white face of an edge. -/
@[simp] theorem whiteFace_v (e : TriEdge) : e.whiteFace.v = e.v - ![0, (1, 0), 0] e.k := (rfl)

/-- The base vertex of the black face of an edge. -/
@[simp] theorem blackFace_v (e : TriEdge) : e.blackFace.v = e.v - ![(0, 1), 0, 0] e.k := (rfl)

/-- The white face of an edge is white. -/
@[simp] theorem whiteFace_isWhite (e : TriEdge) : e.whiteFace.isWhite = true := (rfl)

/-- The black face of an edge is black. -/
@[simp] theorem blackFace_isWhite (e : TriEdge) : e.blackFace.isWhite = false := (rfl)

/-- The two faces containing an edge are distinct. -/
theorem whiteFace_ne_blackFace (e : TriEdge) : e.whiteFace ≠ e.blackFace :=
  fun h => by simpa using congrArg TriFace.isWhite h

/-- An edge lies in exactly two faces, its white face and its black face. -/
theorem _root_.TauCeti.TriFace.mem_edges_iff (e : TriEdge) (f : TriFace) :
    e ∈ f.edges ↔ f = e.whiteFace ∨ f = e.blackFace := by
  obtain ⟨⟨a, b⟩, k⟩ := e
  obtain ⟨⟨c, d⟩, _ | _⟩ := f <;> fin_cases k <;>
    simp [TriFace.edges, whiteFace, blackFace, TriEdge.ext_iff, TriFace.ext_iff, Prod.ext_iff] <;>
      omega

/-- An edge is an edge of its white face. -/
theorem mem_edges_whiteFace (e : TriEdge) : e ∈ e.whiteFace.edges :=
  (TriFace.mem_edges_iff e _).2 (Or.inl rfl)

/-- An edge is an edge of its black face. -/
theorem mem_edges_blackFace (e : TriEdge) : e ∈ e.blackFace.edges :=
  (TriFace.mem_edges_iff e _).2 (Or.inr rfl)

/-- An edge is determined by its white face and its black face. -/
theorem eq_of_whiteFace_eq_of_blackFace_eq {e e' : TriEdge} (hw : e.whiteFace = e'.whiteFace)
    (hb : e.blackFace = e'.blackFace) : e = e' := by
  obtain ⟨⟨a, b⟩, k⟩ := e
  obtain ⟨⟨c, d⟩, k'⟩ := e'
  fin_cases k <;> fin_cases k' <;>
    simp [whiteFace, blackFace, TriEdge.ext_iff, Prod.ext_iff] at hw hb ⊢ <;> omega

/-- The white face of a translated edge is the translated white face. -/
@[simp] theorem whiteFace_vadd (w : ℤ × ℤ) (e : TriEdge) :
    (w +ᵥ e).whiteFace = w +ᵥ e.whiteFace := by
  simp [whiteFace, TriFace.ext_iff, add_sub_assoc]

/-- The black face of a translated edge is the translated black face. -/
@[simp] theorem blackFace_vadd (w : ℤ × ℤ) (e : TriEdge) :
    (w +ᵥ e).blackFace = w +ᵥ e.blackFace := by
  simp [blackFace, TriFace.ext_iff, add_sub_assoc]

/-- The white face of a rotated edge is the rotated white face. -/
theorem whiteFace_rotate (e : TriEdge) :
    e.rotate.whiteFace = e.whiteFace.rotate := by
  obtain ⟨⟨a, b⟩, k⟩ := e
  fin_cases k
  all_goals simp [rotate, whiteFace, TriFace.rotate, TriFace.ext_iff, Prod.ext_iff]
  omega

/-- The black face of a rotated edge is the rotated black face. -/
theorem blackFace_rotate (e : TriEdge) :
    e.rotate.blackFace = e.blackFace.rotate := by
  obtain ⟨⟨a, b⟩, k⟩ := e
  fin_cases k
  all_goals simp [rotate, blackFace, TriFace.rotate, TriFace.ext_iff, Prod.ext_iff]
  omega

end TriEdge

namespace TriFace

/-- Every face has exactly three edges. -/
theorem card_edges (f : TriFace) : f.edges.card = 3 := by
  obtain ⟨⟨a, b⟩, _ | _⟩ := f <;> simp [edges, TriEdge.ext_iff]

/-- The edge of direction `k` of a face. -/
def edge (f : TriFace) (k : Fin 3) : TriEdge :=
  ⟨f.v + (if f.isWhite then ![0, (1, 0), 0] else ![(0, 1), 0, 0]) k, k⟩

/-- The initial vertex of the edge of direction `k` of a face. -/
@[simp] theorem edge_v (f : TriFace) (k : Fin 3) :
    (f.edge k).v = f.v + (if f.isWhite then ![0, (1, 0), 0] else ![(0, 1), 0, 0]) k := (rfl)

/-- The edge of direction `k` of a face has direction `k`. -/
@[simp] theorem edge_k (f : TriFace) (k : Fin 3) : (f.edge k).k = k := (rfl)

/-- The edges of a face are its edges of the three directions. -/
theorem mem_edges_iff_eq_edge (f : TriFace) (e : TriEdge) : e ∈ f.edges ↔ e = f.edge e.k := by
  obtain ⟨⟨a, b⟩, _ | _⟩ := f <;> obtain ⟨⟨c, d⟩, k⟩ := e <;> fin_cases k <;>
    simp [edges, edge, TriEdge.ext_iff, Prod.ext_iff]

/-- The edge of direction `k` of a face is one of its edges. -/
@[simp] theorem edge_mem_edges (f : TriFace) (k : Fin 3) : f.edge k ∈ f.edges :=
  (mem_edges_iff_eq_edge f _).2 rfl

/-- Every face has exactly one edge of each direction. -/
theorem existsUnique_mem_edges_k (f : TriFace) (k : Fin 3) : ∃! e, e ∈ f.edges ∧ e.k = k :=
  ⟨f.edge k, ⟨edge_mem_edges f k, rfl⟩, fun e ⟨he, hk⟩ => hk ▸ (mem_edges_iff_eq_edge f e).1 he⟩

/-- Translating a face translates its edges. -/
theorem vadd_mem_edges_vadd (w : ℤ × ℤ) (e : TriEdge) (f : TriFace) :
    w +ᵥ e ∈ (w +ᵥ f).edges ↔ e ∈ f.edges := by
  simp only [mem_edges_iff, TriEdge.whiteFace_vadd, TriEdge.blackFace_vadd, vadd_left_cancel_iff]

/-- Rotating a face rotates its edges. -/
theorem rotate_mem_edges_rotate (e : TriEdge) (f : TriFace) :
    e.rotate ∈ f.rotate.edges ↔ e ∈ f.edges := by
  rw [mem_edges_iff, mem_edges_iff, TriEdge.whiteFace_rotate, TriEdge.blackFace_rotate,
    rotate_injective.eq_iff, rotate_injective.eq_iff]

/-- Faces sharing an edge have opposite colours, unless they are equal. -/
theorem isWhite_ne_of_mem_edges {f g : TriFace} {e : TriEdge} (hf : e ∈ f.edges)
    (hg : e ∈ g.edges) (hfg : f ≠ g) : f.isWhite ≠ g.isWhite := by
  rw [mem_edges_iff] at hf hg
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl <;> simp_all

/-- Two distinct faces share at most one edge. -/
theorem eq_of_mem_edges_of_mem_edges {f g : TriFace} {e e' : TriEdge} (hfg : f ≠ g)
    (hf : e ∈ f.edges) (hg : e ∈ g.edges) (hf' : e' ∈ f.edges) (hg' : e' ∈ g.edges) :
    e = e' := by
  rw [mem_edges_iff] at hf hg hf' hg'
  apply TriEdge.eq_of_whiteFace_eq_of_blackFace_eq <;>
    rcases hf with rfl | rfl <;> rcases hg with h | h <;> rcases hf' with h' | h' <;>
      rcases hg' with h'' | h'' <;> simp_all [TriFace.ext_iff]

end TriFace

/-! ### Configurations -/

/-- `ℤ²` acts on configurations by `(w +ᵥ ω) e = ω (-w +ᵥ e)` (Mathlib's `arrowAddAction`). -/
instance instAddActionConfiguration : AddAction (ℤ × ℤ) (TriEdge → Bool) := arrowAddAction

/-- The value of a translated configuration at an edge. -/
@[simp] theorem vadd_configuration_apply (w : ℤ × ℤ) (ω : TriEdge → Bool) (e : TriEdge) :
    (w +ᵥ ω) e = ω (-w +ᵥ e) := rfl

/-- The edge set of `w +ᵥ ω` is the translate by `w` of the edge set of `ω`. -/
theorem setOf_vadd_configuration (w : ℤ × ℤ) (ω : TriEdge → Bool) :
    {e | (w +ᵥ ω) e = true} = w +ᵥ {e | ω e = true} := by
  ext e
  simp [vadd_configuration_apply, Set.mem_vadd_set_iff_neg_vadd_mem]

end TauCeti
