/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Iso
public import TauCeti.Combinatorics.PolygonalComplex.SurfaceModel

/-!
# Isomorphisms of polygonal complexes

In a cell complex in the sense of Gallier and Xu, a face is given by its boundary, a cyclically
ordered sequence of oriented edges, and each face `A` comes with its inverse `A⁻¹`, whose boundary
is the reversed sequence of inverse edges. A polygonal complex `PolygonalComplex` records, for each
face, one of these two orientations and one starting point on the boundary. An isomorphism has to
forget both choices: it is an isomorphism of the one-skeletons and a bijection of the faces which
carries the boundary of each face to the boundary of the corresponding face, or to the boundary of
its inverse, up to a cyclic change of starting point.

`PolygonalComplex.Iso` encodes this by a bijection of the side occurrences (`sideEquiv`) and a
record of the faces whose orientation is reversed (`flip`). On a face whose orientation is kept,
consecutive sides go to consecutive sides and each side is attached along the image of its dart;
on a reversed face the cyclic order of the sides is reversed and each side is attached along the
reverse of the image of its dart. Isomorphisms can be inverted and composed.

Everything defined from the incidence structure is invariant under isomorphism. Corners correspond
to corners (`PolygonalComplex.Iso.cornerEquiv`; on a reversed face the two sides of a corner are
exchanged), so the link of a vertex is isomorphic to the link of the corresponding vertex
(`PolygonalComplex.Iso.vertexLinkIso`), corresponding germs have the same degree, and the
surface-link condition, the Euler characteristic and orientability are preserved. A complex
isomorphic to a surface model is a surface model (`SurfaceModel.ofIso`), and an isomorphism of
surface models preserves the boundary darts.

## Main definitions

* `TauCeti.PolygonalComplex.Iso`: isomorphisms of polygonal complexes, with
  `PolygonalComplex.Iso.refl`, `PolygonalComplex.Iso.symm` and `PolygonalComplex.Iso.trans`,
  which satisfy the groupoid laws (`PolygonalComplex.Iso.trans_assoc`,
  `PolygonalComplex.Iso.refl_trans`, `PolygonalComplex.Iso.trans_refl`,
  `PolygonalComplex.Iso.symm_trans_self`, `PolygonalComplex.Iso.self_trans_symm`).
* `TauCeti.PolygonalComplex.Iso.cornerEquiv`: the induced bijection of corners, compatible with
  identities, inverses and composites.
* `TauCeti.PolygonalComplex.Iso.vertexLinkIso`: the induced isomorphisms of vertex links.
* `TauCeti.SurfaceModel.ofIso`: the surface model structure on a complex isomorphic to a surface
  model.

## Main results

* `TauCeti.PolygonalComplex.Iso.sides_faceEquiv`: corresponding faces have the same number of
  sides.
* `TauCeti.PolygonalComplex.Iso.linkDegree_equivE`,
  `TauCeti.PolygonalComplex.Iso.hasSurfaceLink_equivV_iff`: link degrees and the surface-link
  condition are invariant.
* `TauCeti.PolygonalComplex.Iso.eulerChar_eq`, `TauCeti.PolygonalComplex.Iso.isOrientable_iff`:
  the Euler characteristic and orientability are invariant.
* `TauCeti.PolygonalComplex.Iso.equivE_mem_boundaryDarts_iff`,
  `TauCeti.PolygonalComplex.Iso.image_boundaryGerms`: an isomorphism of surface models preserves
  boundary darts and boundary germs; in particular `TauCeti.SurfaceModel.boundaryDarts_ofIso` and
  `TauCeti.SurfaceModel.boundaryGerms_ofIso` describe the boundary of a transported surface model.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definitions 6.1, 6.2 and 6.4.
-/

public section

universe u v w u' v' w' u'' v'' w'' u''' v''' w'''

namespace TauCeti

namespace PolygonalComplex

/-- An isomorphism of polygonal complexes: an isomorphism of the one-skeletons, a bijection of the
faces and a bijection of the side occurrences of corresponding faces, together with the record
`flip` of the faces whose orientation is reversed. On a face whose orientation is kept, the sides
keep their cyclic order and each is attached along the image of its dart. On a reversed face the
cyclic order is reversed and each side is attached along the reverse of the image of its dart.
No starting point of a face is preserved, so a face may also be rotated. -/
structure Iso (C : PolygonalComplex.{u, v, w}) (D : PolygonalComplex.{u', v', w'}) where
  /-- The isomorphism of the one-skeletons. -/
  graph : C.graph.Iso D.graph
  /-- The bijection of faces. -/
  faceEquiv : C.Face ≃ D.Face
  /-- Whether the orientation of a face is reversed. -/
  flip : C.Face → Bool
  /-- The bijection of side occurrences. -/
  sideEquiv : C.Corner ≃ D.Corner
  /-- A side of a face is sent to a side of the corresponding face. -/
  sideEquiv_apply_fst : ∀ c, (sideEquiv c).1 = faceEquiv c.1
  /-- Consecutive sides are sent to consecutive sides, in the reverse order on a reversed face. -/
  sideEquiv_nextCorner : ∀ c, sideEquiv (C.nextCorner c) =
    cond (flip c.1) (D.prevCorner (sideEquiv c)) (D.nextCorner (sideEquiv c))
  /-- A side is attached along the image of its dart, reversed on a reversed face. -/
  outgoing_sideEquiv : ∀ c, D.outgoing (sideEquiv c) =
    cond (flip c.1) (D.graph.rev (graph.equivE (C.outgoing c))) (graph.equivE (C.outgoing c))

namespace Iso

attribute [simp] sideEquiv_apply_fst sideEquiv_nextCorner outgoing_sideEquiv

variable {C : PolygonalComplex.{u, v, w}} {D : PolygonalComplex.{u', v', w'}}
  {K : PolygonalComplex.{u'', v'', w''}} (φ : C.Iso D)

@[simp] theorem sideEquiv_symm_apply_fst (d : D.Corner) :
    (φ.sideEquiv.symm d).1 = φ.faceEquiv.symm d.1 := by
  rw [Equiv.eq_symm_apply, ← φ.sideEquiv_apply_fst, Equiv.apply_symm_apply]

@[simp] theorem sideEquiv_prevCorner (c : C.Corner) : φ.sideEquiv (C.prevCorner c) =
    cond (φ.flip c.1) (D.nextCorner (φ.sideEquiv c)) (D.prevCorner (φ.sideEquiv c)) := by
  have h := φ.sideEquiv_nextCorner (C.prevCorner c)
  rw [nextCorner_prevCorner, prevCorner_fst] at h
  cases hf : φ.flip c.1 <;> simp [hf, h]

@[simp] theorem incoming_sideEquiv (c : C.Corner) : D.incoming (φ.sideEquiv c) =
    cond (φ.flip c.1) (D.graph.rev (φ.graph.equivE (C.outgoing (C.nextCorner c))))
      (φ.graph.equivE (C.incoming c)) := by
  rw [incoming_eq_outgoing_prevCorner]
  cases hf : φ.flip c.1
  · have h := φ.sideEquiv_prevCorner c
    rw [hf, Bool.cond_false] at h
    rw [← h, outgoing_sideEquiv, prevCorner_fst, hf, Bool.cond_false, Bool.cond_false,
      incoming_eq_outgoing_prevCorner]
  · have h := φ.sideEquiv_nextCorner c
    rw [hf, Bool.cond_true] at h
    rw [← h, outgoing_sideEquiv, nextCorner_fst, hf, Bool.cond_true, Bool.cond_true]

/-- The side corresponding to a side along an edge lies along the corresponding edge. -/
theorem toGeomEdge_outgoing_sideEquiv (c : C.Corner) :
    D.graph.toGeomEdge (D.outgoing (φ.sideEquiv c)) =
      φ.graph.geomEdgeEquiv (C.graph.toGeomEdge (C.outgoing c)) := by
  cases hf : φ.flip c.1 <;> simp [hf]

/-- Corresponding faces have the same number of sides. -/
@[simp] theorem sides_faceEquiv (f : C.Face) : D.sides (φ.faceEquiv f) = C.sides f :=
  (Fin.equiv_iff_eq.1 ⟨((Equiv.sigmaSubtype f).symm.trans (φ.sideEquiv.subtypeEquiv fun c => by
    rw [sideEquiv_apply_fst, Equiv.apply_eq_iff_eq])).trans
      (Equiv.sigmaSubtype (φ.faceEquiv f))⟩).symm

@[simp] theorem sides_faceEquiv_symm (g : D.Face) : C.sides (φ.faceEquiv.symm g) = D.sides g := by
  rw [← φ.sides_faceEquiv, Equiv.apply_symm_apply]

/-- An isomorphism of polygonal complexes is determined by its action on the one-skeleton and on
the side occurrences. -/
@[ext] theorem ext {φ ψ : C.Iso D} (hgraph : φ.graph = ψ.graph)
    (hside : φ.sideEquiv = ψ.sideEquiv) : φ = ψ := by
  have hface : φ.faceEquiv = ψ.faceEquiv := Equiv.ext fun f => by
    rw [← φ.sideEquiv_apply_fst ⟨f, ⟨0, C.sides_pos f⟩⟩, hside, ψ.sideEquiv_apply_fst]
  have hflip : φ.flip = ψ.flip := funext fun f => by
    have h := φ.outgoing_sideEquiv ⟨f, ⟨0, C.sides_pos f⟩⟩
    rw [hgraph, hside, ψ.outgoing_sideEquiv] at h
    have hne := D.graph.rev_ne (ψ.graph.equivE (C.outgoing ⟨f, ⟨0, C.sides_pos f⟩⟩))
    generalize φ.flip f = a at h ⊢
    generalize ψ.flip f = b at h ⊢
    cases a <;> cases b <;> first | rfl | exact absurd h hne | exact absurd h.symm hne
  obtain ⟨_, _, _, _, _, _, _⟩ := φ
  obtain ⟨_, _, _, _, _, _, _⟩ := ψ
  congr

/-! ### Identity, inverse and composite -/

/-- The identity isomorphism of a polygonal complex. -/
@[refl] def refl (C : PolygonalComplex.{u, v, w}) : C.Iso C where
  graph := .refl _
  faceEquiv := .refl _
  flip _ := false
  sideEquiv := .refl _
  sideEquiv_apply_fst _ := rfl
  sideEquiv_nextCorner _ := rfl
  outgoing_sideEquiv _ := by simp

@[simp] theorem refl_graph (C : PolygonalComplex.{u, v, w}) :
    (refl C).graph = .refl C.graph := (rfl)

@[simp] theorem refl_faceEquiv (C : PolygonalComplex.{u, v, w}) :
    (refl C).faceEquiv = .refl C.Face := (rfl)

@[simp] theorem refl_flip (C : PolygonalComplex.{u, v, w}) (f : C.Face) :
    (refl C).flip f = false := (rfl)

@[simp] theorem refl_sideEquiv (C : PolygonalComplex.{u, v, w}) :
    (refl C).sideEquiv = .refl C.Corner := (rfl)

/-- The inverse of an isomorphism of polygonal complexes. It reverses the orientation of the faces
corresponding to those whose orientation the isomorphism reverses. -/
@[symm] def symm : D.Iso C where
  graph := φ.graph.symm
  faceEquiv := φ.faceEquiv.symm
  flip g := φ.flip (φ.faceEquiv.symm g)
  sideEquiv := φ.sideEquiv.symm
  sideEquiv_apply_fst := φ.sideEquiv_symm_apply_fst
  sideEquiv_nextCorner d := by
    obtain ⟨c, rfl⟩ := φ.sideEquiv.surjective d
    rw [Equiv.symm_apply_eq]
    cases hf : φ.flip c.1 <;> simp [hf]
  outgoing_sideEquiv d := by
    obtain ⟨c, rfl⟩ := φ.sideEquiv.surjective d
    cases hf : φ.flip c.1 <;> simp [hf]

@[simp] theorem symm_graph : φ.symm.graph = φ.graph.symm := (rfl)

@[simp] theorem symm_faceEquiv : φ.symm.faceEquiv = φ.faceEquiv.symm := (rfl)

@[simp] theorem symm_flip (g : D.Face) : φ.symm.flip g = φ.flip (φ.faceEquiv.symm g) := (rfl)

@[simp] theorem symm_sideEquiv : φ.symm.sideEquiv = φ.sideEquiv.symm := (rfl)

@[simp] theorem symm_symm : φ.symm.symm = φ := ext (by simp) (by simp)

@[simp] theorem sideEquiv_symm_nextCorner (d : D.Corner) : φ.sideEquiv.symm (D.nextCorner d) =
    cond (φ.flip (φ.faceEquiv.symm d.1)) (C.prevCorner (φ.sideEquiv.symm d))
      (C.nextCorner (φ.sideEquiv.symm d)) :=
  φ.symm.sideEquiv_nextCorner d

@[simp] theorem sideEquiv_symm_prevCorner (d : D.Corner) : φ.sideEquiv.symm (D.prevCorner d) =
    cond (φ.flip (φ.faceEquiv.symm d.1)) (C.nextCorner (φ.sideEquiv.symm d))
      (C.prevCorner (φ.sideEquiv.symm d)) :=
  φ.symm.sideEquiv_prevCorner d

@[simp] theorem outgoing_sideEquiv_symm (d : D.Corner) : C.outgoing (φ.sideEquiv.symm d) =
    cond (φ.flip (φ.faceEquiv.symm d.1)) (C.graph.rev (φ.graph.equivE.symm (D.outgoing d)))
      (φ.graph.equivE.symm (D.outgoing d)) := by
  simpa using φ.symm.outgoing_sideEquiv d

@[simp] theorem incoming_sideEquiv_symm (d : D.Corner) : C.incoming (φ.sideEquiv.symm d) =
    cond (φ.flip (φ.faceEquiv.symm d.1))
      (C.graph.rev (φ.graph.equivE.symm (D.outgoing (D.nextCorner d))))
      (φ.graph.equivE.symm (D.incoming d)) := by
  simpa using φ.symm.incoming_sideEquiv d

/-- The composite of two isomorphisms of polygonal complexes, `φ` followed by `ψ`. It reverses the
orientation of a face when exactly one of the two isomorphisms does. -/
@[trans] def trans (ψ : D.Iso K) : C.Iso K where
  graph := φ.graph.trans ψ.graph
  faceEquiv := φ.faceEquiv.trans ψ.faceEquiv
  flip f := φ.flip f ^^ ψ.flip (φ.faceEquiv f)
  sideEquiv := φ.sideEquiv.trans ψ.sideEquiv
  sideEquiv_apply_fst c := by simp
  sideEquiv_nextCorner c := by
    cases hφ : φ.flip c.1 <;> cases hψ : ψ.flip (φ.faceEquiv c.1) <;> simp [hφ, hψ]
  outgoing_sideEquiv c := by
    cases hφ : φ.flip c.1 <;> cases hψ : ψ.flip (φ.faceEquiv c.1) <;> simp [hφ, hψ]

@[simp] theorem trans_graph (ψ : D.Iso K) : (φ.trans ψ).graph = φ.graph.trans ψ.graph := (rfl)

@[simp] theorem trans_faceEquiv (ψ : D.Iso K) :
    (φ.trans ψ).faceEquiv = φ.faceEquiv.trans ψ.faceEquiv := (rfl)

@[simp] theorem trans_flip (ψ : D.Iso K) (f : C.Face) :
    (φ.trans ψ).flip f = (φ.flip f ^^ ψ.flip (φ.faceEquiv f)) := (rfl)

@[simp] theorem trans_sideEquiv (ψ : D.Iso K) :
    (φ.trans ψ).sideEquiv = φ.sideEquiv.trans ψ.sideEquiv := (rfl)

@[simp] theorem refl_symm (C : PolygonalComplex.{u, v, w}) : (refl C).symm = refl C :=
  ext (by simp) (by simp)

@[simp] theorem symm_trans (ψ : D.Iso K) : (φ.trans ψ).symm = ψ.symm.trans φ.symm :=
  ext (by simp) (by simp)

@[simp] theorem refl_trans : (refl C).trans φ = φ := ext (by simp) (by simp)

@[simp] theorem trans_refl : φ.trans (refl D) = φ := ext (by simp) (by simp)

@[simp] theorem symm_trans_self : φ.symm.trans φ = refl D := ext (by simp) (by simp)

@[simp] theorem self_trans_symm : φ.trans φ.symm = refl C := ext (by simp) (by simp)

theorem trans_assoc {L : PolygonalComplex.{u''', v''', w'''}} (ψ : D.Iso K) (χ : K.Iso L) :
    (φ.trans ψ).trans χ = φ.trans (ψ.trans χ) :=
  ext (SerreGraph.Iso.trans_assoc ..) (Equiv.trans_assoc ..)

/-! ### Corners -/

/-- The bijection of corners induced by an isomorphism. On a face whose orientation is kept, the
corner at the start of a side corresponds to the corner at the start of the corresponding side;
on a reversed face it corresponds to the corner at its end. -/
def cornerEquiv : C.Corner ≃ D.Corner where
  toFun c := cond (φ.flip c.1) (D.nextCorner (φ.sideEquiv c)) (φ.sideEquiv c)
  invFun d := φ.sideEquiv.symm (cond (φ.flip (φ.faceEquiv.symm d.1)) (D.prevCorner d) d)
  left_inv c := by cases hf : φ.flip c.1 <;> simp [hf]
  right_inv d := by cases hf : φ.flip (φ.faceEquiv.symm d.1) <;> simp [hf]

theorem cornerEquiv_apply (c : C.Corner) :
    φ.cornerEquiv c = cond (φ.flip c.1) (D.nextCorner (φ.sideEquiv c)) (φ.sideEquiv c) := (rfl)

theorem cornerEquiv_symm_apply (d : D.Corner) : φ.cornerEquiv.symm d =
    φ.sideEquiv.symm (cond (φ.flip (φ.faceEquiv.symm d.1)) (D.prevCorner d) d) := (rfl)

@[simp] theorem cornerEquiv_apply_fst (c : C.Corner) : (φ.cornerEquiv c).1 = φ.faceEquiv c.1 := by
  cases hf : φ.flip c.1 <;> simp [cornerEquiv_apply, hf]

/-- Consecutive corners correspond to consecutive corners, in the reverse order on a reversed
face. -/
@[simp] theorem cornerEquiv_nextCorner (c : C.Corner) : φ.cornerEquiv (C.nextCorner c) =
    cond (φ.flip c.1) (D.prevCorner (φ.cornerEquiv c)) (D.nextCorner (φ.cornerEquiv c)) := by
  cases hf : φ.flip c.1 <;> simp [cornerEquiv_apply, hf]

@[simp] theorem cornerEquiv_prevCorner (c : C.Corner) : φ.cornerEquiv (C.prevCorner c) =
    cond (φ.flip c.1) (D.nextCorner (φ.cornerEquiv c)) (D.prevCorner (φ.cornerEquiv c)) := by
  cases hf : φ.flip c.1 <;> simp [cornerEquiv_apply, hf]

@[simp] theorem cornerEquiv_refl (C : PolygonalComplex.{u, v, w}) :
    (refl C).cornerEquiv = .refl C.Corner :=
  Equiv.ext fun _ => rfl

@[simp] theorem cornerEquiv_symm : φ.symm.cornerEquiv = φ.cornerEquiv.symm :=
  Equiv.ext fun d => by
    rw [Equiv.eq_symm_apply]
    obtain ⟨c, rfl⟩ := φ.sideEquiv.surjective d
    cases hf : φ.flip c.1 <;> simp [cornerEquiv_apply, hf]

@[simp] theorem cornerEquiv_trans (ψ : D.Iso K) :
    (φ.trans ψ).cornerEquiv = φ.cornerEquiv.trans ψ.cornerEquiv :=
  Equiv.ext fun c => by
    cases hφ : φ.flip c.1 <;> cases hψ : ψ.flip (φ.faceEquiv c.1) <;>
      simp [cornerEquiv_apply, hφ, hψ]

@[simp] theorem cornerEquiv_symm_apply_fst (d : D.Corner) :
    (φ.cornerEquiv.symm d).1 = φ.faceEquiv.symm d.1 := by
  rw [← cornerEquiv_symm]
  exact φ.symm.cornerEquiv_apply_fst d

@[simp] theorem cornerEquiv_symm_nextCorner (d : D.Corner) :
    φ.cornerEquiv.symm (D.nextCorner d) = cond (φ.flip (φ.faceEquiv.symm d.1))
      (C.prevCorner (φ.cornerEquiv.symm d)) (C.nextCorner (φ.cornerEquiv.symm d)) := by
  rw [← cornerEquiv_symm]
  exact φ.symm.cornerEquiv_nextCorner d

@[simp] theorem cornerEquiv_symm_prevCorner (d : D.Corner) :
    φ.cornerEquiv.symm (D.prevCorner d) = cond (φ.flip (φ.faceEquiv.symm d.1))
      (C.nextCorner (φ.cornerEquiv.symm d)) (C.prevCorner (φ.cornerEquiv.symm d)) := by
  rw [← cornerEquiv_symm]
  exact φ.symm.cornerEquiv_prevCorner d

/-- The outgoing side of the corresponding corner: the image of the outgoing side, or the reverse
of the image of the incoming side on a reversed face. -/
@[simp] theorem outgoing_cornerEquiv (c : C.Corner) : D.outgoing (φ.cornerEquiv c) =
    cond (φ.flip c.1) (D.graph.rev (φ.graph.equivE (C.incoming c)))
      (φ.graph.equivE (C.outgoing c)) := by
  cases hf : φ.flip c.1
  · simp [cornerEquiv_apply, hf]
  · have h := φ.sideEquiv_prevCorner c
    rw [hf, Bool.cond_true] at h
    rw [cornerEquiv_apply, hf, Bool.cond_true, Bool.cond_true, ← h, outgoing_sideEquiv,
      prevCorner_fst, hf, Bool.cond_true, incoming_eq_outgoing_prevCorner]

/-- The incoming side of the corresponding corner: the image of the incoming side, or the reverse
of the image of the outgoing side on a reversed face. -/
@[simp] theorem incoming_cornerEquiv (c : C.Corner) : D.incoming (φ.cornerEquiv c) =
    cond (φ.flip c.1) (D.graph.rev (φ.graph.equivE (C.outgoing c)))
      (φ.graph.equivE (C.incoming c)) := by
  cases hf : φ.flip c.1 <;> simp [cornerEquiv_apply, hf]

/-- Corresponding corners sit at corresponding vertices. -/
@[simp] theorem cornerVertex_cornerEquiv (c : C.Corner) :
    D.cornerVertex (φ.cornerEquiv c) = φ.graph.equivV (C.cornerVertex c) := by
  rw [← src_outgoing, outgoing_cornerEquiv]
  cases hf : φ.flip c.1 <;> simp

@[simp] theorem outgoing_cornerEquiv_symm (d : D.Corner) : C.outgoing (φ.cornerEquiv.symm d) =
    cond (φ.flip (φ.faceEquiv.symm d.1)) (C.graph.rev (φ.graph.equivE.symm (D.incoming d)))
      (φ.graph.equivE.symm (D.outgoing d)) := by
  simpa using φ.symm.outgoing_cornerEquiv d

@[simp] theorem incoming_cornerEquiv_symm (d : D.Corner) : C.incoming (φ.cornerEquiv.symm d) =
    cond (φ.flip (φ.faceEquiv.symm d.1)) (C.graph.rev (φ.graph.equivE.symm (D.outgoing d)))
      (φ.graph.equivE.symm (D.incoming d)) := by
  simpa using φ.symm.incoming_cornerEquiv d

@[simp] theorem cornerVertex_cornerEquiv_symm (d : D.Corner) :
    C.cornerVertex (φ.cornerEquiv.symm d) = φ.graph.equivV.symm (D.cornerVertex d) := by
  simpa using φ.symm.cornerVertex_cornerEquiv d

/-! ### Vertex links -/

/-- The corners at a vertex correspond to the corners at the corresponding vertex. -/
def cornerAtEquiv (v : C.graph.V) :
    {c : C.Corner // C.cornerVertex c = v} ≃
      {d : D.Corner // D.cornerVertex d = φ.graph.equivV v} :=
  φ.cornerEquiv.subtypeEquiv fun c => by rw [cornerVertex_cornerEquiv, Equiv.apply_eq_iff_eq]

@[simp] theorem cornerAtEquiv_apply_val {v : C.graph.V}
    (c : {c : C.Corner // C.cornerVertex c = v}) :
    (φ.cornerAtEquiv v c).1 = φ.cornerEquiv c.1 := (rfl)

@[simp] theorem cornerAtEquiv_symm_apply_val {v : C.graph.V}
    (d : {d : D.Corner // D.cornerVertex d = φ.graph.equivV v}) :
    ((φ.cornerAtEquiv v).symm d).1 = φ.cornerEquiv.symm d.1 := (rfl)

/-- The germs at a vertex correspond to the germs at the corresponding vertex. -/
private def germEquiv (v : C.graph.V) :
    (C.vertexLink v).V ≃ (D.vertexLink (φ.graph.equivV v)).V :=
  φ.graph.equivE.subtypeEquiv fun e => by rw [φ.graph.map_src, Equiv.apply_eq_iff_eq]

private theorem germEquiv_apply_val {v : C.graph.V} (e : (C.vertexLink v).V) :
    (φ.germEquiv v e).1 = φ.graph.equivE e.1 := rfl

/-- The darts of the link of a vertex correspond to the darts of the link of the corresponding
vertex: the link edge of a corner to that of the corresponding corner, with its two directions
exchanged on a reversed face. -/
private def linkDartEquiv (v : C.graph.V) :
    (C.vertexLink v).E ≃ (D.vertexLink (φ.graph.equivV v)).E :=
  (φ.cornerAtEquiv v).prodShear fun c =>
    Function.Involutive.toPerm (· ^^ φ.flip c.1.1) fun _ => by simp

private theorem linkDartEquiv_apply {v : C.graph.V} (c : {c : C.Corner // C.cornerVertex c = v})
    (b : Bool) : φ.linkDartEquiv v (c, b) = (φ.cornerAtEquiv v c, b ^^ φ.flip c.1.1) := rfl

/-- An isomorphism of polygonal complexes induces an isomorphism from the link of a vertex to the
link of the corresponding vertex. It maps a germ to its image and the link edge of a corner to the
link edge of the corresponding corner, exchanging its two directions on a reversed face. -/
def vertexLinkIso (v : C.graph.V) : (C.vertexLink v).Iso (D.vertexLink (φ.graph.equivV v)) where
  equivV := φ.germEquiv v
  equivE := φ.linkDartEquiv v
  map_src d := by
    obtain ⟨c, b⟩ := d
    apply Subtype.ext
    rw [linkDartEquiv_apply, germEquiv_apply_val]
    cases b <;> cases hf : φ.flip c.1.1 <;> simp [hf]
  map_rev d := Prod.ext rfl (Bool.not_xor _ _)

@[simp] theorem vertexLinkIso_equivV_apply_val {v : C.graph.V} (e : (C.vertexLink v).V) :
    ((φ.vertexLinkIso v).equivV e).1 = φ.graph.equivE e.1 := (rfl)

@[simp] theorem vertexLinkIso_equivE_apply {v : C.graph.V} (d : (C.vertexLink v).E) :
    (φ.vertexLinkIso v).equivE d = (φ.cornerAtEquiv v d.1, d.2 ^^ φ.flip d.1.1.1) := (rfl)

@[simp] theorem vertexLinkIso_equivV_symm_apply_val {v : C.graph.V}
    (e : (D.vertexLink (φ.graph.equivV v)).V) :
    ((φ.vertexLinkIso v).equivV.symm e).1 = φ.graph.equivE.symm e.1 := (rfl)

@[simp] theorem vertexLinkIso_equivE_symm_apply {v : C.graph.V}
    (d : (D.vertexLink (φ.graph.equivV v)).E) : (φ.vertexLinkIso v).equivE.symm d =
      ((φ.cornerAtEquiv v).symm d.1, d.2 ^^ φ.flip (φ.faceEquiv.symm d.1.1.1)) :=
  Prod.ext rfl (congrArg (d.2 ^^ φ.flip ·) (by simp))

/-- Corresponding germs have the same degree in their links. -/
@[simp] theorem linkDegree_equivE (e : C.graph.E) :
    D.linkDegree (φ.graph.equivE e) = C.linkDegree e := by
  rw [D.linkDegree_eq_card_of_src_eq (φ.graph.map_src e), C.linkDegree_eq_card_of_src_eq rfl]
  refine (Nat.card_congr ((φ.vertexLinkIso _).equivE.subtypeEquiv fun d => ?_)).symm
  rw [(φ.vertexLinkIso _).map_src, vertexLinkIso_equivV_apply_val, Equiv.apply_eq_iff_eq]

@[simp] theorem linkDegree_equivE_symm (e : D.graph.E) :
    C.linkDegree (φ.graph.equivE.symm e) = D.linkDegree e := by
  rw [← φ.linkDegree_equivE, Equiv.apply_symm_apply]

/-- A vertex has a surface link exactly when the corresponding vertex has one. -/
@[simp] theorem hasSurfaceLink_equivV_iff (v : C.graph.V) :
    D.HasSurfaceLink (φ.graph.equivV v) ↔ C.HasSurfaceLink v := by
  have hsrc (e : C.graph.E) :
      D.graph.src (φ.graph.equivE e) = φ.graph.equivV v ↔ C.graph.src e = v := by
    rw [φ.graph.map_src, Equiv.apply_eq_iff_eq]
  rw [hasSurfaceLink_iff, hasSurfaceLink_iff, (φ.vertexLinkIso v).connected_iff,
    ← (φ.vertexLinkIso v).equivE.finite_iff]
  simp only [← φ.graph.equivE.forall_congr_right, ← φ.graph.equivE.exists_congr_right, hsrc,
    linkDegree_equivE, ne_eq, EmbeddingLike.apply_eq_iff_eq]

@[simp] theorem hasSurfaceLink_equivV_symm_iff (v : D.graph.V) :
    C.HasSurfaceLink (φ.graph.equivV.symm v) ↔ D.HasSurfaceLink v := by
  rw [← φ.hasSurfaceLink_equivV_iff, Equiv.apply_symm_apply]

/-! ### Euler characteristic and orientability -/

/-- Isomorphic polygonal complexes have the same Euler characteristic. -/
theorem eulerChar_eq (φ : C.Iso D) : D.eulerChar = C.eulerChar := by
  rw [eulerChar_def, eulerChar_def, Nat.card_congr φ.graph.equivV,
    Nat.card_congr φ.graph.geomEdgeEquiv, Nat.card_congr φ.faceEquiv]

/-- An orientation of the faces is transported along an isomorphism by reversing it on the faces
whose orientation the isomorphism reverses; corresponding sides are then traversed along
corresponding darts. -/
theorem orientedSide_sideEquiv (σ : C.Face → Bool) (c : C.Corner) :
    D.orientedSide (fun g => σ (φ.faceEquiv.symm g) ^^ φ.flip (φ.faceEquiv.symm g))
      (φ.sideEquiv c) = φ.graph.equivE (C.orientedSide σ c) := by
  cases hσ : σ c.1 <;> cases hf : φ.flip c.1 <;> simp [hσ, hf]

private theorem isOrientable_of_isOrientable (φ : C.Iso D) (h : C.IsOrientable) :
    D.IsOrientable := by
  obtain ⟨σ, hσ⟩ := C.isOrientable_iff.1 h
  refine D.isOrientable_iff.2
    ⟨fun g => σ (φ.faceEquiv.symm g) ^^ φ.flip (φ.faceEquiv.symm g),
      fun d d' hne hgeom => ?_⟩
  obtain ⟨c, rfl⟩ := φ.sideEquiv.surjective d
  obtain ⟨c', rfl⟩ := φ.sideEquiv.surjective d'
  rw [toGeomEdge_outgoing_sideEquiv, toGeomEdge_outgoing_sideEquiv,
    EmbeddingLike.apply_eq_iff_eq] at hgeom
  rw [orientedSide_sideEquiv, orientedSide_sideEquiv,
    hσ c c' (fun h => hne (congrArg _ h)) hgeom, φ.graph.map_rev]

/-- Isomorphic polygonal complexes are orientable together. -/
theorem isOrientable_iff (φ : C.Iso D) : D.IsOrientable ↔ C.IsOrientable :=
  ⟨φ.symm.isOrientable_of_isOrientable, φ.isOrientable_of_isOrientable⟩

end Iso

end PolygonalComplex

/-! ### Surface models -/

namespace SurfaceModel

variable {D : PolygonalComplex.{u', v', w'}}

/-- A polygonal complex isomorphic to a surface model is a surface model. It is reducible, so that
its underlying complex is seen to be the given one. -/
abbrev ofIso (S : SurfaceModel.{u, v, w}) (φ : S.toPolygonalComplex.Iso D) :
    SurfaceModel.{u', v', w'} where
  toPolygonalComplex := D
  finite_face := Finite.of_equiv _ φ.faceEquiv
  connected := φ.graph.connected_iff.2 S.connected
  hasSurfaceLink v := by
    rw [← φ.graph.equivV.apply_symm_apply v, φ.hasSurfaceLink_equivV_iff]
    exact S.hasSurfaceLink _

@[simp] theorem toPolygonalComplex_ofIso (S : SurfaceModel.{u, v, w})
    (φ : S.toPolygonalComplex.Iso D) : (S.ofIso φ).toPolygonalComplex = D := (rfl)

end SurfaceModel

namespace PolygonalComplex.Iso

variable {S : SurfaceModel.{u, v, w}} {T : SurfaceModel.{u', v', w'}}
  (φ : S.toPolygonalComplex.Iso T.toPolygonalComplex)

/-- An isomorphism of surface models maps boundary darts to boundary darts, and only those. -/
@[simp] theorem equivE_mem_boundaryDarts_iff {e : S.graph.E} :
    φ.graph.equivE e ∈ T.boundaryDarts ↔ e ∈ S.boundaryDarts := by
  rw [← SurfaceModel.linkDegree_eq_one_iff_mem_boundaryDarts,
    ← SurfaceModel.linkDegree_eq_one_iff_mem_boundaryDarts, φ.linkDegree_equivE]

@[simp] theorem equivE_symm_mem_boundaryDarts_iff {e : T.graph.E} :
    φ.graph.equivE.symm e ∈ S.boundaryDarts ↔ e ∈ T.boundaryDarts := by
  rw [← φ.equivE_mem_boundaryDarts_iff, Equiv.apply_symm_apply]

/-- An isomorphism of surface models maps the boundary darts onto the boundary darts. -/
theorem image_boundaryDarts : φ.graph.equivE '' S.boundaryDarts = T.boundaryDarts := by
  ext e
  obtain ⟨e, rfl⟩ := φ.graph.equivE.surjective e
  simp

/-- An isomorphism of surface models maps the boundary germs at a vertex onto the boundary germs at
the corresponding vertex. -/
theorem image_boundaryGerms (v : S.graph.V) :
    φ.graph.equivE '' S.boundaryGerms v = T.boundaryGerms (φ.graph.equivV v) := by
  ext e
  obtain ⟨e, rfl⟩ := φ.graph.equivE.surjective e
  simp

end PolygonalComplex.Iso

namespace SurfaceModel

variable {D : PolygonalComplex.{u', v', w'}} (S : SurfaceModel.{u, v, w})
  (φ : S.toPolygonalComplex.Iso D)

@[simp] theorem boundaryDarts_ofIso :
    (S.ofIso φ).boundaryDarts = φ.graph.equivE '' S.boundaryDarts :=
  (φ.image_boundaryDarts (T := S.ofIso φ)).symm

theorem mem_boundaryDarts_ofIso_iff {e : D.graph.E} :
    e ∈ (S.ofIso φ).boundaryDarts ↔ φ.graph.equivE.symm e ∈ S.boundaryDarts :=
  (φ.equivE_symm_mem_boundaryDarts_iff (T := S.ofIso φ)).symm

@[simp] theorem boundaryGerms_ofIso (v : D.graph.V) :
    (S.ofIso φ).boundaryGerms v = φ.graph.equivE '' S.boundaryGerms (φ.graph.equivV.symm v) := by
  rw [φ.image_boundaryGerms (T := S.ofIso φ), Equiv.apply_symm_apply]

end SurfaceModel

end TauCeti
