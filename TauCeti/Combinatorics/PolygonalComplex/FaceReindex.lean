/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.Iso
public import TauCeti.Data.Fin.Basic

/-!
# Changing the starting points and the orientations of the faces of a polygonal complex

A polygonal complex records each face as a closed sequence of darts read from a chosen starting
point in a chosen direction. In a cell complex in the sense of Gallier and Xu neither choice is
part of the data: the boundary of a face is a cyclically ordered sequence, and the inverse `A⁻¹`
of a face `A` with boundary `a₁ ⋯ aₙ` has boundary `aₙ⁻¹ ⋯ a₁⁻¹`.

This file makes the two changes of presentation explicit. `PolygonalComplex.rotateFaces` moves the
starting point of each face, and `PolygonalComplex.reverseFaces` replaces chosen faces by their
inverses. Both give complexes isomorphic to the original one, by an isomorphism which is the
identity on the one-skeleton and on the faces (`PolygonalComplex.rotateFacesIso`,
`PolygonalComplex.reverseFacesIso`). Consequently link degrees, the surface-link condition, the
Euler characteristic and orientability are unchanged. Both changes carry a surface model to a
surface model (`SurfaceModel.rotateFaces`, `SurfaceModel.reverseFaces`) with the same boundary
darts and boundary germs. Shifts of the starting points add up
(`PolygonalComplex.rotateFaces_rotateFaces`), and reversing the same faces twice gives back the
complex (`PolygonalComplex.reverseFaces_reverseFaces_self`).

## Main definitions

* `TauCeti.PolygonalComplex.rotateFaces`, `TauCeti.PolygonalComplex.rotateFacesIso`: cyclic change
  of the starting points of the faces.
* `TauCeti.PolygonalComplex.reverseFaces`, `TauCeti.PolygonalComplex.reverseFacesIso`: reversal of
  the orientations of some faces.
* `TauCeti.SurfaceModel.rotateFaces`, `TauCeti.SurfaceModel.reverseFaces`: the same changes for
  surface models.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definitions 6.1 and 6.4.
-/

public section

universe u v w

namespace TauCeti

namespace PolygonalComplex

variable (C : PolygonalComplex.{u, v, w})

/-! ### Cyclic changes of starting points -/

/-- The polygonal complex obtained by moving the starting point of each face `f` forward by `k f`
sides: its `i`-th side is the `(i + k f)`-th side of `f`, cyclically. The one-skeleton, the faces
and their numbers of sides are unchanged; the definition is exposed so that they are seen to
be. -/
abbrev rotateFaces (k : C.Face → ℕ) : PolygonalComplex.{u, v, w} where
  graph := C.graph
  Face := C.Face
  sides := C.sides
  sides_pos := C.sides_pos
  side f i := C.side f ((finRotate (C.sides f) ^ k f) i)
  tgt_side f i := by
    rw [C.tgt_side, ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_succ', pow_succ]

@[simp] theorem rotateFaces_side (k : C.Face → ℕ) (f : C.Face) (i : Fin (C.sides f)) :
    (C.rotateFaces k).side f i = C.side f ((finRotate (C.sides f) ^ k f) i) := rfl

@[simp] theorem outgoing_rotateFaces (k : C.Face → ℕ) (c : C.Corner) :
    (C.rotateFaces k).outgoing c = C.outgoing ⟨c.1, (finRotate (C.sides c.1) ^ k c.1) c.2⟩ := by
  simp only [outgoing_def]

@[simp] theorem nextCorner_rotateFaces (k : C.Face → ℕ) (c : C.Corner) :
    (C.rotateFaces k).nextCorner c = C.nextCorner c := by
  simp only [nextCorner_def]

@[simp] theorem prevCorner_rotateFaces (k : C.Face → ℕ) (c : C.Corner) :
    (C.rotateFaces k).prevCorner c = C.prevCorner c := by
  simp only [prevCorner_def]

@[simp] theorem cornerVertex_rotateFaces (k : C.Face → ℕ) (c : C.Corner) :
    (C.rotateFaces k).cornerVertex c =
      C.cornerVertex ⟨c.1, (finRotate (C.sides c.1) ^ k c.1) c.2⟩ := by
  rw [← src_outgoing, ← src_outgoing, outgoing_rotateFaces]

/-- Moving the starting points by `0` does not change the complex. -/
@[simp] theorem rotateFaces_zero : C.rotateFaces 0 = C := by
  obtain ⟨⟩ := C
  simp only [rotateFaces, Pi.zero_apply, pow_zero, Equiv.Perm.one_apply]

/-- Moving the starting points by `k` and then by `k'` moves them by `k + k'`. -/
theorem rotateFaces_rotateFaces (k k' : C.Face → ℕ) :
    (C.rotateFaces k).rotateFaces k' = C.rotateFaces (k + k') := by
  simp only [rotateFaces, Pi.add_apply, pow_add, Equiv.Perm.mul_apply]

/-- Moving the starting points of the faces gives an isomorphic complex: the identity on the
one-skeleton and on the faces, keeping all orientations and shifting the sides back. -/
def rotateFacesIso (k : C.Face → ℕ) : C.Iso (C.rotateFaces k) where
  graph := .refl _
  faceEquiv := .refl _
  flip _ := false
  sideEquiv := Equiv.sigmaCongrRight fun f =>
    ((finRotate (C.sides f) ^ k f)⁻¹ : Equiv.Perm (Fin (C.sides f)))
  sideEquiv_apply_fst _ := rfl
  sideEquiv_nextCorner c := by
    obtain ⟨f, i⟩ := c
    simp only [Bool.cond_false, nextCorner_def, Equiv.sigmaCongrRight_apply]
    exact congrArg (Sigma.mk f) (DFunLike.congr_fun
      ((Commute.refl (finRotate (C.sides f))).pow_right (k f)).inv_right.eq.symm i)
  outgoing_sideEquiv c := by
    simp [outgoing_def]

@[simp] theorem rotateFacesIso_graph (k : C.Face → ℕ) :
    (C.rotateFacesIso k).graph = .refl C.graph := (rfl)

@[simp] theorem rotateFacesIso_faceEquiv (k : C.Face → ℕ) :
    (C.rotateFacesIso k).faceEquiv = .refl C.Face := (rfl)

@[simp] theorem rotateFacesIso_flip (k : C.Face → ℕ) (f : C.Face) :
    (C.rotateFacesIso k).flip f = false := (rfl)

@[simp] theorem rotateFacesIso_sideEquiv_apply (k : C.Face → ℕ) (c : C.Corner) :
    (C.rotateFacesIso k).sideEquiv c = ⟨c.1, (finRotate (C.sides c.1) ^ k c.1)⁻¹ c.2⟩ := (rfl)

@[simp] theorem rotateFacesIso_sideEquiv_symm_apply (k : C.Face → ℕ) (c : C.Corner) :
    (C.rotateFacesIso k).sideEquiv.symm c = ⟨c.1, (finRotate (C.sides c.1) ^ k c.1) c.2⟩ := (rfl)

@[simp] theorem rotateFacesIso_cornerEquiv_apply (k : C.Face → ℕ) (c : C.Corner) :
    (C.rotateFacesIso k).cornerEquiv c = ⟨c.1, (finRotate (C.sides c.1) ^ k c.1)⁻¹ c.2⟩ := by
  simp [Iso.cornerEquiv_apply]

@[simp] theorem rotateFacesIso_cornerEquiv_symm_apply (k : C.Face → ℕ) (c : C.Corner) :
    (C.rotateFacesIso k).cornerEquiv.symm c = ⟨c.1, (finRotate (C.sides c.1) ^ k c.1) c.2⟩ := by
  simp [Iso.cornerEquiv_symm_apply]

@[simp] theorem incoming_rotateFaces (k : C.Face → ℕ) (c : C.Corner) :
    (C.rotateFaces k).incoming c = C.incoming ⟨c.1, (finRotate (C.sides c.1) ^ k c.1) c.2⟩ := by
  simpa using (C.rotateFacesIso k).incoming_sideEquiv ⟨c.1, (finRotate (C.sides c.1) ^ k c.1) c.2⟩

/-- Moving the starting points of the faces does not change the degrees of the germs. -/
@[simp] theorem linkDegree_rotateFaces (k : C.Face → ℕ) (e : C.graph.E) :
    (C.rotateFaces k).linkDegree e = C.linkDegree e := by
  simpa using (C.rotateFacesIso k).linkDegree_equivE e

/-- Moving the starting points of the faces does not change which vertices have surface links. -/
@[simp] theorem hasSurfaceLink_rotateFaces_iff (k : C.Face → ℕ) (v : C.graph.V) :
    (C.rotateFaces k).HasSurfaceLink v ↔ C.HasSurfaceLink v := by
  simpa using (C.rotateFacesIso k).hasSurfaceLink_equivV_iff v

/-- Moving the starting points of the faces does not change the Euler characteristic. -/
@[simp] theorem eulerChar_rotateFaces (k : C.Face → ℕ) :
    (C.rotateFaces k).eulerChar = C.eulerChar :=
  (C.rotateFacesIso k).eulerChar_eq

/-- Moving the starting points of the faces does not change orientability. -/
@[simp] theorem isOrientable_rotateFaces_iff (k : C.Face → ℕ) :
    (C.rotateFaces k).IsOrientable ↔ C.IsOrientable :=
  (C.rotateFacesIso k).isOrientable_iff

/-! ### Reversal of face orientations -/

/-- The polygonal complex obtained by reversing the orientation of the faces `f` with
`s f = true`: such a face is traversed backwards, so its `i`-th side is the reverse of the side of
`f` at the opposite position. It is reducible, so that its one-skeleton, faces and numbers of sides
are seen to be those of `C`. -/
abbrev reverseFaces (s : C.Face → Bool) : PolygonalComplex.{u, v, w} where
  graph := C.graph
  Face := C.Face
  sides := C.sides
  sides_pos := C.sides_pos
  side f i := cond (s f) (C.graph.rev (C.side f (Fin.rev i))) (C.side f i)
  tgt_side f i := by
    cases s f
    · exact C.tgt_side f i
    · have h := Fin.finRotate_rev_finRotate_rev (Fin.rev i)
      rw [Fin.rev_rev] at h
      simp only [Bool.cond_true, SerreGraph.tgt_rev, SerreGraph.src_rev, C.tgt_side, h]

@[simp] theorem reverseFaces_side (s : C.Face → Bool) (f : C.Face) (i : Fin (C.sides f)) :
    (C.reverseFaces s).side f i =
      cond (s f) (C.graph.rev (C.side f (Fin.rev i))) (C.side f i) := rfl

@[simp] theorem outgoing_reverseFaces (s : C.Face → Bool) (c : C.Corner) :
    (C.reverseFaces s).outgoing c =
      cond (s c.1) (C.graph.rev (C.outgoing ⟨c.1, Fin.rev c.2⟩)) (C.outgoing c) := by
  simp only [outgoing_def]

@[simp] theorem nextCorner_reverseFaces (s : C.Face → Bool) (c : C.Corner) :
    (C.reverseFaces s).nextCorner c = C.nextCorner c := by
  simp only [nextCorner_def]

@[simp] theorem prevCorner_reverseFaces (s : C.Face → Bool) (c : C.Corner) :
    (C.reverseFaces s).prevCorner c = C.prevCorner c := by
  simp only [prevCorner_def]

@[simp] theorem cornerVertex_reverseFaces (s : C.Face → Bool) (c : C.Corner) :
    (C.reverseFaces s).cornerVertex c =
      cond (s c.1) (C.cornerVertex (C.nextCorner ⟨c.1, Fin.rev c.2⟩)) (C.cornerVertex c) := by
  rw [← src_outgoing, outgoing_reverseFaces]
  cases s c.1 <;> simp

/-- Reversing no face does not change the complex. -/
@[simp] theorem reverseFaces_false : C.reverseFaces (fun _ => false) = C := (rfl)

/-- Reversing the faces chosen by `s` and then those chosen by `t` reverses the faces chosen by
exactly one of them. -/
theorem reverseFaces_reverseFaces (s t : C.Face → Bool) :
    (C.reverseFaces s).reverseFaces t = C.reverseFaces (fun f => s f ^^ t f) := by
  dsimp only [reverseFaces]
  congr 1
  funext f i
  cases s f <;> cases t f <;> simp

/-- Reversing the same faces twice gives back the complex. -/
@[simp] theorem reverseFaces_reverseFaces_self (s : C.Face → Bool) :
    (C.reverseFaces s).reverseFaces s = C := by
  simp [reverseFaces_reverseFaces]

/-- Reversing the orientations of some faces gives an isomorphic complex: the identity on the
one-skeleton and on the faces, reversing the orientation of the chosen faces and the order of
their sides. -/
def reverseFacesIso (s : C.Face → Bool) : C.Iso (C.reverseFaces s) where
  graph := .refl _
  faceEquiv := .refl _
  flip := s
  sideEquiv := Equiv.sigmaCongrRight fun f => cond (s f) Fin.revPerm (Equiv.refl _)
  sideEquiv_apply_fst _ := rfl
  sideEquiv_nextCorner c := by
    obtain ⟨f, i⟩ := c
    cases hs : s f
    · simp [nextCorner_def, hs]
    · have h := Fin.finRotate_rev_finRotate_rev (Fin.rev i)
      rw [Fin.rev_rev] at h
      simp only [hs, Bool.cond_true, nextCorner_def, prevCorner_def, Equiv.sigmaCongrRight_apply,
        Fin.revPerm_apply]
      exact congrArg (Sigma.mk f) ((Equiv.eq_symm_apply _).2 h)
  outgoing_sideEquiv c := by
    obtain ⟨f, i⟩ := c
    cases hs : s f <;> simp [outgoing_def, hs]

@[simp] theorem reverseFacesIso_graph (s : C.Face → Bool) :
    (C.reverseFacesIso s).graph = .refl C.graph := (rfl)

@[simp] theorem reverseFacesIso_faceEquiv (s : C.Face → Bool) :
    (C.reverseFacesIso s).faceEquiv = .refl C.Face := (rfl)

@[simp] theorem reverseFacesIso_flip (s : C.Face → Bool) : (C.reverseFacesIso s).flip = s := (rfl)

@[simp] theorem reverseFacesIso_sideEquiv_apply (s : C.Face → Bool) (c : C.Corner) :
    (C.reverseFacesIso s).sideEquiv c = ⟨c.1, cond (s c.1) (Fin.rev c.2) c.2⟩ := by
  obtain ⟨f, i⟩ := c
  cases hs : s f <;> simp [reverseFacesIso, hs]

@[simp] theorem reverseFacesIso_sideEquiv_symm_apply (s : C.Face → Bool) (c : C.Corner) :
    (C.reverseFacesIso s).sideEquiv.symm c = ⟨c.1, cond (s c.1) (Fin.rev c.2) c.2⟩ := by
  obtain ⟨f, i⟩ := c
  cases hs : s f <;> simp [Equiv.symm_apply_eq, hs]

@[simp] theorem reverseFacesIso_cornerEquiv_apply (s : C.Face → Bool) (c : C.Corner) :
    (C.reverseFacesIso s).cornerEquiv c =
      ⟨c.1, cond (s c.1) (finRotate (C.sides c.1) (Fin.rev c.2)) c.2⟩ := by
  obtain ⟨f, i⟩ := c
  cases hs : s f <;> simp only [Iso.cornerEquiv_apply, reverseFacesIso_flip,
    reverseFacesIso_sideEquiv_apply, nextCorner_def, hs, Bool.cond_true, Bool.cond_false]

@[simp] theorem reverseFacesIso_cornerEquiv_symm_apply (s : C.Face → Bool) (c : C.Corner) :
    (C.reverseFacesIso s).cornerEquiv.symm c =
      ⟨c.1, cond (s c.1) (finRotate (C.sides c.1) (Fin.rev c.2)) c.2⟩ := by
  rw [Equiv.symm_apply_eq, reverseFacesIso_cornerEquiv_apply]
  obtain ⟨f, i⟩ := c
  cases s f <;> simp only [Bool.cond_true, Bool.cond_false, Fin.finRotate_rev_finRotate_rev]

@[simp] theorem incoming_reverseFaces (s : C.Face → Bool) (c : C.Corner) :
    (C.reverseFaces s).incoming c = cond (s c.1)
      (C.graph.rev (C.outgoing (C.nextCorner ⟨c.1, Fin.rev c.2⟩))) (C.incoming c) := by
  obtain ⟨f, i⟩ := c
  cases hs : s f
  · simpa [hs] using (C.reverseFacesIso s).incoming_sideEquiv ⟨f, i⟩
  · simpa [hs] using (C.reverseFacesIso s).incoming_sideEquiv ⟨f, Fin.rev i⟩

/-- Reversing the orientations of some faces does not change the degrees of the germs. -/
@[simp] theorem linkDegree_reverseFaces (s : C.Face → Bool) (e : C.graph.E) :
    (C.reverseFaces s).linkDegree e = C.linkDegree e := by
  simpa using (C.reverseFacesIso s).linkDegree_equivE e

/-- Reversing the orientations of some faces does not change which vertices have surface
links. -/
@[simp] theorem hasSurfaceLink_reverseFaces_iff (s : C.Face → Bool) (v : C.graph.V) :
    (C.reverseFaces s).HasSurfaceLink v ↔ C.HasSurfaceLink v := by
  simpa using (C.reverseFacesIso s).hasSurfaceLink_equivV_iff v

/-- Reversing the orientations of some faces does not change the Euler characteristic. -/
@[simp] theorem eulerChar_reverseFaces (s : C.Face → Bool) :
    (C.reverseFaces s).eulerChar = C.eulerChar :=
  (C.reverseFacesIso s).eulerChar_eq

/-- Reversing the orientations of some faces does not change orientability. -/
@[simp] theorem isOrientable_reverseFaces_iff (s : C.Face → Bool) :
    (C.reverseFaces s).IsOrientable ↔ C.IsOrientable :=
  (C.reverseFacesIso s).isOrientable_iff

end PolygonalComplex

/-! ### Surface models -/

namespace SurfaceModel

variable (S : SurfaceModel.{u, v, w})

/-- The surface model obtained by moving the starting point of each face `f` forward by `k f`
sides. It is reducible, so that its underlying complex is seen to be
`S.toPolygonalComplex.rotateFaces k`. -/
abbrev rotateFaces (k : S.Face → ℕ) : SurfaceModel.{u, v, w} :=
  S.ofIso (S.rotateFacesIso k)

@[simp] theorem toPolygonalComplex_rotateFaces (k : S.Face → ℕ) :
    (S.rotateFaces k).toPolygonalComplex = S.toPolygonalComplex.rotateFaces k := (rfl)

/-- Moving the starting points by `0` does not change the surface model. -/
@[simp] theorem rotateFaces_zero : S.rotateFaces 0 = S :=
  toPolygonalComplex_injective S.toPolygonalComplex.rotateFaces_zero

/-- Moving the starting points by `k` and then by `k'` moves them by `k + k'`. -/
theorem rotateFaces_rotateFaces (k k' : S.Face → ℕ) :
    (S.rotateFaces k).rotateFaces k' = S.rotateFaces (k + k') :=
  toPolygonalComplex_injective (S.toPolygonalComplex.rotateFaces_rotateFaces k k')

/-- Moving the starting points of the faces does not change the boundary darts. -/
theorem boundaryDarts_rotateFaces (k : S.Face → ℕ) :
    (S.rotateFaces k).boundaryDarts = S.boundaryDarts := by
  simp

/-- Moving the starting points of the faces does not change the boundary germs. -/
theorem boundaryGerms_rotateFaces (k : S.Face → ℕ) (v : S.graph.V) :
    (S.rotateFaces k).boundaryGerms v = S.boundaryGerms v := by
  simp

/-- The surface model obtained by reversing the orientation of the faces `f` with `s f = true`.
It is reducible, so that its underlying complex is seen to be
`S.toPolygonalComplex.reverseFaces s`. -/
abbrev reverseFaces (s : S.Face → Bool) : SurfaceModel.{u, v, w} :=
  S.ofIso (S.reverseFacesIso s)

@[simp] theorem toPolygonalComplex_reverseFaces (s : S.Face → Bool) :
    (S.reverseFaces s).toPolygonalComplex = S.toPolygonalComplex.reverseFaces s := (rfl)

/-- Reversing no face does not change the surface model. -/
@[simp] theorem reverseFaces_false : S.reverseFaces (fun _ => false) = S :=
  toPolygonalComplex_injective S.toPolygonalComplex.reverseFaces_false

/-- Reversing the faces chosen by `s` and then those chosen by `t` reverses the faces chosen by
exactly one of them. -/
theorem reverseFaces_reverseFaces (s t : S.Face → Bool) :
    (S.reverseFaces s).reverseFaces t = S.reverseFaces (fun f => s f ^^ t f) :=
  toPolygonalComplex_injective (S.toPolygonalComplex.reverseFaces_reverseFaces s t)

/-- Reversing the same faces twice gives back the surface model. -/
@[simp] theorem reverseFaces_reverseFaces_self (s : S.Face → Bool) :
    (S.reverseFaces s).reverseFaces s = S :=
  toPolygonalComplex_injective (S.toPolygonalComplex.reverseFaces_reverseFaces_self s)

/-- Reversing the orientations of some faces does not change the boundary darts. -/
theorem boundaryDarts_reverseFaces (s : S.Face → Bool) :
    (S.reverseFaces s).boundaryDarts = S.boundaryDarts := by
  simp

/-- Reversing the orientations of some faces does not change the boundary germs. -/
theorem boundaryGerms_reverseFaces (s : S.Face → Bool) (v : S.graph.V) :
    (S.reverseFaces s).boundaryGerms v = S.boundaryGerms v := by
  simp

end SurfaceModel

end TauCeti
