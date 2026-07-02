/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LowDimTopology.Plumbing.CubeGenerator

/-!
# Codimension-two faces of a plumbing cube

This file adds the codimension-two face bookkeeping for the cubical generators of Némethi's
lattice homology (`CubeGenerator.lean`). A plumbing cube `(x, S)` has, in each present
direction `v`, a lower face `(x, S.erase v)` and an upper face `(x + E_v, S.erase v)`. Taking
faces in two distinct present directions `v ≠ w` produces a codimension-two face, and the
central fact is that the order of the two directions does not matter: the two ways of reaching
each corner agree.

These commuting squares are the geometric skeleton of the lattice-homology differential's
`∂² = 0`: the boundary of the boundary revisits each codimension-two face along the two edges of
a square, and the squares here identify those two contributions as the *same* generator (before
the `U`-power bookkeeping, which lives in the weight files). All four corners are recorded, one
per choice of lower/upper in each direction.

The direction set is the same for all four corners, `(S.erase v).erase w`, while the base points
are the four corners `x`, `x + E_v`, `x + E_w`, `x + E_v + E_w`.

## Main results

* `TauCeti.PlumbingCube.lowerFace_lowerFace_comm`,
  `TauCeti.PlumbingCube.upperFace_upperFace_comm`,
  `TauCeti.PlumbingCube.lowerFace_upperFace_comm`,
  `TauCeti.PlumbingCube.upperFace_lowerFace_comm`: the four codimension-two faces are independent
  of the order in which the two directions are removed.
* `TauCeti.PlumbingCube.directions_lowerFace_lowerFace`,
  `TauCeti.PlumbingCube.base_lowerFace_lowerFace`,
  `TauCeti.PlumbingCube.base_upperFace_upperFace`: the shared direction set and two of the corner
  base points of a codimension-two face.
* `TauCeti.PlumbingCube.dimension_lowerFace_lowerFace`: a codimension-two face has cubical
  dimension two less than the ambient cube.
* `TauCeti.PlumbingCube.vertices_lowerFace_lowerFace_subset`: its vertices are vertices of the
  ambient cube.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose opening item asks for Némethi's lattice (co)homology from lattice
points and weight functions. The commuting codimension-two faces are the standard cubical-boundary
squares underlying `∂² = 0` in Némethi, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841).
-/

public section

namespace TauCeti

namespace PlumbingCube

variable {V : Type*} [DecidableEq V] (C : PlumbingCube V) {v w : V}

/-- The two lower faces in distinct directions `v` and `w` agree: both are the cube based at
`C.base` with directions `(C.directions.erase v).erase w`. -/
theorem lowerFace_lowerFace_comm (hv : v ∈ C.directions) (hw : w ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) (hvw : v ∈ (C.lowerFace w hw).directions) :
    (C.lowerFace v hv).lowerFace w hwv = (C.lowerFace w hw).lowerFace v hvw := by
  apply PlumbingCube.ext
  · simp
  · simp only [lowerFace_directions]
    exact Finset.erase_right_comm

/-- The two upper faces in distinct directions `v` and `w` agree: both are the cube based at
`C.base + E_v + E_w` with directions `(C.directions.erase v).erase w`, since the two basis shifts
commute. -/
theorem upperFace_upperFace_comm (hv : v ∈ C.directions) (hw : w ∈ C.directions)
    (hwv : w ∈ (C.upperFace v hv).directions) (hvw : v ∈ (C.upperFace w hw).directions) :
    (C.upperFace v hv).upperFace w hwv = (C.upperFace w hw).upperFace v hvw := by
  apply PlumbingCube.ext
  · simp only [upperFace_base]
    exact add_right_comm _ _ _
  · simp only [upperFace_directions]
    exact Finset.erase_right_comm

/-- Taking the lower face in direction `v` then the upper face in direction `w` agrees with taking
the upper face in direction `w` then the lower face in direction `v`: both are the mixed corner
based at `C.base + E_w`. -/
theorem lowerFace_upperFace_comm (hv : v ∈ C.directions) (hw : w ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) (hvw : v ∈ (C.upperFace w hw).directions) :
    (C.lowerFace v hv).upperFace w hwv = (C.upperFace w hw).lowerFace v hvw := by
  apply PlumbingCube.ext
  · simp
  · simp only [upperFace_directions, lowerFace_directions]
    exact Finset.erase_right_comm

/-- Taking the upper face in direction `v` then the lower face in direction `w` agrees with taking
the lower face in direction `w` then the upper face in direction `v`: both are the mixed corner
based at `C.base + E_v`. -/
theorem upperFace_lowerFace_comm (hv : v ∈ C.directions) (hw : w ∈ C.directions)
    (hwv : w ∈ (C.upperFace v hv).directions) (hvw : v ∈ (C.lowerFace w hw).directions) :
    (C.upperFace v hv).lowerFace w hwv = (C.lowerFace w hw).upperFace v hvw := by
  apply PlumbingCube.ext
  · simp
  · simp only [upperFace_directions, lowerFace_directions]
    exact Finset.erase_right_comm

/-- The direction set of a codimension-two face is the ambient direction set with the two chosen
directions removed. -/
@[simp]
theorem directions_lowerFace_lowerFace (hv : v ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) :
    ((C.lowerFace v hv).lowerFace w hwv).directions = (C.directions.erase v).erase w := by
  simp

/-- The lower-lower codimension-two face keeps the ambient base point. -/
@[simp]
theorem base_lowerFace_lowerFace (hv : v ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) :
    ((C.lowerFace v hv).lowerFace w hwv).base = C.base := by
  simp

/-- The upper-upper codimension-two face sits at the far corner `C.base + E_v + E_w`. -/
@[simp]
theorem base_upperFace_upperFace (hv : v ∈ C.directions)
    (hwv : w ∈ (C.upperFace v hv).directions) :
    ((C.upperFace v hv).upperFace w hwv).base = C.base + Pi.single v (1 : ℤ) + Pi.single w 1 := by
  simp

/-- A codimension-two face has cubical dimension two less than the ambient cube. -/
theorem dimension_lowerFace_lowerFace (hv : v ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) :
    ((C.lowerFace v hv).lowerFace w hwv).dimension = C.dimension - 2 := by
  rw [dimension_lowerFace_of_mem, dimension_lowerFace_of_mem]
  omega

variable [DecidableEq (V → ℤ)]

/-- The vertices of a codimension-two face are vertices of the ambient cube. -/
theorem vertices_lowerFace_lowerFace_subset (hv : v ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) :
    ((C.lowerFace v hv).lowerFace w hwv).vertices ⊆ C.vertices :=
  ((C.lowerFace v hv).vertices_lowerFace_subset hwv).trans (C.vertices_lowerFace_subset hv)

end PlumbingCube

end TauCeti
