/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Cube.Generator
public import Mathlib.Data.Finset.Option

/-!
# Forgetting one coordinate of a plumbing cube

`PlumbingCube.dropNone` projects a cube on `Option V` onto its old coordinates in `V`.
It commutes with faces in old directions and identifies the two faces in the forgotten
direction. Its vertices are exactly the projections of the original vertices, including
when the forgotten direction belongs to the cube. These facts describe the cubical
projection underlying a vertex blow-down in lattice homology.

The cubical conventions follow A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti.PlumbingCube

variable {V : Type*}

/-- Forget the coordinate and direction indexed by `none`. -/
def dropNone (C : PlumbingCube (Option V)) : PlumbingCube V where
  base w := C.base (some w)
  directions := C.directions.eraseNone

@[simp]
theorem dropNone_base (C : PlumbingCube (Option V)) (w : V) :
    C.dropNone.base w = C.base (some w) :=
  (rfl)

@[simp]
theorem dropNone_directions (C : PlumbingCube (Option V)) :
    C.dropNone.directions = C.directions.eraseNone :=
  (rfl)

theorem mem_dropNone_directions (C : PlumbingCube (Option V)) (w : V) :
    w ∈ C.dropNone.directions ↔ some w ∈ C.directions :=
  Finset.mem_eraseNone

variable [DecidableEq V]

/-- Projection commutes with a lower face in an old direction. -/
@[simp]
theorem dropNone_lowerFace_some (C : PlumbingCube (Option V)) (w : V)
    (hw : some w ∈ C.directions) :
    (C.lowerFace (some w) hw).dropNone =
      C.dropNone.lowerFace w ((C.mem_dropNone_directions w).mpr hw) := by
  ext z
  · simp
  · simp

/-- Projection commutes with an upper face in an old direction. -/
@[simp]
theorem dropNone_upperFace_some (C : PlumbingCube (Option V)) (w : V)
    (hw : some w ∈ C.directions) :
    (C.upperFace (some w) hw).dropNone =
      C.dropNone.upperFace w ((C.mem_dropNone_directions w).mpr hw) := by
  ext z
  · simp [Pi.single_apply]
  · simp

/-- The lower exceptional face projects to the same cube as the ambient cube. -/
@[simp]
theorem dropNone_lowerFace_none (C : PlumbingCube (Option V))
    (h : none ∈ C.directions) : (C.lowerFace none h).dropNone = C.dropNone := by
  ext z
  · simp
  · simp

/-- The upper exceptional face projects to the same cube as the ambient cube. -/
@[simp]
theorem dropNone_upperFace_none (C : PlumbingCube (Option V))
    (h : none ∈ C.directions) : (C.upperFace none h).dropNone = C.dropNone := by
  ext z
  · simp
  · simp

omit [DecidableEq V] in
/-- A cube with no exceptional direction retains its dimension under projection. -/
theorem dimension_dropNone_of_none_notMem (C : PlumbingCube (Option V))
    (h : none ∉ C.directions) : C.dropNone.dimension = C.dimension :=
  Finset.card_eraseNone_of_notMem h

/-- Projected vertices are exactly the vertices of the projected cube. -/
theorem vertices_dropNone [DecidableEq (V → ℤ)] [DecidableEq (Option V → ℤ)]
    (C : PlumbingCube (Option V)) :
    C.dropNone.vertices = C.vertices.image (fun y w => y (some w)) := by
  classical
  ext z
  rw [mem_vertices, Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩
    refine ⟨PlumbingGraph.cubeVertex C.base (T.image some), ?_, ?_⟩
    · rw [mem_vertices]
      refine ⟨T.image some, ?_, rfl⟩
      rintro _ ha
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ha
      exact (C.mem_dropNone_directions w).mp (hT hw)
    · funext w
      simp
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨T, hT, rfl⟩ := (C.mem_vertices y).mp hy
    refine ⟨T.eraseNone, Finset.eraseNone.monotone hT, ?_⟩
    funext w
    simp

end TauCeti.PlumbingCube
