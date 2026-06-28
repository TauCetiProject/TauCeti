/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LowDimTopology.Plumbing.CubeWeightRecursion

/-!
# Plumbing-lattice cube generators and their faces

This file packages the cubical generators used in Némethi's lattice homology. A cube generator is
the pair of a lattice base point `x : V → ℤ` and a finite set `S : Finset V` of basis directions.
Its codimension-one faces in a direction `v ∈ S` are the lower face `(x, S.erase v)` and the
upper face `(x + E_v, S.erase v)`.

The earlier plumbing files define vertices, characteristic cube weights, and the lower/upper
face exponents as functions of `(x, S)`. This file provides the bundled generator API that the
lattice-homology differential can use directly.

## Main definitions

* `TauCeti.PlumbingCube`: a bundled plumbing-lattice cube generator.
* `TauCeti.PlumbingCube.lowerFace` and `TauCeti.PlumbingCube.upperFace`: the two
  codimension-one faces in a direction.
* `TauCeti.PlumbingCube.characteristicWeight`: the characteristic cube weight of a bundled
  generator.
* `TauCeti.PlumbingCube.characteristicLowerFaceExponent` and
  `TauCeti.PlumbingCube.characteristicUpperFaceExponent`: the `U`-exponents of the two faces.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose opening item asks for Némethi's lattice (co)homology from lattice
points and weight functions. The lower/upper face convention and exponents are the standard
cubical-boundary data in Némethi, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841).
-/

public section

namespace TauCeti

/-- A plumbing-lattice cube generator: a lattice base point together with a finite set of basis
directions. In Némethi's lattice homology this is the cubical generator usually denoted by a pair
`(x, S)`. -/
structure PlumbingCube (V : Type*) where
  /-- The lattice base point of the cube. -/
  base : V → ℤ
  /-- The finite set of basis directions spanning the cube. -/
  directions : Finset V

namespace PlumbingCube

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Two plumbing cubes are equal when their base points and direction sets agree. -/
@[ext]
theorem ext {C D : PlumbingCube V} (hbase : C.base = D.base)
    (hdirections : C.directions = D.directions) : C = D := by
  cases C
  cases D
  simp_all

/-- The cubical dimension of a plumbing cube, namely the number of basis directions. -/
abbrev dimension (C : PlumbingCube V) : ℕ :=
  C.directions.card

/-- The lower codimension-one face in a present direction `v`: keep the base point and remove
`v` from the direction set. -/
irreducible_def lowerFace (C : PlumbingCube V) (v : V)
    (_hv : v ∈ C.directions) : PlumbingCube V where
  base := C.base
  directions := C.directions.erase v

/-- The upper codimension-one face in a present direction `v`: shift the base point by `E_v` and
remove `v` from the direction set. -/
irreducible_def upperFace (C : PlumbingCube V) (v : V)
    (_hv : v ∈ C.directions) : PlumbingCube V where
  base := C.base + Pi.single v (1 : ℤ)
  directions := C.directions.erase v

omit [DecidableEq V] in
@[simp]
theorem dimension_mk (x : V → ℤ) (S : Finset V) :
    dimension ({ base := x, directions := S } : PlumbingCube V) = S.card :=
  rfl

@[simp]
theorem lowerFace_mk (x : V → ℤ) (S : Finset V) (v : V) (hv : v ∈ S) :
    lowerFace ({ base := x, directions := S } : PlumbingCube V) v hv =
      ({ base := x, directions := S.erase v } : PlumbingCube V) :=
  by simp [lowerFace_def]

@[simp]
theorem upperFace_mk (x : V → ℤ) (S : Finset V) (v : V) (hv : v ∈ S) :
    upperFace ({ base := x, directions := S } : PlumbingCube V) v hv =
      ({ base := x + Pi.single v (1 : ℤ), directions := S.erase v } : PlumbingCube V) :=
  by simp [upperFace_def]

@[simp]
theorem lowerFace_base (C : PlumbingCube V) (v : V) (hv : v ∈ C.directions) :
    (C.lowerFace v hv).base = C.base :=
  by simp [lowerFace_def]

@[simp]
theorem lowerFace_directions (C : PlumbingCube V) (v : V) (hv : v ∈ C.directions) :
    (C.lowerFace v hv).directions = C.directions.erase v :=
  by simp [lowerFace_def]

@[simp]
theorem upperFace_base (C : PlumbingCube V) (v : V) (hv : v ∈ C.directions) :
    (C.upperFace v hv).base = C.base + Pi.single v (1 : ℤ) :=
  by simp [upperFace_def]

@[simp]
theorem upperFace_directions (C : PlumbingCube V) (v : V) (hv : v ∈ C.directions) :
    (C.upperFace v hv).directions = C.directions.erase v :=
  by simp [upperFace_def]

variable [DecidableEq (V → ℤ)]

/-- The vertices of a bundled plumbing cube. -/
noncomputable irreducible_def vertices (C : PlumbingCube V) : Finset (V → ℤ) :=
  PlumbingGraph.cubeVertices C.base C.directions

@[simp]
theorem vertices_mk (x : V → ℤ) (S : Finset V) :
    vertices ({ base := x, directions := S } : PlumbingCube V) =
      PlumbingGraph.cubeVertices x S :=
  by simp [vertices_def]

/-- Membership in the vertices of a bundled cube, expressed by a direction subset. -/
theorem mem_vertices (C : PlumbingCube V) (y : V → ℤ) :
    y ∈ C.vertices ↔ ∃ T ⊆ C.directions, PlumbingGraph.cubeVertex C.base T = y :=
  by simpa [vertices_def] using PlumbingGraph.mem_cubeVertices C.base C.directions y

/-- The base point is a vertex of every bundled cube. -/
@[simp]
theorem base_mem_vertices (C : PlumbingCube V) :
    C.base ∈ C.vertices :=
  by simp [vertices_def]

/-- The lower face's vertices are vertices of the ambient cube. -/
theorem vertices_lowerFace_subset (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    (C.lowerFace v hv).vertices ⊆ C.vertices :=
  by
    simpa [vertices_def, lowerFace_base, lowerFace_directions] using
      PlumbingGraph.cubeVertices_subset (Finset.erase_subset v C.directions) C.base

/-- The upper face's vertices are vertices of the ambient cube when the face direction belongs to
the ambient cube. -/
theorem vertices_upperFace_subset (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    (C.upperFace v hv).vertices ⊆ C.vertices :=
  by
    simpa [vertices_def, upperFace_base, upperFace_directions] using
      PlumbingGraph.cubeVertices_upperFace_subset (x := C.base) hv

omit [DecidableEq (V → ℤ)] in
/-- Removing a present direction drops the cubical dimension by one for the lower face. -/
@[simp]
theorem dimension_lowerFace_of_mem (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    (C.lowerFace v hv).dimension = C.dimension - 1 := by
  rw [dimension, dimension, lowerFace_directions, Finset.card_erase_of_mem hv]

omit [DecidableEq (V → ℤ)] in
/-- Removing a present direction drops the cubical dimension by one for the upper face. -/
@[simp]
theorem dimension_upperFace_of_mem (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    (C.upperFace v hv).dimension = C.dimension - 1 := by
  rw [dimension, dimension, upperFace_directions, Finset.card_erase_of_mem hv]

/-- The characteristic cube weight of a bundled plumbing cube. -/
noncomputable irreducible_def characteristicWeight [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) : ℤ :=
  P.characteristicCubeWeight k C.base C.directions

@[simp]
theorem characteristicWeight_mk [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) :
    characteristicWeight P k ({ base := x, directions := S } : PlumbingCube V) =
      P.characteristicCubeWeight k x S :=
  by simp [characteristicWeight_def]

/-- The lower face's characteristic weight is bounded by the ambient cube weight. -/
theorem characteristicWeight_lowerFace_le [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    characteristicWeight P k (C.lowerFace v hv) ≤ characteristicWeight P k C :=
  by
    simpa [characteristicWeight_def, lowerFace_base, lowerFace_directions] using
      P.characteristicCubeWeight_mono k (Finset.erase_subset v C.directions) C.base

/-- The upper face's characteristic weight is bounded by the ambient cube weight. -/
theorem characteristicWeight_upperFace_le [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    characteristicWeight P k (C.upperFace v hv) ≤ characteristicWeight P k C :=
  by
    simpa [characteristicWeight_def, upperFace_base, upperFace_directions] using
      P.characteristicUpperFaceWeight_le (x := C.base) k hv

/-- The nonnegative exponent of the lower face in the lattice-homology differential. -/
noncomputable irreducible_def characteristicLowerFaceExponent [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (_hv : v ∈ C.directions) : ℕ :=
  P.characteristicLowerFaceExponent k C.base C.directions v

/-- The nonnegative exponent of the upper face in the lattice-homology differential. -/
noncomputable irreducible_def characteristicUpperFaceExponent [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) : ℕ :=
  P.characteristicUpperFaceExponent k C.base C.directions hv

@[simp]
theorem characteristicLowerFaceExponent_mk [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) {v : V} (hv : v ∈ S) :
    characteristicLowerFaceExponent P k ({ base := x, directions := S } : PlumbingCube V) hv =
      P.characteristicLowerFaceExponent k x S v :=
  by simp [characteristicLowerFaceExponent_def]

@[simp]
theorem characteristicUpperFaceExponent_mk [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) {v : V} (hv : v ∈ S) :
    characteristicUpperFaceExponent P k ({ base := x, directions := S } : PlumbingCube V) hv =
      P.characteristicUpperFaceExponent k x S hv :=
  by simp [characteristicUpperFaceExponent_def]

/-- The lower-face exponent is the weight difference between the ambient cube and the lower face. -/
@[simp]
theorem characteristicLowerFaceExponent_natCast [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    (characteristicLowerFaceExponent P k C hv : ℤ) =
      characteristicWeight P k C - characteristicWeight P k (C.lowerFace v hv) :=
  by
    simp [characteristicLowerFaceExponent_def, characteristicWeight_def, lowerFace_base,
      lowerFace_directions]

/-- The upper-face exponent is the weight difference between the ambient cube and the upper face. -/
@[simp]
theorem characteristicUpperFaceExponent_natCast [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    (characteristicUpperFaceExponent P k C hv : ℤ) =
      characteristicWeight P k C - characteristicWeight P k (C.upperFace v hv) :=
  by
    simp [characteristicUpperFaceExponent_def, characteristicWeight_def, upperFace_base,
      upperFace_directions]

/-- The lower-face exponent vanishes exactly when the lower face has the ambient cube's
characteristic weight. -/
theorem characteristicLowerFaceExponent_eq_zero_iff [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    characteristicLowerFaceExponent P k C hv = 0 ↔
      characteristicWeight P k C = characteristicWeight P k (C.lowerFace v hv) :=
  by
    simpa [characteristicLowerFaceExponent_def, characteristicWeight_def, lowerFace_base,
      lowerFace_directions] using
      P.characteristicLowerFaceExponent_eq_zero_iff (x := C.base) (S := C.directions) (v := v) k

/-- The upper-face exponent vanishes exactly when the upper face has the ambient cube's
characteristic weight. -/
theorem characteristicUpperFaceExponent_eq_zero_iff [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    characteristicUpperFaceExponent P k C hv = 0 ↔
      characteristicWeight P k C = characteristicWeight P k (C.upperFace v hv) :=
  by
    simpa [characteristicUpperFaceExponent_def, characteristicWeight_def, upperFace_base,
      upperFace_directions] using
      P.characteristicUpperFaceExponent_eq_zero_iff (x := C.base) k hv

/-- In any present direction, the characteristic weight of a cube is the maximum of the weights
of its lower and upper faces. -/
theorem characteristicWeight_eq_max_faces [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    characteristicWeight P k C =
      max (characteristicWeight P k (C.lowerFace v hv))
        (characteristicWeight P k (C.upperFace v hv)) :=
  by
    simpa [characteristicWeight_def, lowerFace_base, lowerFace_directions, upperFace_base,
      upperFace_directions] using
      P.characteristicCubeWeight_eq_max_erase k C.base hv

/-- In any present direction, at least one of the two face exponents vanishes. -/
@[simp]
theorem min_characteristicFaceExponent_eq_zero [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    min (characteristicLowerFaceExponent P k C hv)
      (characteristicUpperFaceExponent P k C hv) = 0 :=
  by
    simp [characteristicLowerFaceExponent_def, characteristicUpperFaceExponent_def]

end PlumbingCube

end TauCeti
