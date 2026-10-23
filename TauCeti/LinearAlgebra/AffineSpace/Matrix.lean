/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Matrix

/-!
# Determinants of matrices of barycentric coordinates

Fix an affine basis `b` of an affine space `P`. For a family `q` of points of `P`, the matrix
`b.toMatrix q` has the barycentric coordinates of `q i` with respect to `b` as its rows, and when
`q` is indexed like `b` its determinant is the signed (oriented) volume of the simplex with vertices
`q i`, measured relative to the simplex of `b`; the unsigned relative volume is its absolute value.

Replacing the vertex `q i` of an affine basis `q` by a point `x` scales this determinant by the
barycentric coordinate of `x` at `i` with respect to `q`
(`AffineBasis.det_toMatrix_update`). This is Cramer's rule for barycentric coordinates
(`AffineBasis.det_smul_coords_eq_cramer_coords`) read as a statement about volumes, and it is the
reason a simplex of maximal volume inside a set controls the barycentric coordinates of all points
of the set.

## Main statements

* `AffineBasis.toMatrix_update`: replacing a point of the family replaces the corresponding row by
  its barycentric coordinates;
* `AffineBasis.det_toMatrix_update`: replacing the vertex `q i` of an affine basis `q` by `x`
  multiplies the determinant by `q.coord i x`.
-/

public section

open Matrix

namespace AffineBasis

variable {ι ι' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

/-- Replacing the point `q i` of a family by `x` replaces the `i`-th row of the matrix of
barycentric coordinates by the coordinates of `x`. -/
@[simp]
theorem toMatrix_update [DecidableEq ι'] (q : ι' → P) (i : ι') (x : P) :
    b.toMatrix (Function.update q i x) = (b.toMatrix q).updateRow i (b.coords x) := by
  ext j l
  rcases eq_or_ne j i with rfl | hj
  · simp [toMatrix_apply]
  · simp [toMatrix_apply, hj]

end Ring

section CommRing

variable [CommRing k] [Module k V] [Fintype ι] [DecidableEq ι] (b b₂ : AffineBasis ι k P)

/-- Replacing the vertex `b₂ i` of the affine basis `b₂` by a point `x` multiplies the determinant
of the matrix of barycentric coordinates relative to `b` by the barycentric coordinate of `x` at
`i` with respect to `b₂`. -/
theorem det_toMatrix_update (i : ι) (x : P) :
    (b.toMatrix (Function.update b₂ i x)).det = (b.toMatrix b₂).det * b₂.coord i x := by
  have h := congr_fun (b.det_smul_coords_eq_cramer_coords b₂ x) i
  rw [Pi.smul_apply, coords_apply, smul_eq_mul, cramer_apply, updateCol_transpose,
    det_transpose] at h
  rw [toMatrix_update, h]

end CommRing

end AffineBasis
