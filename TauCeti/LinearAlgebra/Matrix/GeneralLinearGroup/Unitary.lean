/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The unitary subgroup of the general linear group

Mathlib's `unitarySubgroup (GL n R)` is the subgroup of invertible matrices `g` with
`g * star g = 1`, read on units. This file identifies it with Mathlib's matrix-level
`Matrix.unitaryGroup n R`, and records that a unitary invertible matrix is inverted by its star.
When the star on `R` is trivial (as for `ℝ`), the star of a matrix is its transpose and the unitary
subgroup is the orthogonal group: these are the matrices whose transpose is a two-sided inverse.

## Main results

* `TauCeti.mem_unitarySubgroup_GL_iff_mem_unitaryGroup`: membership in the unitary subgroup is
  membership of the underlying matrix in `Matrix.unitaryGroup`.
* `TauCeti.coe_inv_eq_star_of_mem_unitarySubgroup`: a unitary invertible matrix is inverted by its
  star.
* `TauCeti.mem_unitarySubgroup_GL_iff`: over a ring with trivial star, `g` is unitary exactly when
  `g gᵀ = 1`.
* `TauCeti.coe_inv_eq_transpose_of_mem_unitarySubgroup` and
  `TauCeti.transpose_mul_self_of_mem_unitarySubgroup`: over a ring with trivial star, a unitary
  invertible matrix is inverted by its transpose.
-/

public section

open Matrix

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] [StarRing R]
  {g : GL n R}

/-- An invertible matrix lies in the unitary subgroup of `GL n R` exactly when its underlying
matrix lies in Mathlib's unitary group `Matrix.unitaryGroup n R`. -/
theorem mem_unitarySubgroup_GL_iff_mem_unitaryGroup :
    g ∈ unitarySubgroup (GL n R) ↔ (g : Matrix n n R) ∈ unitaryGroup n R := by
  rw [mem_unitarySubgroup_iff, Units.unitary_eq, Submonoid.mem_comap, Units.coeHom_apply]

/-- The inverse of an element of the unitary subgroup of `GL n R` is its star. -/
theorem coe_inv_eq_star_of_mem_unitarySubgroup (hg : g ∈ unitarySubgroup (GL n R)) :
    ((g⁻¹ : GL n R) : Matrix n n R) = star (g : Matrix n n R) :=
  (Units.eq_inv_of_mul_eq_one_left
    ((mem_unitaryGroup_iff.1 (mem_unitarySubgroup_GL_iff_mem_unitaryGroup.1 hg)))).symm

variable [TrivialStar R]

/-- Over a ring with trivial star, an invertible matrix lies in the unitary subgroup of `GL n R`
exactly when its transpose is a right inverse. -/
theorem mem_unitarySubgroup_GL_iff :
    g ∈ unitarySubgroup (GL n R) ↔ (g : Matrix n n R) * (g : Matrix n n R)ᵀ = 1 := by
  rw [mem_unitarySubgroup_GL_iff_mem_unitaryGroup, mem_unitaryGroup_iff, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]

/-- Over a ring with trivial star, the inverse of an element of the unitary subgroup of `GL n R` is
its transpose. -/
theorem coe_inv_eq_transpose_of_mem_unitarySubgroup (hg : g ∈ unitarySubgroup (GL n R)) :
    ((g⁻¹ : GL n R) : Matrix n n R) = (g : Matrix n n R)ᵀ := by
  rw [coe_inv_eq_star_of_mem_unitarySubgroup hg, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]

/-- Over a ring with trivial star, the transpose of an element of the unitary subgroup of `GL n R`
is a left inverse. -/
theorem transpose_mul_self_of_mem_unitarySubgroup (hg : g ∈ unitarySubgroup (GL n R)) :
    (g : Matrix n n R)ᵀ * (g : Matrix n n R) = 1 := by
  rw [← coe_inv_eq_transpose_of_mem_unitarySubgroup hg, Units.inv_mul]

end TauCeti
