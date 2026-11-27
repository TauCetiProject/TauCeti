/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.LinearAlgebra.Projectivization.AffineChart
import TauCeti.LinearAlgebra.Projectivization.Basic

/-!
# The projective line `OnePoint K` and the standard affine opens of `ℙ K (Fin 2 → K)`

Mathlib identifies `OnePoint K` with `ℙ K (Fin 2 → K)` by `OnePoint.equivProjectivization`:
`t ↦ [t : 1]` and `∞ ↦ [1 : 0]`. This file describes, in terms of `OnePoint K`, which points land
in the two standard affine opens `Projectivization.affineOpen i`: the affine open of the
coordinate `1` consists of the finite points, and the affine open of the coordinate `0` consists
of the points other than `0`, and the only point outside the affine open of the coordinate `1`
corresponds to `∞`. Over a field, two points with homogeneous coordinates `v` and `w` coincide
exactly when the matrix with rows `v` and `w` has determinant zero.

## Main declarations

* `OnePoint.equivProjectivization_mem_affineOpen_one_iff`
* `OnePoint.equivProjectivization_mem_affineOpen_zero_iff`
* `OnePoint.equivProjectivization_symm_eq_infty_iff`
* `OnePoint.eq_iff_det_eq_zero`
-/

public section

open scoped LinearAlgebra.Projectivization

namespace OnePoint

section DivisionRing

variable {K : Type*} [DivisionRing K] [DecidableEq K]

/-- The point `[t : 1]` or `[1 : 0]` corresponding to `x : OnePoint K` lies in the standard affine
open of the coordinate `1` exactly when `x` is finite. -/
@[simp]
theorem equivProjectivization_mem_affineOpen_one_iff (x : OnePoint K) :
    equivProjectivization K x ∈ Projectivization.affineOpen 1 ↔ x ≠ (∞ : OnePoint K) := by
  induction x using OnePoint.rec <;> simp

/-- The point `[t : 1]` or `[1 : 0]` corresponding to `x : OnePoint K` lies in the standard affine
open of the coordinate `0` exactly when `x` is not `0`. -/
@[simp]
theorem equivProjectivization_mem_affineOpen_zero_iff (x : OnePoint K) :
    equivProjectivization K x ∈ Projectivization.affineOpen 0 ↔ x ≠ ((0 : K) : OnePoint K) := by
  induction x using OnePoint.rec <;> simp

/-- The only point of `ℙ K (Fin 2 → K)` outside the standard affine open of the coordinate `1`
corresponds to `∞`. -/
@[simp]
theorem equivProjectivization_symm_eq_infty_iff (x : ℙ K (Fin 2 → K)) :
    (equivProjectivization K).symm x = (∞ : OnePoint K) ↔ x ∉ Projectivization.affineOpen 1 := by
  rw [← (equivProjectivization K).apply_symm_apply x, equivProjectivization_mem_affineOpen_one_iff,
    Equiv.symm_apply_apply, not_not]

end DivisionRing

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- Two points of the projective line with homogeneous coordinates `v` and `w` coincide exactly
when the matrix with rows `v` and `w` has determinant zero. -/
theorem eq_iff_det_eq_zero {x y : OnePoint K} {v w : Fin 2 → K}
    {hv : v ≠ 0} {hw : w ≠ 0} (hx : equivProjectivization K x = .mk K v hv)
    (hy : equivProjectivization K y = .mk K w hw) : x = y ↔ (Matrix.of ![v, w]).det = 0 := by
  rw [← (equivProjectivization K).injective.eq_iff, hx, hy,
    Projectivization.mk_eq_mk_iff_det_eq_zero]

end Field

end OnePoint
