/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import TauCeti.LinearAlgebra.Matrix.IsometryMatrices.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Basic

/-!
# Lifting special orthogonal matrices

When `2` is invertible, a special orthogonal matrix lifts across a quotient by a square-zero
ideal. An orthogonal matrix is one preserving the Gram matrix `1`, so the lifting of matrices
preserving a symmetric Gram matrix with unit determinant,
`Matrix.exists_map_eq_of_mem_isometryMatrices_map`, gives an orthogonal lift.

The lift's determinant squares to one and is congruent to one modulo the ideal. Invertibility of
`2` then forces its determinant to equal one, so the lift is special orthogonal.

## Main declarations

* `Matrix.SpecialOrthogonalGroup.map_quotient_mk_surjective_of_sq_eq_bot`: special orthogonal
  matrices lift across square-zero quotients when `2` is invertible.

## References

* The Stacks Project, Tag 00TH, for the infinitesimal lifting criterion for formal smoothness.
* SGA 3, Exposé XXIII, for the split special orthogonal group away from characteristic two.
-/

public section

open Matrix

namespace Matrix.SpecialOrthogonalGroup

universe u v

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type u} [CommRing R]

attribute [local instance] starRingOfComm

/-- Every special orthogonal matrix modulo a square-zero ideal lifts to a special orthogonal
matrix when `2` is invertible in the coefficient ring. -/
theorem map_quotient_mk_surjective_of_sq_eq_bot [Invertible (2 : R)]
    (I : Ideal R) (hI : I ^ 2 = (⊥ : Ideal R)) :
    Function.Surjective
      (map (n := n) (Ideal.Quotient.mk I)) := by
  intro g
  have hg : g.1 ∈ isometryMatrices ((1 : Matrix n n R).map (Ideal.Quotient.mk I)) := by
    rw [mem_isometryMatrices, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    exact (Matrix.mem_orthogonalGroup_iff' n (R ⧸ I)).mp g.2.1
  obtain ⟨N, hN, hN_map⟩ := exists_map_eq_of_mem_isometryMatrices_map
    Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker, hI]) (isUnit_of_invertible 2)
    transpose_one (by rw [det_one]; exact isUnit_one) hg
  have hN_orthogonal : N * Nᵀ = 1 := by
    rw [mem_isometryMatrices, Matrix.mul_one] at hN
    exact mul_eq_one_comm.mp hN
  have hdet_map : Ideal.Quotient.mk I N.det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hN_map]
    exact g.2.2
  have hdet_sub_mem : N.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hdet_map, map_one, sub_self]
  have hdet_sub_sq : (N.det - 1) ^ 2 = 0 := by
    rw [← Ideal.mem_bot, ← hI]
    simpa only [pow_two] using Ideal.mul_mem_mul hdet_sub_mem hdet_sub_mem
  have hdet_sq : N.det ^ 2 = 1 := by
    have hdet := congrArg Matrix.det hN_orthogonal
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, pow_two] using hdet
  have htwo : (2 : R) * (N.det - 1) = 0 := by
    calc
      (2 : R) * (N.det - 1) = N.det ^ 2 - 1 - (N.det - 1) ^ 2 := by ring
      _ = 0 := by rw [hdet_sq, hdet_sub_sq]; ring
  have hdet : N.det = 1 := by
    apply sub_eq_zero.mp
    apply (isUnit_of_invertible (2 : R)).mul_left_cancel
    simpa only [mul_zero] using htwo
  exact ⟨⟨N, (Matrix.mem_specialOrthogonalGroup_iff).mpr
    ⟨(Matrix.mem_orthogonalGroup_iff n R).mpr hN_orthogonal, hdet⟩⟩,
    Subtype.ext <| by rw [coe_map]; exact hN_map⟩

end Matrix.SpecialOrthogonalGroup
