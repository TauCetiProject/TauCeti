/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# The modular-group generators in special linear groups

This module records the matrix of the standard modular-group generator `S` after scalar extension
from `SL₂(ℤ)` to `SL₂(R)`, and that `S` and `U = T S` generate `SL₂(ℤ)`. It also records the right
action `r ↦ r γ` of a special linear group on row vectors through a ring homomorphism of the
entries: it composes as a right action, and for `S` and `T` it is explicit.

## Main declarations

* `TauCeti.Matrix.SpecialLinearGroup.coe_modularGroup_S`: the scalar extension of
  `ModularGroup.S` has matrix `!![0, -1; 1, 0]`.
* `TauCeti.Matrix.SpecialLinearGroup.closure_S_T_mul_S`: `S` and `T S` generate `SL₂(ℤ)`; this
  follows from Mathlib's `Matrix.SpecialLinearGroup.SL2Z_generators` for `S` and `T`, since
  `T = (T S) S⁻¹`.
* `TauCeti.Matrix.SpecialLinearGroup.vecMul_map_mul`: the row action of `g * h` is the row action
  of `g` followed by that of `h`.
* `TauCeti.Matrix.SpecialLinearGroup.vecMul_map_modularGroup_S`,
  `TauCeti.Matrix.SpecialLinearGroup.vecMul_map_modularGroup_T`: `r S = (r₂, -r₁)` and
  `r T = (r₁, r₁ + r₂)`.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.Matrix.SpecialLinearGroup

universe u

/-- The scalar extension of `ModularGroup.S` to a commutative ring has its standard matrix. -/
theorem coe_modularGroup_S {R : Type u} [CommRing R] :
    (((ModularGroup.S : SL(2, ℤ)) : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) =
      !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_matrix_coe, ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

open ModularGroup in
/-- `S` and `U = T S` generate `SL₂(ℤ)`. -/
theorem closure_S_T_mul_S : Subgroup.closure {S, T * S} = (⊤ : Subgroup SL(2, ℤ)) := by
  rw [eq_top_iff, ← SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
  have hS : S ∈ Subgroup.closure {S, T * S} := Subgroup.subset_closure (by simp)
  have hU : T * S ∈ Subgroup.closure {S, T * S} := Subgroup.subset_closure (by simp)
  -- `T = (T S) S⁻¹`
  exact Set.pair_subset hS (by simpa using mul_mem hU (inv_mem hS))

section RowAction

variable {n : Type*} [Fintype n] [DecidableEq n] {A R : Type*} [CommRing A] [CommRing R]

/-- The right action of a special linear group on row vectors, through a ring homomorphism of the
entries, composes as a right action: `r (g h) = (r g) h`. -/
theorem vecMul_map_mul (f : A →+* R) (r : n → R) (g h : Matrix.SpecialLinearGroup n A) :
    r ᵥ* (↑(g * h) : Matrix n n A).map f =
      (r ᵥ* (g : Matrix n n A).map f) ᵥ* (h : Matrix n n A).map f := by
  rw [vecMul_vecMul, ← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul]

/-- Acting on a row vector by `g⁻¹` and then by `g` gives back the row vector: `(r g⁻¹) g = r`. -/
theorem vecMul_map_inv_vecMul_map (f : A →+* R) (r : n → R) (g : Matrix.SpecialLinearGroup n A) :
    (r ᵥ* (↑g⁻¹ : Matrix n n A).map f) ᵥ* (g : Matrix n n A).map f = r := by
  rw [← vecMul_map_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.map_one _ (map_zero _) (map_one _), vecMul_one]

end RowAction

/-- The row vector `r` multiplied on the right by `S = [[0, -1], [1, 0]]` is `(r₂, -r₁)`. -/
theorem vecMul_map_modularGroup_S {R : Type u} [CommRing R] (r : Fin 2 → R) :
    r ᵥ* (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom R) = ![r 1, -r 0] := by
  ext i
  fin_cases i <;> simp [ModularGroup.coe_S, vecMul, dotProduct, Fin.sum_univ_two]

/-- The row vector `r` multiplied on the right by `T = [[1, 1], [0, 1]]` is `(r₁, r₁ + r₂)`. -/
theorem vecMul_map_modularGroup_T {R : Type u} [CommRing R] (r : Fin 2 → R) :
    r ᵥ* (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom R) =
      ![r 0, r 0 + r 1] := by
  ext i
  fin_cases i <;> simp [ModularGroup.coe_T, vecMul, dotProduct, Fin.sum_univ_two]

end TauCeti.Matrix.SpecialLinearGroup
