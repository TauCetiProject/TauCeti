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
from `SL₂(ℤ)` to `SL₂(R)`, and that `S` and `U = T S` generate `SL₂(ℤ)`.

## Main declarations

* `TauCeti.Matrix.SpecialLinearGroup.coe_modularGroup_S`: the scalar extension of
  `ModularGroup.S` has matrix `!![0, -1; 1, 0]`.
* `TauCeti.Matrix.SpecialLinearGroup.closure_S_T_mul_S`: `S` and `T S` generate `SL₂(ℤ)`; this
  follows from Mathlib's `Matrix.SpecialLinearGroup.SL2Z_generators` for `S` and `T`, since
  `T = (T S) S⁻¹`.
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

end TauCeti.Matrix.SpecialLinearGroup
