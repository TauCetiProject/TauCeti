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
from `SL₂(ℤ)` to `SL₂(R)`, writes it as a word in three transvections, and shows that `S` and
`U = T S` generate `SL₂(ℤ)`.

## Main declarations

* `TauCeti.Matrix.SpecialLinearGroup.coe_modularGroup_S`: the scalar extension of
  `ModularGroup.S` has matrix `!![0, -1; 1, 0]`.
* `TauCeti.Matrix.SpecialLinearGroup.modularGroup_S_decompose`: over any commutative ring,
  `S = x₀₁(-1) x₁₀(1) x₀₁(-1)` is a word in three transvections, the word that defines the Weyl
  representative `n_r(-1)` of a rank-one Chevalley group.
* `TauCeti.Matrix.SpecialLinearGroup.closure_S_T_mul_S`: `S` and `T S` generate `SL₂(ℤ)`; this
  follows from Mathlib's `Matrix.SpecialLinearGroup.SL2Z_generators` for `S` and `T`, since
  `T = (T S) S⁻¹`.
* `TauCeti.Matrix.SpecialLinearGroup.apply_smul_eq_of_S_smul_of_T_smul`: a function on an
  `SL₂(ℤ)`-set that is invariant under `S` and `T` is invariant under all of `SL₂(ℤ)`.
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

/-- The scalar extension of `ModularGroup.S` is the word `x₀₁(-1) x₁₀(1) x₀₁(-1)` in the upper
and lower transvections. -/
theorem modularGroup_S_decompose {R : Type u} [CommRing R] :
    ((ModularGroup.S : SL(2, ℤ)) : SL(2, R)) =
      Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (-1) *
        Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) 1 *
        Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (-1) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    coe_modularGroup_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

open ModularGroup in
/-- `S` and `U = T S` generate `SL₂(ℤ)`. -/
theorem closure_S_T_mul_S : Subgroup.closure {S, T * S} = (⊤ : Subgroup SL(2, ℤ)) := by
  rw [eq_top_iff, ← SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
  have hS : S ∈ Subgroup.closure {S, T * S} := Subgroup.subset_closure (by simp)
  have hU : T * S ∈ Subgroup.closure {S, T * S} := Subgroup.subset_closure (by simp)
  -- `T = (T S) S⁻¹`
  exact Set.pair_subset hS (by simpa using mul_mem hU (inv_mem hS))

open ModularGroup in
/-- A function on an `SL₂(ℤ)`-set that is invariant under the generators `S` and `T` is invariant
under all of `SL₂(ℤ)`. -/
theorem apply_smul_eq_of_S_smul_of_T_smul {X α : Type*} [MulAction SL(2, ℤ) X] {f : X → α}
    (hS : ∀ x, f (S • x) = f x) (hT : ∀ x, f (T • x) = f x) (γ : SL(2, ℤ)) (x : X) :
    f (γ • x) = f x := by
  have hγ : γ ∈ Subgroup.closure {S, T} := by simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction generalizing x with
  | one => rw [one_smul]
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact hS x
    · exact hT x
  | mul g h _ _ hg hh => rw [mul_smul, hg, hh]
  | inv g _ hg => rw [← hg, smul_inv_smul]

end TauCeti.Matrix.SpecialLinearGroup
