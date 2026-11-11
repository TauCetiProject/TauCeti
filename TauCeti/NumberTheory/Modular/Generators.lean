/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Modular.Relations
public import TauCeti.GroupTheory.TriangleGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Pinned generators of the modular triangle group

The integral matrices `R = S T` and `U = S T⁻¹` have different central signs:
`R³ = -I`, whereas `U³ = I`. Their projective classes both have order three.
Together with the class of `S` of order two and the infinite-order class of `T`,
these give the surjection `modularHom : TriangleGroup 3 2 0 →* PSL(2, ℤ)` sending
`x, y, z` to `U, S, T`. This convention makes the cusp generator the positive
translation and fixes the product relation `T S U = 1` projectively, as needed
for coset permutation triples.

We use Mathlib's quotient projection and coercion into `PSL(2, ℤ)` directly.
The center is already described by
`Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one`, and the
projective relations for `S` come from `TauCeti.NumberTheory.Modular.Relations`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VII, §1.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-- The integral generator `R = S T`, whose cube is `-I`. -/
def R : SL(2, ℤ) := S * T

/-- The integral generator `U = S T⁻¹`, whose cube is `I`. -/
def U : SL(2, ℤ) := S * T⁻¹

/-- The pinned product convention for `R`. -/
theorem R_def : R = S * T := (rfl)

/-- The pinned product convention for `U`. -/
theorem U_def : U = S * T⁻¹ := (rfl)

/-- The matrix of `R = S T`. -/
@[simp]
theorem coe_R : (R : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 1] := by
  decide

/-- The matrix of `U = S T⁻¹`. -/
@[simp]
theorem coe_U : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, -1] := by
  decide

/-- `R³ = -I`, so the integral lift `R` does not have order three. -/
@[simp]
theorem R_pow_three : R ^ 3 = (-1 : SL(2, ℤ)) := by
  decide

/-- `R⁶ = I` in the integral modular group. -/
theorem R_pow_six : R ^ 6 = 1 := by
  calc
    R ^ 6 = (R ^ 3) ^ 2 := pow_mul R 3 2
    _ = 1 := by rw [R_pow_three]; decide

/-- Unlike `R`, the integral lift `U` already satisfies `U³ = I`. -/
@[simp]
theorem U_pow_three : U ^ 3 = 1 := by
  decide

/-- The integral generators `R⁻¹` and `U` are conjugate up to sign. -/
theorem S_mul_R_inv_mul_S_inv : S * R⁻¹ * S⁻¹ = -U := by
  decide

/-- Recovering the translation from `R`, with the inverse of `S`. -/
theorem S_inv_mul_R : S⁻¹ * R = T := by
  simp [R]

/-- Recovering the translation from `R`, with its central sign retained. -/
theorem neg_S_mul_R : -S * R = T := by
  rw [← S_inv, S_inv_mul_R]

/-- Recovering the inverse translation from `U`. -/
theorem S_inv_mul_U : S⁻¹ * U = T⁻¹ := by
  simp [U]

/-- The product of the two generators gives a conjugate of the square translation. -/
theorem R_mul_U_inv : R * U⁻¹ = S * T ^ 2 * S⁻¹ := by
  simp [R, U, pow_two, mul_assoc]

/-- The integral reversed triangle product is `-I`, not `I`. -/
theorem T_mul_S_mul_U : T * S * U = (-1 : SL(2, ℤ)) := by
  decide

/-- The projective class of `R` has cube one. -/
@[simp]
theorem coe_R_pow_three : (R : PSL(2, ℤ)) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow, R_pow_three, QuotientGroup.eq_one_iff]
  simp

/-- The projective class of `U` has cube one. -/
@[simp]
theorem coe_U_pow_three : (U : PSL(2, ℤ)) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow, U_pow_three, QuotientGroup.mk_one]

/-- The triangle relation in the convention with positive cusp translation. -/
theorem coe_T_mul_coe_S_mul_coe_U : (T : PSL(2, ℤ)) * S * U = 1 := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, T_mul_S_mul_U,
    QuotientGroup.eq_one_iff]
  simp

/-- Projectively, `U` is conjugate to the inverse of `R` by `S`. -/
theorem coe_S_mul_coe_R_inv_mul_coe_S_inv :
    (S : PSL(2, ℤ)) * (R : PSL(2, ℤ))⁻¹ * (S : PSL(2, ℤ))⁻¹ = U := by
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, S_mul_R_inv_mul_S_inv]
  apply QuotientGroup.eq.mpr
  simp [SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]

/-- The projective class of `R` has exact order three. -/
@[simp]
theorem orderOf_coe_R : orderOf (R : PSL(2, ℤ)) = 3 := by
  apply orderOf_eq_prime coe_R_pow_three
  rw [ne_eq, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  decide

/-- The projective class of `U` has exact order three. -/
@[simp]
theorem orderOf_coe_U : orderOf (U : PSL(2, ℤ)) = 3 := by
  apply orderOf_eq_prime coe_U_pow_three
  rw [ne_eq, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  decide

/-- The modular triangle homomorphism with `x ↦ U`, `y ↦ S` and `z ↦ T`. -/
def modularHom : TriangleGroup 3 2 0 →* PSL(2, ℤ) :=
  TriangleGroup.lift (U : PSL(2, ℤ)) S T coe_U_pow_three coe_S_sq (pow_zero _)
    coe_T_mul_coe_S_mul_coe_U

/-- The order-three triangle generator maps to `U`. -/
@[simp]
theorem modularHom_x : modularHom (TriangleGroup.x 3 2 0) = (U : PSL(2, ℤ)) :=
  TriangleGroup.lift_x ..

/-- The order-two triangle generator maps to `S`. -/
@[simp]
theorem modularHom_y : modularHom (TriangleGroup.y 3 2 0) = (S : PSL(2, ℤ)) :=
  TriangleGroup.lift_y ..

/-- The cusp triangle generator maps to the positive translation `T`. -/
@[simp]
theorem modularHom_z : modularHom (TriangleGroup.z 3 2 0) = (T : PSL(2, ℤ)) :=
  TriangleGroup.lift_z ..

/-- The modular triangle homomorphism is surjective. -/
theorem modularHom_surjective : Function.Surjective modularHom := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_coe_S_coe_T, Subgroup.closure_le]
  exact Set.pair_subset ⟨TriangleGroup.y 3 2 0, modularHom_y⟩
    ⟨TriangleGroup.z 3 2 0, modularHom_z⟩

end TauCeti.ModularGroup
