/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Multiplication operators in seminormed algebras

This file identifies the underlying linear maps of bounded left and right multiplication,
and evaluates their powers. These identities connect the bounded-operator API with the
algebraic multiplication maps and allow power-series calculations on multiplication operators.
For unital algebras we also bundle the left regular representation as a unital algebra
homomorphism and give its inverse norm bound without assuming that the identity has norm one.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜]

section NonUnital

variable [NonUnitalSeminormedRing R] [NormedSpace 𝕜 R]
  [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R]

/-- The underlying linear map of bounded left multiplication is algebraic left multiplication. -/
@[simp]
theorem toLinearMap_mul_eq_mulLeft (x : R) :
    (mul 𝕜 R x).toLinearMap = LinearMap.mulLeft 𝕜 x := by
  ext y
  simp

/-- The underlying linear map of bounded right multiplication is algebraic right multiplication. -/
@[simp]
theorem toLinearMap_flip_mul_eq_mulRight (x : R) :
    ((mul 𝕜 R).flip x).toLinearMap = LinearMap.mulRight 𝕜 x := by
  ext y
  simp

end NonUnital

section Unital

variable [SeminormedRing R] [NormedSpace 𝕜 R]
  [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R]

/-- A power of bounded left multiplication acts by the corresponding algebra power. -/
-- Simplify before the generic operator-power rule rewrites the application as an iterate.
@[simp↓]
theorem mul_pow_apply (x y : R) (n : ℕ) :
    ((mul 𝕜 R x) ^ n) y = x ^ n * y := by
  -- Transport the linear-map power identity through the explicit bundling boundary.
  rw [← coe_coe, toLinearMap_pow, toLinearMap_mul_eq_mulLeft,
    LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]

/-- A power of bounded right multiplication acts by the corresponding algebra power. -/
@[simp↓]
theorem flip_mul_pow_apply (x y : R) (n : ℕ) :
    (((mul 𝕜 R).flip x) ^ n) y = y * x ^ n := by
  -- Transport the linear-map power identity through the explicit bundling boundary.
  rw [← coe_coe, toLinearMap_pow, toLinearMap_flip_mul_eq_mulRight,
    LinearMap.pow_mulRight, LinearMap.mulRight_apply]

/-- Evaluation at the identity bounds an element by its left multiplication operator,
without normalizing the norm of the identity. -/
theorem norm_le_opNorm_mul_apply_mul_norm_one (x : R) :
    ‖x‖ ≤ ‖mul 𝕜 R x‖ * ‖(1 : R)‖ := by
  simpa only [mul_apply', mul_one] using (mul 𝕜 R x).le_opNorm (1 : R)

end Unital

end ContinuousLinearMap

namespace AlgHom

variable (𝕜 R : Type*) [NontriviallyNormedField 𝕜] [SeminormedRing R]
  [NormedAlgebra 𝕜 R]

/-- The unital left regular representation by bounded operators. This is the unital
version of `NonUnitalAlgHom.Lmul`. -/
noncomputable def Lmul : R →ₐ[𝕜] R →L[𝕜] R :=
  { NonUnitalAlgHom.Lmul 𝕜 R with
    map_one' := by ext x; simp
    commutes' := fun c ↦ by ext x; simp [Algebra.algebraMap_eq_smul_one] }

/-- The left regular representation has the usual continuous multiplication map as its
underlying function. -/
@[simp]
theorem coe_Lmul : ⇑(Lmul 𝕜 R) = ContinuousLinearMap.mul 𝕜 R := (rfl)

/-- The left regular representation is faithful, as can be seen by evaluation at one. -/
theorem Lmul_injective : Function.Injective (Lmul 𝕜 R) := by
  intro x y h
  simpa using DFunLike.congr_fun h (1 : R)

end AlgHom
