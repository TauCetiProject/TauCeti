/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Multiplication operators in seminormed algebras

This file identifies the underlying linear maps of bounded left and right multiplication,
bounds the right-multiplication and commutator operators
(`opNorm_flip_mul_apply_le`, `opNorm_mul_sub_flip_le`), and evaluates their powers. These
identities connect the bounded-operator API with the
algebraic multiplication maps and allow power-series calculations on multiplication operators.
It also records the norm of a difference of scalar-to-vector maps, notes that every subsingleton
seminormed algebra is regular, and shows that left multiplication in a regular normed algebra is
faithful (`RegularNormedAlgebra.faithfulSMul`). On the field itself, `c • mul 𝕜 𝕜` is invertible
exactly when `c ≠ 0` (`ContinuousLinearMap.isInvertible_smul_mul_iff`).
For unital algebras we also specialize bounded two-sided multiplication `mulLeftRight` when one
factor is `1`, bundle the left regular representation as a unital algebra homomorphism, and give its
inverse norm bound without assuming that the identity has norm one.
A scalar map `T : 𝕜 →L[𝕜] 𝕜` acts on any normed space as multiplication by `T 1`
(`ContinuousLinearMap.scalarSMulL`), with the same operator norm.
Finally, exponentiating bounded left or right multiplication by `x` gives multiplication by
`exp x`, over any nontrivially normed field of characteristic zero and without completeness.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜]

/-- The operator norm of a difference of scalar-to-vector maps is the norm of the difference
of their defining vectors. -/
@[simp]
theorem norm_toSpanSingleton_sub {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (a b : E) : ‖toSpanSingleton 𝕜 a - toSpanSingleton 𝕜 b‖ = ‖a - b‖ := by
  simpa only [map_sub, toSpanSingletonLIE_apply] using
    (toSpanSingletonLIE 𝕜 E).norm_map (a - b)

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

/-- Bounded right multiplication by `x` has operator norm at most `‖x‖`. -/
theorem opNorm_flip_mul_apply_le (x : R) : ‖(mul 𝕜 R).flip x‖ ≤ ‖x‖ :=
  ((mul 𝕜 R).flip.le_opNorm x).trans <| by
    rw [opNorm_flip]
    exact mul_le_of_le_one_left (norm_nonneg x) (opNorm_mul_le 𝕜 R)

/-- The commutator operator `y ↦ x * y - y * x` has operator norm at most `2 * ‖x‖`. -/
theorem opNorm_mul_sub_flip_le (x : R) : ‖mul 𝕜 R x - (mul 𝕜 R).flip x‖ ≤ 2 * ‖x‖ :=
  (norm_sub_le _ _).trans <| by
    linarith [opNorm_mul_apply_le 𝕜 R x, opNorm_flip_mul_apply_le (𝕜 := 𝕜) x]

/-- Every subsingleton seminormed algebra is trivially regular, since both the algebra and its
bounded endomorphism ring are subsingletons. -/
instance _root_.RegularNormedAlgebra.of_subsingleton [Subsingleton R] :
    RegularNormedAlgebra 𝕜 R where
  isometry_mul' := isometry_subsingleton

end NonUnital

variable (𝕜) in
/-- Left multiplication in a regular normed algebra is faithful. -/
theorem _root_.RegularNormedAlgebra.faithfulSMul [NonUnitalNormedRing R]
    [NormedSpace 𝕜 R] [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R] [RegularNormedAlgebra 𝕜 R] :
    FaithfulSMul R R where
  eq_of_smul_eq_smul h := (isometry_mul 𝕜 R).injective <| by
    ext c
    simpa [smul_eq_mul] using h c

section Unital

variable [SeminormedRing R] [NormedSpace 𝕜 R]
  [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R]

/-- Specializing the left factor of bounded two-sided multiplication `mulLeftRight 𝕜 R` to `1`
gives the flipped (right-multiplication) operator `(mul 𝕜 R).flip`. -/
@[simp]
theorem mulLeftRight_one : mulLeftRight 𝕜 R (1 : R) = (mul 𝕜 R).flip := by
  ext y x
  simp

/-- Specializing the right factor of `mulLeftRight 𝕜 R` to `1` gives bounded left multiplication
by `x`. -/
@[simp]
theorem mulLeftRight_one_right (x : R) : mulLeftRight 𝕜 R x 1 = mul 𝕜 R x := by
  ext z
  simp

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

section ScalarSMul

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (𝕜 E) in
/-- A scalar map `T : 𝕜 →L[𝕜] 𝕜` acting on `E` as multiplication by `T 1`. -/
noncomputable def scalarSMulL : (𝕜 →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] E :=
  (lsmul 𝕜 𝕜).comp (apply 𝕜 𝕜 (1 : 𝕜))

/-- Unfolding `ContinuousLinearMap.scalarSMulL`. -/
@[simp]
theorem scalarSMulL_apply_apply (T : 𝕜 →L[𝕜] 𝕜) (v : E) : scalarSMulL 𝕜 E T v = T 1 • v :=
  (rfl)

/-- The scalar map `T` and its action on a nontrivial space have the same operator norm. -/
@[simp]
theorem norm_scalarSMulL_apply [NontrivialTopology E] (T : 𝕜 →L[𝕜] 𝕜) :
    ‖scalarSMulL 𝕜 E T‖ = ‖T‖ := by
  have h : scalarSMulL 𝕜 E T = T 1 • ContinuousLinearMap.id 𝕜 E := by
    ext v
    simp
  rw [h, norm_smul, norm_id, mul_one, ← norm_toSpanSingleton (𝕜 := 𝕜) (T 1)]
  congr 1
  ext
  simp

end ScalarSMul

/-- On the field itself, the bilinear map `(v, w) ↦ c v w`, viewed as a map into the dual, is
invertible exactly when `c ≠ 0`. -/
@[simp]
theorem isInvertible_smul_mul_iff {c : 𝕜} : (c • mul 𝕜 𝕜).IsInvertible ↔ c ≠ 0 := by
  refine ⟨fun h hc ↦ ?_, fun hc ↦ .of_inverse (g := c⁻¹ • apply 𝕜 𝕜 (1 : 𝕜)) ?_ ?_⟩
  · exact one_ne_zero (h.injective (a₁ := 1) (a₂ := 0) (by simp [hc]))
  all_goals ext; simp [hc]

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

namespace TauCeti

open NormedSpace

variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [NormedRing R]
  [NormedAlgebra 𝕜 R]

/-- Exponentiating the bounded left-multiplication operator gives the operator of left
multiplication by the algebra exponential. Completeness is not needed: evaluation at `1` is a
continuous left inverse of `ContinuousLinearMap.mul 𝕜 R`, so the exponential series of `x` and of
its left multiplication operator are summable together, and both sides are the junk value `0`
otherwise. -/
theorem exp_mulLeft (x : R) :
    exp (ContinuousLinearMap.mul 𝕜 R x) = ContinuousLinearMap.mul 𝕜 R (exp x) := by
  have hinv : Function.LeftInverse (ContinuousLinearMap.apply 𝕜 R (1 : R))
      (ContinuousLinearMap.mul 𝕜 R) := fun z => by simp
  simp only [exp_eq_tsum 𝕜]
  rw [hinv.map_tsum _ (ContinuousLinearMap.mul 𝕜 R).continuous
    (ContinuousLinearMap.apply 𝕜 R (1 : R)).continuous]
  refine tsum_congr fun n => ?_
  ext z
  simp [ContinuousLinearMap.mul_pow_apply]

/-- Exponentiating the bounded right-multiplication operator gives the operator of right
multiplication by the algebra exponential. As for `TauCeti.exp_mulLeft`, completeness is not
needed. -/
theorem exp_mulRight (x : R) :
    exp ((ContinuousLinearMap.mul 𝕜 R).flip x) =
      (ContinuousLinearMap.mul 𝕜 R).flip (exp x) := by
  have hinv : Function.LeftInverse (ContinuousLinearMap.apply 𝕜 R (1 : R))
      (ContinuousLinearMap.mul 𝕜 R).flip := fun z => by simp
  simp only [exp_eq_tsum 𝕜]
  rw [hinv.map_tsum _ (ContinuousLinearMap.mul 𝕜 R).flip.continuous
    (ContinuousLinearMap.apply 𝕜 R (1 : R)).continuous]
  refine tsum_congr fun n => ?_
  ext z
  simp [ContinuousLinearMap.flip_mul_pow_apply]

/-- Exponentiating the bounded left-multiplication operator gives left multiplication by the
algebra exponential. -/
@[simp]
theorem exp_mulLeft_apply (x y : R) :
    exp (ContinuousLinearMap.mul 𝕜 R x) y = exp x * y := by
  rw [exp_mulLeft, ContinuousLinearMap.mul_apply']

/-- Exponentiating the bounded right-multiplication operator gives right multiplication by the
algebra exponential. -/
@[simp]
theorem exp_mulRight_apply (x y : R) :
    exp ((ContinuousLinearMap.mul 𝕜 R).flip x) y = y * exp x := by
  rw [exp_mulRight, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']

end TauCeti
