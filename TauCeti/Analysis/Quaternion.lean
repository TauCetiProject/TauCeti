/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion

/-!
# Quaternionic inner-product spaces

This file develops basic facts about a real inner-product space with a norm-compatible right
action by the quaternions. Right multiplication by quaternions scales inner products, and for a
unit vector it gives a linear isometry from the quaternions onto the corresponding quaternionic
line. The file also records the real dimension of a finite quaternionic coordinate space.

## Main declarations

* `TauCeti.inner_op_smul_op_smul`: right multiplication by quaternions scales inner products.
* `TauCeti.inner_op_smul_self_left_eq_zero_iff`: multiplication by a quaternion is orthogonal to a
  nonzero vector exactly when the quaternion is purely imaginary.
* `TauCeti.quaternionLineIsometry`: the quaternionic line through a unit vector is linearly
  isometric to the quaternions.
* `TauCeti.orthonormal_op_smul`: right multiplication of a unit vector carries orthonormal
  families of quaternions to orthonormal families.
* `TauCeti.finrank_piLp_quaternion`: a finite quaternionic coordinate space has real dimension
  four times the number of coordinates.
-/

public section

open Module MulOpposite Quaternion
open scoped RealInnerProductSpace RightActions ENNReal

namespace TauCeti

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Module ℍᵐᵒᵖ E] [NormSMulClass ℍᵐᵒᵖ E]

/-- Right multiplication by quaternions scales inner products by the square of the norm:
`⟪x <• p, x <• q⟫ = ‖x‖ ^ 2 * ⟪p, q⟫`. -/
@[simp]
theorem inner_op_smul_op_smul (x : E) (p q : ℍ) :
    ⟪x <• p, x <• q⟫ = ‖x‖ ^ 2 * ⟪p, q⟫ := by
  have hnorm (r : ℍ) : ‖x <• r‖ = ‖r‖ * ‖x‖ := by rw [norm_smul, norm_op]
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two p q,
    ← add_smul, ← op_add, hnorm, hnorm, hnorm]
  ring

/-- The inner product of `x <• q` with `x` is `‖x‖ ^ 2` times the real part of `q`. -/
@[simp]
theorem inner_op_smul_self_left (x : E) (q : ℍ) : ⟪x <• q, x⟫ = ‖x‖ ^ 2 * q.re := by
  simpa [inner_def] using inner_op_smul_op_smul x q 1

/-- Right multiplication of a nonzero vector `x` by `q` is orthogonal to `x` exactly when `q` is
purely imaginary. -/
theorem inner_op_smul_self_left_eq_zero_iff {x : E} (hx : x ≠ 0) (q : ℍ) :
    ⟪x <• q, x⟫ = 0 ↔ q.re = 0 := by
  simp [hx]

section LineIsometry

variable [IsScalarTower ℝ ℍᵐᵒᵖ E]

/-- For a unit vector `x`, right multiplication `q ↦ x <• q` is a linear isometry from the
quaternions onto the quaternionic line through `x`. -/
noncomputable def quaternionLineIsometry {x : E} (hx : ‖x‖ = 1) : ℍ →ₗᵢ[ℝ] E where
  toLinearMap := (opLinearEquiv ℝ).toLinearMap.smulRight x
  norm_map' q := by simp [norm_smul, norm_op, hx]

@[simp]
theorem quaternionLineIsometry_apply {x : E} (hx : ‖x‖ = 1) (q : ℍ) :
    quaternionLineIsometry hx q = x <• q :=
  (rfl)

end LineIsometry

/-- Right multiplication of a unit vector carries an orthonormal family of quaternions to an
orthonormal family of vectors. -/
theorem orthonormal_op_smul {x : E} (hx : ‖x‖ = 1) {ι : Type*} {v : ι → ℍ}
    (hv : Orthonormal ℝ v) : Orthonormal ℝ fun i ↦ x <• v i := by
  classical
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  simp [hx, hv]

/-- The quaternionic coordinate space `PiLp p (fun _ : ι ↦ ℍ)` has real dimension
`4 * Fintype.card ι` for every `p`. -/
theorem finrank_piLp_quaternion (p : ℝ≥0∞) (ι : Type*) [Fintype ι] :
    finrank ℝ (PiLp p fun _ : ι ↦ ℍ) = 4 * Fintype.card ι := by
  rw [(WithLp.linearEquiv p ℝ _).finrank_eq, Module.finrank_pi_fintype]
  simp [Quaternion.finrank_eq_four, mul_comm]

end TauCeti
