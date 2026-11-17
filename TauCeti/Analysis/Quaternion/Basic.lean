/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Quaternionic inner-product spaces

This file develops basic facts about a real seminormed inner-product space with a norm-compatible
right action by the quaternions. Right multiplication by quaternions scales inner products. For a
unit vector in a seminormed module, it gives a linear isometry from the quaternions onto the
corresponding quaternionic line, without requiring an inner product. The file also records the
real dimension of a finite quaternionic coordinate space, finds unit vectors orthogonal to a
quaternionic line in real dimension above four, and packages the standard basis
`1, i, j, k` of the quaternions as an orthonormal basis.

## Main declarations

* `TauCeti.inner_op_smul_op_smul`: right multiplication by quaternions scales inner products.
* `TauCeti.inner_op_smul_self_left_eq_zero_iff`: multiplication by a quaternion is orthogonal to a
  vector with nonzero seminorm exactly when the quaternion is purely imaginary.
* `TauCeti.quaternionLineIsometry`: the quaternionic line through a unit vector is linearly
  isometric to the quaternions.
* `TauCeti.orthonormal_op_smul`: right multiplication of a unit vector carries orthonormal
  families of quaternions to orthonormal families.
* `TauCeti.exists_norm_eq_one_forall_inner_op_smul_eq_zero`: in real dimension greater than four,
  every quaternionic line has an orthogonal unit vector.
* `TauCeti.finrank_piLp_quaternion`: a finite quaternionic coordinate space has real dimension
  four times the number of coordinates.
* `Quaternion.orthonormalBasisOneIJK`: the basis `1, i, j, k` of `ℍ` as an orthonormal basis.
* `Quaternion.normSq_inv_norm_smul_star`, `Quaternion.mul_inv_norm_smul_star`: for nonzero `q`,
  normalizing `star q` by `‖q‖⁻¹` gives a unit quaternion, and right multiplication by it sends any
  `q` to the nonnegative real quaternion `‖q‖`.
-/

public section

open Module MulOpposite Quaternion
open scoped RealInnerProductSpace RightActions ENNReal

/-- The basis `1, i, j, k` of the quaternions, as an orthonormal basis for the real inner
product. Its coordinate isometry is `Quaternion.linearIsometryEquivTuple`. -/
noncomputable def Quaternion.orthonormalBasisOneIJK : OrthonormalBasis (Fin 4) ℝ ℍ :=
  .ofRepr linearIsometryEquivTuple

@[simp]
theorem Quaternion.orthonormalBasisOneIJK_repr :
    orthonormalBasisOneIJK.repr = linearIsometryEquivTuple :=
  (rfl)

@[simp]
theorem Quaternion.coe_orthonormalBasisOneIJK :
    (orthonormalBasisOneIJK : Fin 4 → ℍ) = ![1, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] := by
  ext n : 1
  rw [← orthonormalBasisOneIJK.repr_symm_single, orthonormalBasisOneIJK_repr]
  fin_cases n <;> ext <;> simp

@[simp]
theorem Quaternion.toBasis_orthonormalBasisOneIJK :
    orthonormalBasisOneIJK.toBasis = QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) := by
  refine Module.Basis.eq_of_apply_eq fun n ↦ ?_
  rw [OrthonormalBasis.coe_toBasis, coe_orthonormalBasisOneIJK]
  fin_cases n <;> ext <;> simp [QuaternionAlgebra.basisOneIJK, Module.Basis.coe_ofEquivFun]

/-- For any nonzero Hamilton quaternion `q`, `(‖q‖⁻¹ : ℝ) • star q` has unit norm square. -/
theorem Quaternion.normSq_inv_norm_smul_star {q : ℍ} (hq : q ≠ 0) :
    normSq ((‖q‖⁻¹ : ℝ) • star q) = 1 := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
  rw [normSq_smul, normSq_star, normSq_eq_norm_mul_self]
  field_simp

/-- Multiplying a Hamilton quaternion `q` on the right by `(‖q‖⁻¹ : ℝ) • star q` yields the
nonnegative real quaternion `‖q‖`. -/
theorem Quaternion.mul_inv_norm_smul_star (q : ℍ) :
    q * ((‖q‖⁻¹ : ℝ) • star q) = ((‖q‖ : ℝ) : ℍ) := by
  by_cases hq : q = 0
  · simp [hq]
  · have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
    rw [mul_smul_comm, self_mul_star, normSq_eq_norm_mul_self, ← coe_mul_eq_smul, ← coe_mul,
      ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

namespace TauCeti

variable {E : Type*}
variable [SeminormedAddCommGroup E] [Module ℍᵐᵒᵖ E] [NormSMulClass ℍᵐᵒᵖ E]

section InnerProductSpace

variable [InnerProductSpace ℝ E]

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

/-- Right multiplication of a vector `x` with nonzero seminorm by `q` is orthogonal to `x` exactly
when `q` is purely imaginary. -/
theorem inner_op_smul_self_left_eq_zero_iff {x : E} (hx : ‖x‖ ≠ 0) (q : ℍ) :
    ⟪x <• q, x⟫ = 0 ↔ q.re = 0 := by
  simp [hx]

/-- Right multiplication of a unit vector carries an orthonormal family of quaternions to an
orthonormal family of vectors. -/
theorem orthonormal_op_smul {x : E} (hx : ‖x‖ = 1) {ι : Type*} {v : ι → ℍ}
    (hv : Orthonormal ℝ v) : Orthonormal ℝ fun i ↦ x <• v i := by
  classical
  simpa [orthonormal_iff_ite, hx] using hv

end InnerProductSpace

section LineIsometry

variable [Module ℝ E] [IsScalarTower ℝ ℍᵐᵒᵖ E]

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

section OrthogonalLine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Module ℍᵐᵒᵖ F]
  [IsScalarTower ℝ ℍᵐᵒᵖ F]

/-- In real dimension greater than four, every quaternionic line `{x <• a}` has an orthogonal unit
vector: the line is the image of the four-dimensional space `ℍ` under a real-linear map, so its
orthogonal complement is nontrivial. -/
theorem exists_norm_eq_one_forall_inner_op_smul_eq_zero (h : 4 < Module.rank ℝ F) (x : F) :
    ∃ w : F, ‖w‖ = 1 ∧ ∀ a : ℍ, ⟪x <• a, w⟫ = 0 := by
  let L : ℍ →ₗ[ℝ] F := (opLinearEquiv ℝ).toLinearMap.smulRight x
  let K := LinearMap.range L
  obtain ⟨w, hw, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := Kᗮ) fun hK ↦ by
    have hle : Module.rank ℝ F ≤ 4 := by
      rw [← rank_top ℝ F, ← Submodule.orthogonal_eq_bot_iff.1 hK, ← Module.finrank_eq_rank]
      exact_mod_cast L.finrank_range_le.trans_eq Quaternion.finrank_eq_four
    exact (h.trans_le hle).false
  refine ⟨(‖w‖⁻¹ : ℝ) • w, norm_smul_inv_norm hw₀, fun a ↦ ?_⟩
  have hL : L a = x <• a := by simp [L, LinearMap.smulRight_apply]
  rw [inner_smul_right, ← hL,
    Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self L a) hw, mul_zero]

end OrthogonalLine

/-- The quaternionic coordinate space `PiLp p (fun _ : ι ↦ ℍ)` has real dimension
`4 * Fintype.card ι` for every `p`. -/
theorem finrank_piLp_quaternion (p : ℝ≥0∞) (ι : Type*) [Fintype ι] :
    finrank ℝ (PiLp p fun _ : ι ↦ ℍ) = 4 * Fintype.card ι := by
  rw [(WithLp.linearEquiv p ℝ _).finrank_eq, Module.finrank_pi_fintype]
  simp [Quaternion.finrank_eq_four, mul_comm]

end TauCeti
