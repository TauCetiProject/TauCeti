/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Quaternionic tangent vector fields on the spheres `S^{4k-1}`

Let `E` be a real inner product space on which the quaternions act on the right, written
`x <• q`, with `‖x <• q‖ = ‖q‖ * ‖x‖`. The model case is the quaternionic coordinate space
`ℍ^ι = PiLp 2 (fun _ : ι => ℍ)`, of real dimension `4 * Fintype.card ι`
(`TauCeti.finrank_piLp_quaternion`), whose unit sphere is `S^{4k-1}` for `k = Fintype.card ι`.

Right multiplication by quaternions scales inner products:
`⟪x <• p, x <• q⟫ = ‖x‖ ^ 2 * ⟪p, q⟫`. So for a unit vector `x` the map `q ↦ x <• q` is a linear
isometry from `ℍ` onto the quaternionic line through `x`, and `x <• q` is orthogonal to `x`
exactly when `q` is purely imaginary. In particular the three vectors `x <• i`, `x <• j`,
`x <• k` are orthonormal and orthogonal to `x`: they are three pointwise orthonormal tangent
vector fields on the unit sphere of `E`, and they are restrictions of real-linear maps of `E`,
hence smooth. For `E = ℍ^ι` these are the classical vector fields on `S^{4k-1}` coming from
quaternionic multiplication.

Tangent vector fields on a sphere are represented, as usual in topology, by maps
`v : sphere (0 : E) 1 → E` with `⟪v x, x⟫ = 0`.

## Main declarations

* `TauCeti.inner_op_smul_op_smul`: `⟪x <• p, x <• q⟫ = ‖x‖ ^ 2 * ⟪p, q⟫`.
* `TauCeti.inner_op_smul_self_left`, `TauCeti.inner_op_smul_self_left_eq_zero_iff`:
  `⟪x <• q, x⟫ = ‖x‖ ^ 2 * q.re`, so `x <• q` is orthogonal to `x ≠ 0` if and only if `q` is
  purely imaginary.
* `TauCeti.quaternionLineIsometry`: for a unit vector `x`, the linear isometry `q ↦ x <• q` from
  `ℍ` to `E`.
* `TauCeti.orthonormal_op_smul`: right multiplication of a unit vector carries orthonormal
  families of quaternions to orthonormal families.
* `TauCeti.quaternionFrame`: the three vectors `x <• i`, `x <• j`, `x <• k`.
* `TauCeti.orthonormal_quaternionFrame`, `TauCeti.inner_quaternionFrame_self`: the three
  vectors are orthogonal to `x`, and orthonormal when `x` is a unit vector.
* `TauCeti.contDiff_quaternionFrame`, `TauCeti.contMDiff_quaternionFrame`: they are smooth on
  `E` and on the unit sphere.
* `TauCeti.finrank_piLp_quaternion`: `ℍ^ι` has real dimension `4 * Fintype.card ι`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.3.
-/

public section

open Metric Module MulOpposite Quaternion
open scoped RealInnerProductSpace RightActions Manifold ContDiff ENNReal

namespace TauCeti

variable {E : Type*}

section Frame

variable [SMul ℍᵐᵒᵖ E]

/-- The three vectors `x <• i`, `x <• j`, `x <• k` obtained from `x` by right multiplication by
the imaginary quaternion units. On the unit sphere they are three pointwise orthonormal tangent
vector fields. -/
def quaternionFrame (x : E) : Fin 3 → E :=
  ![x <• (⟨0, 1, 0, 0⟩ : ℍ), x <• (⟨0, 0, 1, 0⟩ : ℍ), x <• (⟨0, 0, 0, 1⟩ : ℍ)]

@[simp]
theorem quaternionFrame_zero (x : E) : quaternionFrame x 0 = x <• (⟨0, 1, 0, 0⟩ : ℍ) :=
  (rfl)

@[simp]
theorem quaternionFrame_one (x : E) : quaternionFrame x 1 = x <• (⟨0, 0, 1, 0⟩ : ℍ) :=
  (rfl)

@[simp]
theorem quaternionFrame_two (x : E) : quaternionFrame x 2 = x <• (⟨0, 0, 0, 1⟩ : ℍ) :=
  (rfl)

end Frame

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

/-- Each vector of the quaternionic frame of `x` is orthogonal to `x`: on the unit sphere the
frame consists of tangent vectors. -/
@[simp]
theorem inner_quaternionFrame_self (x : E) (j : Fin 3) : ⟪quaternionFrame x j, x⟫ = 0 := by
  fin_cases j <;> simp

section Smooth

variable [SMulCommClass ℝ ℍᵐᵒᵖ E]

/-- Each vector field of the quaternionic frame extends to a smooth map of `E`. -/
theorem contDiff_quaternionFrame (j : Fin 3) : ContDiff ℝ ∞ fun x : E ↦ quaternionFrame x j := by
  fin_cases j <;> exact contDiff_const_smul _

/-- Each vector field of the quaternionic frame is a smooth map on the unit sphere. -/
theorem contMDiff_quaternionFrame {n : ℕ} [Fact (finrank ℝ E = n + 1)] (j : Fin 3) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ fun x : sphere (0 : E) 1 ↦ quaternionFrame (x : E) j :=
  (contDiff_quaternionFrame j).contMDiff.comp contMDiff_coe_sphere

end Smooth

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

/-- The quaternionic frame of a unit vector is orthonormal. -/
theorem orthonormal_quaternionFrame {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ (quaternionFrame x) := by
  -- The imaginary units `i`, `j`, `k` are orthonormal in `ℍ`.
  have hijk : Orthonormal ℝ (![⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] : Fin 3 → ℍ) := by
    simp [orthonormal_iff_ite, Fin.forall_fin_succ, inner_def]
  convert orthonormal_op_smul hx hijk using 1
  ext j
  fin_cases j <;> simp

/-- The quaternionic coordinate space `PiLp p (fun _ : ι ↦ ℍ)` has real dimension
`4 * Fintype.card ι` for every `p`. For `p = 2` this is `ℍ^ι`, whose unit sphere is therefore a
sphere of dimension `4 * Fintype.card ι - 1`. -/
theorem finrank_piLp_quaternion (p : ℝ≥0∞) (ι : Type*) [Fintype ι] :
    finrank ℝ (PiLp p fun _ : ι ↦ ℍ) = 4 * Fintype.card ι := by
  rw [(WithLp.linearEquiv p ℝ _).finrank_eq, Module.finrank_pi_fintype]
  simp [Quaternion.finrank_eq_four, mul_comm]

end TauCeti
