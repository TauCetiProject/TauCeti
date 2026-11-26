/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Transvections along an inner product

In a real inner product space `E`, the transvection `x ↦ x + ⟪ν, x⟫ s` is Mathlib's
`LinearMap.transvection (innerₛₗ ℝ ν) s`, as a continuous linear map. When `⟪ν, s⟫ = 0` it is a
shear along the hyperplane `ν⊥`: it fixes `ν⊥` pointwise, preserves `⟪ν, ·⟫`, has determinant one
and inverse `x ↦ x - ⟪ν, x⟫ s`.

## Main declarations

* `TauCeti.transvectionL`: the transvection `x ↦ x + ⟪ν, x⟫ s` as a continuous linear map.
* `TauCeti.coe_transvectionL`: its underlying linear map is `LinearMap.transvection`.
* `TauCeti.transvectionL_apply_of_inner_eq_zero` and `TauCeti.inner_transvectionL`: it fixes `ν⊥`
  pointwise and, for `⟪μ, s⟫ = 0`, preserves `⟪μ, ·⟫`.
* `TauCeti.transvectionL_transvectionL_neg`, `TauCeti.transvectionL_comp_transvectionL_neg`,
  `TauCeti.transvectionL_neg_comp_transvectionL` and `TauCeti.transvectionEquivL`: for
  `⟪ν, s⟫ = 0` its inverse is the transvection along `-s`, and it is a continuous linear
  equivalence.
* `TauCeti.injective_transvectionL`: for `⟪ν, s⟫ = 0` it is injective.
* `TauCeti.det_transvectionL`: its determinant is `1 + ⟪ν, s⟫`.
* `TauCeti.abs_det_fderiv_transvectionL`: for `⟪ν, s⟫ = 0` its derivative has determinant of
  absolute value one, as the change of variables formula uses it.
* `TauCeti.adjoint_transvectionL`: its adjoint is the transvection with `ν` and `s` exchanged.
* `TauCeti.norm_transvectionL_le`: its operator norm is at most `1 + ‖ν‖ ‖s‖`.
-/

public section

noncomputable section

open InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **transvection** `x ↦ x + ⟪ν, x⟫ s` as a continuous linear map; its underlying linear map
is `LinearMap.transvection (innerₛₗ ℝ ν) s` (`TauCeti.coe_transvectionL`). -/
def transvectionL (ν s : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + (innerSL ℝ ν).smulRight s

/-- The transvection `TauCeti.transvectionL ν s` sends `x` to `x + ⟪ν, x⟫ s`. -/
@[simp]
theorem transvectionL_apply (ν s x : E) : transvectionL ν s x = x + ⟪ν, x⟫_ℝ • s := by
  rw [transvectionL, add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

/-- The transvection along an inner product is Mathlib's `LinearMap.transvection`. -/
theorem coe_transvectionL (ν s : E) :
    (transvectionL ν s : E →ₗ[ℝ] E) = LinearMap.transvection (innerₛₗ ℝ ν) s :=
  LinearMap.ext fun x => by
    rw [ContinuousLinearMap.coe_coe, transvectionL_apply, LinearMap.transvection.apply,
      innerₛₗ_apply_apply]

/-- The transvection `x ↦ x + ⟪ν, x⟫ s` fixes every `x` with `⟪ν, x⟫ = 0`. -/
theorem transvectionL_apply_of_inner_eq_zero (s : E) {ν x : E} (hx : ⟪ν, x⟫_ℝ = 0) :
    transvectionL ν s x = x := by
  rw [transvectionL_apply, hx, zero_smul, add_zero]

/-- For `⟪μ, s⟫ = 0`, the transvection `x ↦ x + ⟪ν, x⟫ s` preserves `⟪μ, ·⟫`; in particular,
for `⟪ν, s⟫ = 0` it preserves `⟪ν, ·⟫`. -/
theorem inner_transvectionL {μ ν s : E} (h : ⟪μ, s⟫_ℝ = 0) (x : E) :
    ⟪μ, transvectionL ν s x⟫_ℝ = ⟪μ, x⟫_ℝ := by
  rw [transvectionL_apply, inner_add_right, inner_smul_right, h, mul_zero, add_zero]

/-- For `⟪ν, s⟫ = 0`, the transvection along `-s` inverts the transvection along `s`. -/
theorem transvectionL_transvectionL_neg {ν s : E} (h : ⟪ν, s⟫_ℝ = 0) (x : E) :
    transvectionL ν s (transvectionL ν (-s) x) = x := by
  rw [← ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.coe_coe (transvectionL ν (-s)),
    coe_transvectionL, coe_transvectionL,
    LinearMap.transvection.comp_of_left_eq_apply
      (by rw [innerₛₗ_apply_apply, inner_neg_right, h, neg_zero]), add_neg_cancel,
    LinearMap.transvection.of_right_eq_zero, LinearMap.id_apply]

/-- For `⟪ν, s⟫ = 0`, the transvection along `s` composed after the one along `-s` is the
identity. -/
theorem transvectionL_comp_transvectionL_neg {ν s : E} (h : ⟪ν, s⟫_ℝ = 0) :
    transvectionL ν s ∘L transvectionL ν (-s) = ContinuousLinearMap.id ℝ E :=
  ContinuousLinearMap.ext (transvectionL_transvectionL_neg h)

/-- For `⟪ν, s⟫ = 0`, the transvection along `-s` composed after the one along `s` is the
identity. -/
theorem transvectionL_neg_comp_transvectionL {ν s : E} (h : ⟪ν, s⟫_ℝ = 0) :
    transvectionL ν (-s) ∘L transvectionL ν s = ContinuousLinearMap.id ℝ E := by
  simpa using
    transvectionL_comp_transvectionL_neg (s := -s) (by rw [inner_neg_right, h, neg_zero])

/-- For `⟪ν, s⟫ = 0`, the transvection `x ↦ x + ⟪ν, x⟫ s` as a continuous linear equivalence,
with inverse the transvection along `-s`. -/
def transvectionEquivL {ν s : E} (h : ⟪ν, s⟫_ℝ = 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofContinuousLinearMap (transvectionL ν s) (transvectionL ν (-s))
    (transvectionL_comp_transvectionL_neg h) (transvectionL_neg_comp_transvectionL h)

/-- The equivalence `TauCeti.transvectionEquivL` applies the transvection along `s`. -/
@[simp]
theorem transvectionEquivL_apply {ν s : E} (h : ⟪ν, s⟫_ℝ = 0) (x : E) :
    transvectionEquivL h x = transvectionL ν s x := by
  rw [transvectionEquivL, ContinuousLinearEquiv.coe_ofContinuousLinearMap]

/-- The inverse of `TauCeti.transvectionEquivL` is the transvection along `-s`. -/
@[simp]
theorem transvectionEquivL_symm_apply {ν s : E} (h : ⟪ν, s⟫_ℝ = 0) (x : E) :
    (transvectionEquivL h).symm x = transvectionL ν (-s) x := by
  rw [transvectionEquivL, ContinuousLinearEquiv.symm_ofContinuousLinearMap,
    ContinuousLinearEquiv.coe_ofContinuousLinearMap]

/-- For `⟪ν, s⟫ = 0`, the transvection `x ↦ x + ⟪ν, x⟫ s` is injective. -/
theorem injective_transvectionL {ν s : E} (h : ⟪ν, s⟫_ℝ = 0) :
    Function.Injective (transvectionL ν s) := fun x y hxy => by
  rw [← transvectionEquivL_apply h x, ← transvectionEquivL_apply h y] at hxy
  exact (transvectionEquivL h).injective hxy

/-- The transvection `x ↦ x + ⟪ν, x⟫ s` has determinant `1 + ⟪ν, s⟫`. -/
@[simp]
theorem det_transvectionL [FiniteDimensional ℝ E] (ν s : E) :
    (transvectionL ν s).det = 1 + ⟪ν, s⟫_ℝ := by
  rw [ContinuousLinearMap.det, coe_transvectionL, LinearMap.transvection.det,
    innerₛₗ_apply_apply]

/-- For `⟪ν, s⟫ = 0`, the derivative of the transvection `x ↦ x + ⟪ν, x⟫ s`, which is the
transvection itself, has determinant of absolute value one. -/
theorem abs_det_fderiv_transvectionL [FiniteDimensional ℝ E] {ν s : E} (h : ⟪ν, s⟫_ℝ = 0)
    (x : E) : |(fderiv ℝ (transvectionL ν s) x).det| = 1 := by
  rw [ContinuousLinearMap.fderiv, det_transvectionL, h, add_zero, abs_one]

/-- The adjoint of the transvection `x ↦ x + ⟪ν, x⟫ s` is `x ↦ x + ⟪s, x⟫ ν`. -/
theorem adjoint_transvectionL [CompleteSpace E] (ν s : E) :
    ContinuousLinearMap.adjoint (transvectionL ν s) = transvectionL s ν := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_).symm
  simp only [transvectionL_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm s x]
  ring

/-- The transvection `x ↦ x + ⟪ν, x⟫ s` has operator norm at most `1 + ‖ν‖ ‖s‖`. -/
theorem norm_transvectionL_le (ν s : E) : ‖transvectionL ν s‖ ≤ 1 + ‖ν‖ * ‖s‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [transvectionL_apply]
  calc ‖x + ⟪ν, x⟫_ℝ • s‖ ≤ ‖x‖ + ‖ν‖ * ‖x‖ * ‖s‖ := by
        refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (abs_real_inner_le_norm ν x) (norm_nonneg _)
    _ = (1 + ‖ν‖ * ‖s‖) * ‖x‖ := by ring

end TauCeti
