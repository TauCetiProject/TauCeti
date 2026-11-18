/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Calculus.FDeriv.Adjugate
import TauCeti.Analysis.Matrix.Normed

/-!
# Derivatives of inversion and maps precomposed with inversion

For a map `u` out of a normed field `𝕜'` and `w ≠ 0`, the derivative over a subfield `𝕜` of
`w ↦ u w⁻¹` at `w` is the derivative of `u` at `w⁻¹` precomposed with
multiplication by `-(w ^ 2)⁻¹`, the derivative of the inversion (`TauCeti.fderiv_comp_inv_apply`).
Multiplication by `-(w ^ 2)⁻¹` scales all norms by `‖w‖⁻²`, so the operator norm of this derivative
is that of the derivative of `u` at `w⁻¹` divided by `‖w‖ ^ 2` (`TauCeti.norm_fderiv_comp_inv`).
This is how a map near infinity is read off in the coordinate `w = z⁻¹` near zero. No
differentiability of `u` is assumed: where `u` is not differentiable at `w⁻¹`, neither is
`w ↦ u w⁻¹` at `w`, and both derivatives are `0`.

For an invertible finite matrix, inversion has differential `H ↦ -(A⁻¹ * H * A⁻¹)`.
Matrices carry the operator norm, and the scalar field need not be complete.
-/

public section

open Filter
open scoped Topology Matrix.Norms.Operator RightActions

namespace Matrix

attribute [local instance] Matrix.linftyOpTopologicalSpace

/-- At an invertible matrix, inversion has differential `H ↦ -(A⁻¹ * H * A⁻¹)`.
No scalar completeness assumption is needed. -/
theorem hasFDerivAt_inv {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι 𝕜} (hdet : IsUnit A.det) :
    HasFDerivAt (Inv.inv : Matrix ι ι 𝕜 → Matrix ι ι 𝕜)
      (-ContinuousLinearMap.mulLeftRight 𝕜 (Matrix ι ι 𝕜) A⁻¹ A⁻¹) A := by
  have hd := differentiable_det A
  have hne := hd.continuousAt.eventually_ne hdet.ne_zero
  -- Transport through the entry-function equivalence before using Pi differentiability.
  have hRows : DifferentiableAt 𝕜
      ((ofContinuousLinearEquiv 𝕜 : (ι → ι → 𝕜) ≃L[𝕜] Matrix ι ι 𝕜).symm) A :=
    (ofContinuousLinearEquiv 𝕜 : (ι → ι → 𝕜) ≃L[𝕜] Matrix ι ι 𝕜).symm.differentiableAt
  have hAdjRows : DifferentiableAt 𝕜 (fun B : Matrix ι ι 𝕜 ↦ of.symm B.adjugate) A := by
    simp only [coe_ofContinuousLinearEquiv_symm] at hRows
    exact differentiableAt_pi.mpr fun i ↦ differentiableAt_pi.mpr fun j ↦
      differentiableAt_adjugate_apply id A
        (fun k l ↦ differentiableAt_pi.mp (differentiableAt_pi.mp hRows k) l) i j
  have hAdj : DifferentiableAt 𝕜 (adjugate : Matrix ι ι 𝕜 → Matrix ι ι 𝕜) A := by
    simpa only [Function.comp_def, coe_ofContinuousLinearEquiv, Equiv.apply_symm_apply] using!
      (ofContinuousLinearEquiv 𝕜 : (ι → ι → 𝕜) ≃L[𝕜] Matrix ι ι 𝕜).differentiableAt.comp A
        hAdjRows
  have hInv : DifferentiableAt 𝕜 (fun B : Matrix ι ι 𝕜 ↦ B⁻¹) A := by
    simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Pi.inv_apply] using!
      (hd.inv hdet.ne_zero).fun_smul hAdj
  -- Differentiating B * B⁻¹ = 1 determines the differential on every direction.
  have hmul : (fun B : Matrix ι ι 𝕜 ↦ B * B⁻¹) =ᶠ[𝓝 A] fun _ ↦ 1 := by
    filter_upwards [hne] with B hB
    exact mul_nonsing_inv B hB.isUnit
  have hzero := ((hasFDerivAt_id A).fun_mul' hInv.hasFDerivAt).congr_of_eventuallyEq hmul.symm
  apply hInv.hasFDerivAt.congr_fderiv
  ext1 H
  have hz : H * A⁻¹ + A * fderiv 𝕜 Inv.inv A H = 0 := by
    have h := congrArg (fun L : Matrix ι ι 𝕜 →L[𝕜] Matrix ι ι 𝕜 ↦ L H)
      (hzero.unique (hasFDerivAt_const (1 : Matrix ι ι 𝕜) A))
    simpa [_root_.add_apply (β := Matrix ι ι 𝕜),
      _root_.smul_apply (β := Matrix ι ι 𝕜), smul_eq_mul, op_smul_eq_mul,
      ContinuousLinearMap.id_apply, add_comm] using! h
  have hz' := congrArg (fun M ↦ A⁻¹ * M) hz
  simpa [mul_add, ← Matrix.mul_assoc, nonsing_inv_mul _ hdet,
    eq_neg_iff_add_eq_zero, add_comm, _root_.neg_apply (β := Matrix ι ι 𝕜),
    ContinuousLinearMap.mulLeftRight_apply] using! hz'

end Matrix

namespace TauCeti

variable {𝕜 𝕜' F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of `w ↦ u w⁻¹` at `w ≠ 0` is the derivative of `u` at `w⁻¹` precomposed with
multiplication by `-(w ^ 2)⁻¹`. -/
theorem fderiv_comp_inv_apply {u : 𝕜' → F} {w : 𝕜'} (hw : w ≠ 0) (h : 𝕜') :
    fderiv 𝕜 (fun w ↦ u w⁻¹) w h = fderiv 𝕜 u w⁻¹ (-(w ^ 2)⁻¹ * h) := by
  by_cases hu : DifferentiableAt 𝕜 u w⁻¹
  · have hinv : HasFDerivAt (fun w : 𝕜' ↦ w⁻¹)
        ((ContinuousLinearMap.smulRight (1 : 𝕜' →L[𝕜'] 𝕜') (-(w ^ 2)⁻¹)).restrictScalars 𝕜) w :=
      (hasDerivAt_inv hw).hasFDerivAt.restrictScalars 𝕜
    have hv : HasFDerivAt (fun w ↦ u w⁻¹) ((fderiv 𝕜 u w⁻¹).comp
        ((ContinuousLinearMap.smulRight (1 : 𝕜' →L[𝕜'] 𝕜') (-(w ^ 2)⁻¹)).restrictScalars 𝕜)) w :=
      hu.hasFDerivAt.comp w hinv
    rw [hv.fderiv]
    simp [mul_comm]
  · -- `u` is `w ↦ u w⁻¹` precomposed with the inversion, so neither map is differentiable.
    have hv : ¬DifferentiableAt 𝕜 (fun w ↦ u w⁻¹) w := fun hv ↦ hu <| by
      have hinv : DifferentiableAt 𝕜 (fun w : 𝕜' ↦ w⁻¹) w⁻¹ :=
        ((hasDerivAt_inv (inv_ne_zero hw)).hasFDerivAt.restrictScalars 𝕜).differentiableAt
      rw [← inv_inv w] at hv
      simpa [Function.comp_def] using hv.comp w⁻¹ hinv
    simp [fderiv_zero_of_not_differentiableAt hu, fderiv_zero_of_not_differentiableAt hv]

/-- The operator norm of the derivative of `w ↦ u w⁻¹` at `w ≠ 0` is that of the derivative of `u`
at `w⁻¹`, divided by `‖w‖ ^ 2`: the derivative of the inversion multiplies every vector by
`-(w ^ 2)⁻¹`, which scales all norms by the same factor. -/
theorem norm_fderiv_comp_inv {u : 𝕜' → F} {w : 𝕜'} (hw : w ≠ 0) :
    ‖fderiv 𝕜 (fun w ↦ u w⁻¹) w‖ = ‖fderiv 𝕜 u w⁻¹‖ / ‖w‖ ^ 2 := by
  have hc0 : -(w ^ 2)⁻¹ ≠ 0 := by simp [hw]
  have hc : ‖-(w ^ 2)⁻¹‖ = (‖w‖ ^ 2)⁻¹ := by rw [norm_neg, norm_inv, norm_pow]
  rw [div_eq_mul_inv, ← hc]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_) ?_
  · rw [fderiv_comp_inv_apply hw, mul_assoc, ← norm_mul]
    exact (fderiv 𝕜 u w⁻¹).le_opNorm _
  · -- Every value of `fderiv u w⁻¹` is a value of the derivative of `w ↦ u w⁻¹`.
    have hle : ‖fderiv 𝕜 u w⁻¹‖ ≤ ‖fderiv 𝕜 (fun w ↦ u w⁻¹) w‖ * ‖-(w ^ 2)⁻¹‖⁻¹ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
      have h' := fderiv_comp_inv_apply (𝕜 := 𝕜) (u := u) hw ((-(w ^ 2)⁻¹)⁻¹ * h)
      rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at h'
      rw [← h', mul_assoc, ← norm_inv, ← norm_mul]
      exact (fderiv 𝕜 (fun w ↦ u w⁻¹) w).le_opNorm _
    calc ‖fderiv 𝕜 u w⁻¹‖ * ‖-(w ^ 2)⁻¹‖
        ≤ ‖fderiv 𝕜 (fun w ↦ u w⁻¹) w‖ * ‖-(w ^ 2)⁻¹‖⁻¹ * ‖-(w ^ 2)⁻¹‖ := by gcongr
      _ = ‖fderiv 𝕜 (fun w ↦ u w⁻¹) w‖ := by field_simp

end TauCeti
