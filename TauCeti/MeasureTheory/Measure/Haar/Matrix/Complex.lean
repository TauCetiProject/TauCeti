/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Change of variables for complex matrix actions on Lebesgue measure

Derives lower Lebesgue integral change-of-variables formulas for invertible complex matrices acting
on `κ → ℂ` by `mulVec` and on `ι → κ → ℂ` by affine left matrix multiplication from
`MeasureTheory.lintegral_comp_linearMap`. No measurability assumption on the integrand is needed.

## Main results

* `MeasureTheory.lintegral_comp_mulVec`: for an invertible complex matrix `u`,
  `∫⁻ y : κ → ℂ, g (u *ᵥ y) = ENNReal.ofReal (‖u.det‖⁻¹ ^ 2) * ∫⁻ y : κ → ℂ, g y`.
* `MeasureTheory.lintegral_comp_matrix_mul_add`: for an invertible complex matrix `S` and offset
  `c : Matrix ι κ ℂ`,
  `∫⁻ A : ι → κ → ℂ, g (of.symm (S * of A + c)) =`
  `ENNReal.ofReal (‖S.det‖⁻¹ ^ (2 * Fintype.card κ)) * ∫⁻ A : ι → κ → ℂ, g A`.
-/

public section

open Fintype Matrix

namespace MeasureTheory

/-- Change of variables on `κ → ℂ` for an invertible complex matrix `u`. -/
theorem lintegral_comp_mulVec {κ : Type*} [Fintype κ] [DecidableEq κ]
    {u : Matrix κ κ ℂ} (hu : u.det ≠ 0) (g : (κ → ℂ) → ENNReal) :
    ∫⁻ y : κ → ℂ, g (u *ᵥ y) = ENNReal.ofReal (‖u.det‖⁻¹ ^ 2) * ∫⁻ y : κ → ℂ, g y := by
  let f : (κ → ℂ) →ₗ[ℝ] (κ → ℂ) := u.toLin'.restrictScalars ℝ
  have hf (y : κ → ℂ) : f y = u *ᵥ y := Matrix.toLin'_apply u y
  have h_det : LinearMap.det f = ‖u.det‖ ^ 2 := by
    simp [f, LinearMap.det_restrictScalars, Algebra.norm_complex_eq, ← Complex.sq_norm]
  have h_pos : 0 < ‖u.det‖ ^ 2 := pow_pos (norm_pos_iff.2 hu) 2
  rw [lintegral_congr fun y ↦ by rw [← hf],
    lintegral_comp_linearMap (volume : Measure (κ → ℂ)) (h_det.trans_ne h_pos.ne') g,
    h_det, abs_of_pos (inv_pos.2 h_pos), inv_pow]

/-- Change of variables on `ι → κ → ℂ` for the affine matrix substitution `A ↦ S * A + c` with
invertible `S : Matrix ι ι ℂ`. -/
theorem lintegral_comp_matrix_mul_add {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {S : Matrix ι ι ℂ} (hS : S.det ≠ 0) (c : Matrix ι κ ℂ) (g : (ι → κ → ℂ) → ENNReal) :
    ∫⁻ A : ι → κ → ℂ, g (of.symm (S * of A + c)) =
      ENNReal.ofReal (‖S.det‖⁻¹ ^ (2 * card κ)) * ∫⁻ A : ι → κ → ℂ, g A := by
  classical
  let e : (ι × κ → ℂ) ≃ₗ[ℂ] (ι → κ → ℂ) := LinearEquiv.curry ℂ ℂ ι κ
  let f : (ι → κ → ℂ) →ₗ[ℂ] (ι → κ → ℂ) :=
    e.toLinearMap ∘ₗ (kroneckerMap (· * ·) S (1 : Matrix κ κ ℂ)).toLin' ∘ₗ e.symm.toLinearMap
  have hf (A : ι → κ → ℂ) : f A = of.symm (S * of A) := by
    ext a b
    simp [f, e, mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]
  have h_det : LinearMap.det (f.restrictScalars ℝ) = ‖S.det‖ ^ (2 * card κ) := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_conj]
    simp [det_kronecker, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, ← pow_mul, mul_comm]
  have h_pos : 0 < ‖S.det‖ ^ (2 * card κ) := pow_pos (norm_pos_iff.2 hS) _
  have h_arg (A : ι → κ → ℂ) : of.symm (S * of A + c) = f.restrictScalars ℝ A + of.symm c := by
    ext i j
    simp [hf]
  -- Typeclass search does not chain `IsAddHaarMeasure` across nested `Pi` spaces `ι → κ → ℂ`.
  have : (volume : Measure (κ → ℂ)).IsAddHaarMeasure := ⟨⟩
  have : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := ⟨⟩
  rw [lintegral_congr fun A ↦ by rw [h_arg],
    lintegral_comp_linearMap (volume : Measure (ι → κ → ℂ)) (h_det.trans_ne h_pos.ne')
      (fun A ↦ g (A + of.symm c)),
    lintegral_add_right_eq_self, h_det, abs_of_pos (inv_pos.2 h_pos), inv_pow]

end MeasureTheory
