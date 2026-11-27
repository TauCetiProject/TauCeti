/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.MeasureTheory.Measure.Lebesgue.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Change of variables for complex matrix actions on Lebesgue measure

Derives lower Lebesgue integral change-of-variables formulas for invertible complex matrices acting
on `κ → ℂ` by `mulVec` and on `ι → κ → ℂ` by two-sided and by affine left matrix multiplication from
`MeasureTheory.lintegral_comp_linearMap`. No measurability assumption on the integrand is needed.

## Main results

* `MeasureTheory.lintegral_comp_mulVec`: for an invertible complex matrix `u`,
  `∫⁻ y : κ → ℂ, g (u *ᵥ y) = ENNReal.ofReal (‖u.det‖⁻¹ ^ 2) * ∫⁻ y : κ → ℂ, g y`.
* `MeasureTheory.lintegral_comp_matrix_mul_add`: for an invertible complex matrix `S` and offset
  `c : Matrix ι κ ℂ`,
  `∫⁻ A : ι → κ → ℂ, g (of.symm (S * of A + c)) =`
  `ENNReal.ofReal (‖S.det‖⁻¹ ^ (2 * Fintype.card κ)) * ∫⁻ A : ι → κ → ℂ, g A`.
* `MeasureTheory.lintegral_comp_matrix_mul_mul`: for invertible complex matrices `P` and `Q`,
  the substitution `A ↦ P * A * Q` has the real Jacobian
  `‖P.det‖ ^ (2 * Fintype.card κ) * ‖Q.det‖ ^ (2 * Fintype.card ι)`.
* `MeasureTheory.lintegral_eq_enorm_det_pow_mul_enorm_det_pow_mul_lintegral_comp_matrix_mul_mul`:
  the same substitution `Y ↦ P * Y * Q` on `Matrix ι κ ℂ` with its product Lebesgue measure, in
  the form `∫⁻ Y, g Y = ‖P.det‖ₑ ^ (2 |κ|) * ‖Q.det‖ₑ ^ (2 |ι|) * ∫⁻ Y, g (P * Y * Q)`.

## Provenance

The two-sided multiplication formula is adapted from `New.lintegral_eq_det_mul_comp_mul_mul` in
`src/Lib/DiscreteSeries/Haar/GramCoordinates.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). There the
integrand is assumed measurable; here it is arbitrary, and the determinant comes from the
Kronecker product on arrays of entries.
-/

public section

open Fintype Matrix

namespace MeasureTheory

/-- The product Lebesgue measure on `ι → κ → ℂ` is an additive Haar measure. Typeclass search
does not chain `Measure.pi.isAddHaarMeasure` across the nested `Pi` type on its own. -/
instance isAddHaarMeasure_volume_pi_pi_complex {ι κ : Type*} [Fintype ι] [Fintype κ] :
    (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

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

/-- **Change of variables for two-sided multiplication** on `ι → κ → ℂ`: for invertible complex
matrices `P` and `Q`, the substitution `A ↦ P * A * Q` has the real Jacobian
`|det P| ^ (2 |κ|) * |det Q| ^ (2 |ι|)`. -/
theorem lintegral_comp_matrix_mul_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {P : Matrix ι ι ℂ} {Q : Matrix κ κ ℂ} (hP : P.det ≠ 0)
    (hQ : Q.det ≠ 0) (g : (ι → κ → ℂ) → ENNReal) :
    ∫⁻ A : ι → κ → ℂ, g (of.symm (P * of A * Q)) =
      ENNReal.ofReal ((‖P.det‖ ^ (2 * card κ) * ‖Q.det‖ ^ (2 * card ι))⁻¹) *
        ∫⁻ A : ι → κ → ℂ, g A := by
  let e : (ι × κ → ℂ) ≃ₗ[ℂ] (ι → κ → ℂ) := LinearEquiv.curry ℂ ℂ ι κ
  let f : (ι → κ → ℂ) →ₗ[ℂ] (ι → κ → ℂ) :=
    e.toLinearMap ∘ₗ (Matrix.kroneckerMap (· * ·) P Qᵀ).toLin' ∘ₗ e.symm.toLinearMap
  have hf (A : ι → κ → ℂ) : f A = of.symm (P * of A * Q) := by
    ext a b
    simp only [f, e, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.coe_curry_symm, Matrix.toLin'_apply, LinearEquiv.coe_curry,
      Function.curry_apply, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, Fintype.sum_prod_type, Function.uncurry_apply_pair, Matrix.symm_of,
      Matrix.coe_rowEquiv, Matrix.row_apply, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have h_det : LinearMap.det (f.restrictScalars ℝ) =
      ‖P.det‖ ^ (2 * card κ) * ‖Q.det‖ ^ (2 * card ι) := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_conj, LinearMap.det_toLin', det_kronecker,
      det_transpose, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_mul, norm_pow,
      norm_pow]
    ring
  have h_pos : 0 < ‖P.det‖ ^ (2 * card κ) * ‖Q.det‖ ^ (2 * card ι) := by
    have := norm_pos_iff.2 hP
    have := norm_pos_iff.2 hQ
    positivity
  rw [lintegral_congr fun A ↦ by rw [← hf]]
  refine (lintegral_comp_linearMap (volume : Measure (ι → κ → ℂ))
    (h_det.trans_ne h_pos.ne') g).trans ?_
  rw [h_det, abs_of_pos (inv_pos.2 h_pos)]

/-- Change of variables on `ι → κ → ℂ` for the affine matrix substitution `A ↦ S * A + c` with
invertible `S : Matrix ι ι ℂ`. -/
theorem lintegral_comp_matrix_mul_add {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {S : Matrix ι ι ℂ} (hS : S.det ≠ 0) (c : Matrix ι κ ℂ) (g : (ι → κ → ℂ) → ENNReal) :
    ∫⁻ A : ι → κ → ℂ, g (of.symm (S * of A + c)) =
      ENNReal.ofReal (‖S.det‖⁻¹ ^ (2 * card κ)) * ∫⁻ A : ι → κ → ℂ, g A := by
  classical
  -- The case `Q = 1` of `lintegral_comp_matrix_mul_mul`, followed by a translation.
  have h := lintegral_comp_matrix_mul_mul hS (by simp : (1 : Matrix κ κ ℂ).det ≠ 0)
    fun A ↦ g (A + of.symm c)
  simp only [Matrix.mul_one, det_one, norm_one, one_pow, mul_one,
    lintegral_add_right_eq_self] at h
  have h_arg (A : ι → κ → ℂ) : of.symm (S * of A + c) = of.symm (S * of A) + of.symm c := by
    ext i j
    simp only [of_symm_apply, Matrix.add_apply, Pi.add_apply]
  simp only [h_arg, h, inv_pow]

/-- **Change of variables for two-sided multiplication** on `Matrix ι κ ℂ` with its product
Lebesgue measure: for invertible `P` and `Q`,
`∫⁻ Y, g Y = |det P| ^ (2 |κ|) * |det Q| ^ (2 |ι|) * ∫⁻ Y, g (P * Y * Q)`. -/
theorem lintegral_eq_enorm_det_pow_mul_enorm_det_pow_mul_lintegral_comp_matrix_mul_mul
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {P : Matrix ι ι ℂ} {Q : Matrix κ κ ℂ} (hP : P.det ≠ 0) (hQ : Q.det ≠ 0)
    (g : Matrix ι κ ℂ → ENNReal) :
    ∫⁻ Y : Matrix ι κ ℂ, g Y =
      ‖P.det‖ₑ ^ (2 * card κ) * ‖Q.det‖ₑ ^ (2 * card ι) *
        ∫⁻ Y : Matrix ι κ ℂ, g (P * Y * Q) := by
  have hmp := Matrix.volume_preserving_ofMeasurableEquiv ι κ ℂ
  rw [← hmp.lintegral_comp_emb (Matrix.ofMeasurableEquiv ι κ ℂ).measurableEmbedding,
    ← hmp.lintegral_comp_emb (Matrix.ofMeasurableEquiv ι κ ℂ).measurableEmbedding]
  have h := lintegral_comp_matrix_mul_mul hP hQ (fun A ↦ g (Matrix.of A))
  simp only [Matrix.ofMeasurableEquiv_apply, Equiv.apply_symm_apply] at h ⊢
  -- The Jacobian factor cancels against the inverse factor of `lintegral_comp_matrix_mul_mul`.
  have hP' := norm_pos_iff.2 hP
  have hQ' := norm_pos_iff.2 hQ
  rw [h, ← mul_assoc, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow hP'.le, ENNReal.ofReal_pow hQ'.le, ofReal_norm, ofReal_norm,
    ENNReal.mul_inv_cancel (by simp [hP, hQ]) (ENNReal.mul_ne_top (by simp) (by simp)), one_mul]

end MeasureTheory
