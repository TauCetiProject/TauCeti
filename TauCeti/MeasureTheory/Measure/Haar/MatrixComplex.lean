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
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Change of variables for complex matrix actions on Lebesgue measure

Provides lower Lebesgue integral change-of-variables formulas for invertible complex matrices
acting on `κ → ℂ` by `mulVec` and on `ι → κ → ℂ` by left matrix multiplication plus translation.
Both use `MeasurableEmbedding.lintegral_map`, so no measurability assumption on the integrand is
needed.

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
  have h_inj : Function.Injective f := fun x y hxy ↦
    mulVec_injective_of_det_ne_zero hu (by simpa only [hf] using hxy)
  have h_emb : MeasurableEmbedding f :=
    Continuous.measurableEmbedding f.continuous_of_finiteDimensional h_inj
  calc
    ∫⁻ y : κ → ℂ, g (u *ᵥ y) = ∫⁻ y : κ → ℂ, g (f y) := lintegral_congr fun y ↦ by rw [hf]
    _ = ∫⁻ y : κ → ℂ, g y ∂(Measure.map f volume) := (h_emb.lintegral_map g).symm
    _ = ENNReal.ofReal (‖u.det‖⁻¹ ^ 2) * ∫⁻ y : κ → ℂ, g y := by
      rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (κ → ℂ))
          (h_det.trans_ne h_pos.ne'),
        lintegral_smul_measure, h_det, abs_of_pos (inv_pos.2 h_pos), inv_pow, smul_eq_mul]

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
  have h_inj : Function.Injective (f.restrictScalars ℝ) := fun A B hAB ↦ by
    have hmul : S * of A = S * of B := by
      simpa only [LinearMap.coe_restrictScalars, hf, Equiv.apply_symm_apply] using congrArg of hAB
    have h_inv : S⁻¹ * (S * of A) = S⁻¹ * (S * of B) := congrArg (S⁻¹ * ·) hmul
    simpa only [← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hS),
      Matrix.one_mul, Equiv.symm_apply_apply] using congrArg of.symm h_inv
  have h_emb : MeasurableEmbedding (f.restrictScalars ℝ) :=
    Continuous.measurableEmbedding (f.restrictScalars ℝ).continuous_of_finiteDimensional h_inj
  have h_arg (A : ι → κ → ℂ) : of.symm (S * of A + c) = f.restrictScalars ℝ A + of.symm c := by
    ext i j
    simp [hf]
  calc
    ∫⁻ A : ι → κ → ℂ, g (of.symm (S * of A + c))
      = ∫⁻ A : ι → κ → ℂ, g (f.restrictScalars ℝ A + of.symm c) :=
        lintegral_congr fun A ↦ by rw [h_arg]
    _ = ∫⁻ A : ι → κ → ℂ, g (A + of.symm c) ∂(Measure.map (f.restrictScalars ℝ) volume) :=
        (h_emb.lintegral_map (fun A ↦ g (A + of.symm c))).symm
    _ = ENNReal.ofReal (‖S.det‖⁻¹ ^ (2 * card κ)) * ∫⁻ A : ι → κ → ℂ, g A := by
      -- Typeclass search does not chain `IsAddHaarMeasure` across nested `Pi` spaces `ι → κ → ℂ`.
      have : (volume : Measure (κ → ℂ)).IsAddHaarMeasure := ⟨⟩
      have : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := ⟨⟩
      rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → κ → ℂ))
          (h_det.trans_ne h_pos.ne'),
        lintegral_smul_measure, lintegral_add_right_eq_self, h_det,
        abs_of_pos (inv_pos.2 h_pos), inv_pow, smul_eq_mul]

end MeasureTheory
