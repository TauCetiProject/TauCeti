/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Datum
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import Mathlib.Analysis.Complex.Periodic

/-!
# Changing the scaling of a cusp

Two normalized data at the same cusp have the same positive primitive generator. Their scalings
are related by `σ' = aσ + b`, with `a > 0`, and their widths satisfy `w' = aw`.
Consequently their exponential coordinates differ by the constant
`exp (2πib / (aw))`, of modulus one. This is the coordinate transition needed to compare cusp
charts, including at the added point where the exponential coordinate vanishes.

The statements use `Function.Periodic.qParam` directly, so they apply before choosing a complex
structure on the cusp quotient. No discreteness hypothesis is needed once normalized cusp data
have been supplied. The affine normal form reuses Mathlib's
`UpperHalfPlane.exists_SL2_smul_eq_of_apply_zero_one_eq_zero`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Springer, 2005, §2.4.
-/

public section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane OnePoint
open scoped MatrixGroups

namespace TauCeti

variable {Γ : Subgroup PSL(2, ℝ)} {D D' : Γ.CuspDatum}

/-- The positive primitive generator depends only on the cusp, not on its scaling. -/
theorem cuspDatum_generator_eq (hc : D.cusp = D'.cusp) : D.generator = D'.generator := by
  let g := D'.scaling * D.scaling⁻¹
  have hg : g • (∞ : OnePoint ℝ) = ∞ := by
    dsimp only [g]
    rw [mul_smul, inv_smul_eq_iff.mpr D.scaling_smul_cusp.symm, hc,
      D'.scaling_smul_cusp]
  obtain ⟨t, ht, hconj⟩ := exists_conj_upperRightHom_of_smul_infty hg
  let E : Γ.CuspDatum :=
    { D with
      scaling := D'.scaling
      width := t ^ 2 * D.width
      width_pos := mul_pos (sq_pos_of_ne_zero ht) D.width_pos
      scaling_mul_generator_mul_inv := by
        rw [← hconj, ← D.scaling_mul_generator_mul_inv]
        dsimp only [g]
        group }
  have hE : E = D' := Subgroup.CuspDatum.ext hc rfl
  simpa only [E] using congrArg (fun F : Γ.CuspDatum ↦ F.generator) hE

/-- Any two scalings at the same cusp differ by a positive real affine transformation. -/
theorem cuspDatum_exists_scaling_eq_affine (hc : D.cusp = D'.cusp) :
    ∃ a b : ℝ, 0 < a ∧ ∀ z : ℍ,
      (↑(D'.scaling • z) : ℂ) = a * (↑(D.scaling • z) : ℂ) + b := by
  have hg : (D'.scaling * D.scaling⁻¹) • (∞ : OnePoint ℝ) = ∞ := by
    rw [mul_smul, inv_smul_eq_iff.mpr D.scaling_smul_cusp.symm, hc,
      D'.scaling_smul_cusp]
  obtain ⟨g, hgeq⟩ := QuotientGroup.mk_surjective (D'.scaling * D.scaling⁻¹)
  rw [← hgeq, OnePoint.pslMk_smul, OnePoint.smul_infty_eq_self_iff,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hg
  obtain ⟨a, b, hab⟩ := exists_SL2_smul_eq_of_apply_zero_one_eq_zero g hg
  refine ⟨a, b, a.property, fun z ↦ ?_⟩
  have heq : g • (D.scaling • z) = D'.scaling • z := by
    rw [← UpperHalfPlane.pslMk_smul, hgeq, mul_smul, inv_smul_smul]
  rw [← heq, congrFun hab]
  simp only [Function.comp_apply, coe_vadd, coe_pos_real_smul, Complex.real_smul]
  ring

/-- Under `σ' = aσ + b`, the cusp width changes from `w` to `aw`. -/
theorem cuspDatum_width_eq_mul (hc : D.cusp = D'.cusp) {a b : ℝ}
    (hσ : ∀ z : ℍ, (↑(D'.scaling • z) : ℂ) = a * (↑(D.scaling • z) : ℂ) + b) :
    D'.width = a * D.width := by
  have htranslate (E : Γ.CuspDatum) (z : ℍ) :
      (↑(E.scaling • (E.generator : PSL(2, ℝ)) • z) : ℂ) =
        (↑(E.scaling • z) : ℂ) + E.width := by
    have heq : E.scaling • (E.generator : PSL(2, ℝ)) • z =
        upperRightHom E.width • (E.scaling • z) := by
      rw [← E.scaling_mul_generator_mul_inv, mul_smul, mul_smul, inv_smul_smul]
    rw [heq, upperRightHom_apply, UpperHalfPlane.pslMk_smul, coe_specialLinearGroup_apply]
    simp [Matrix.SpecialLinearGroup.transvection_coe]
  have h := hσ ((D.generator : PSL(2, ℝ)) • UpperHalfPlane.I)
  rw [htranslate D, cuspDatum_generator_eq hc, htranslate D', hσ] at h
  have hw : (D'.width : ℂ) = (a : ℂ) * D.width := by linear_combination h
  exact_mod_cast hw

/-- The exact change-of-scaling formula for the exponential cusp coordinate. -/
theorem cuspDatum_qParam_eq (hc : D.cusp = D'.cusp) {a b : ℝ}
    (hσ : ∀ z : ℍ, (↑(D'.scaling • z) : ℂ) = a * (↑(D.scaling • z) : ℂ) + b)
    (z : ℍ) :
    Function.Periodic.qParam D'.width (↑(D'.scaling • z) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * b / (a * D.width)) *
        Function.Periodic.qParam D.width (↑(D.scaling • z) : ℂ) := by
  have hw := cuspDatum_width_eq_mul hc hσ
  have ha : a ≠ 0 := by
    intro h
    have := D'.width_pos
    rw [hw, h, zero_mul] at this
    exact lt_irrefl _ this
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hw' : (D.width : ℂ) ≠ 0 := by exact_mod_cast D.width_pos.ne'
  simp only [Function.Periodic.qParam, hσ, hw, Complex.ofReal_mul]
  rw [← Complex.exp_add]
  congr 1
  field_simp
  ring

/-- The modulus of the exponential cusp coordinate is independent of the normalized scaling. -/
theorem cuspDatum_norm_qParam_eq (hc : D.cusp = D'.cusp) (z : ℍ) :
    ‖Function.Periodic.qParam D'.width (↑(D'.scaling • z) : ℂ)‖ =
      ‖Function.Periodic.qParam D.width (↑(D.scaling • z) : ℂ)‖ := by
  obtain ⟨a, b, -, hσ⟩ := cuspDatum_exists_scaling_eq_affine hc
  rw [cuspDatum_qParam_eq hc hσ, norm_mul, Complex.norm_exp]
  simp [Complex.div_re, Complex.mul_re, Complex.mul_im]

end TauCeti
