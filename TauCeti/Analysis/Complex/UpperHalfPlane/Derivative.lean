/-
Copyright (c) 2026 The Tau Ceti authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti authors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PSLAction
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints

/-!
# Derivatives of projective Möbius transformations

The derivative of a projective Möbius transformation `g : PSL(2, ℝ)` at a point of the upper
half-plane is the complex derivative of its action. On an `SL(2, ℝ)` representative it is the
reciprocal square of the Möbius denominator. The derivative is a multiplicative cocycle for the
action, and at a fixed point it has norm one. A projective transformation fixing a point whose
derivative there is one is the identity. Together these properties make the derivative at a point
a faithful character of its stabilizer with values on the unit circle.

## Main results

* `Matrix.SpecialLinearGroup.derivative_mk`: the derivative formula for an `SL(2, ℝ)`
  representative.
* `Matrix.ProjectiveSpecialLinearGroup.derivative_mul`: the derivative cocycle for the
  `PSL(2, ℝ)` action.
* `Matrix.ProjectiveSpecialLinearGroup.eq_one_of_smul_eq_self_of_derivative_eq_one`:
  faithfulness at a fixed point.

## References

* [S. Katok, *Fuchsian Groups*, Chapter 2][katok1992]
-/

public section

open scoped MatrixGroups
open Matrix.SpecialLinearGroup UpperHalfPlane

noncomputable section

namespace Matrix.ProjectiveSpecialLinearGroup

/-- The complex derivative at `τ` of the action of a projective special linear transformation,
extended to `ℂ` through `UpperHalfPlane.ofComplex`. -/
def derivative (g : PSL(2, ℝ)) (τ : ℍ) : ℂ :=
  deriv (fun z : ℂ ↦ ↑(g • ofComplex z)) τ

/-- The derivative of a projective transformation is the complex derivative of its action. -/
theorem derivative_def (g : PSL(2, ℝ)) (τ : ℍ) :
    derivative g τ = deriv (fun z : ℂ ↦ ↑(g • ofComplex z)) τ := (rfl)

end Matrix.ProjectiveSpecialLinearGroup

namespace Matrix.SpecialLinearGroup

/-- The derivative of an `SL(2, ℝ)` representative is the reciprocal square of its Möbius
denominator. In particular, it is unchanged when the representative is multiplied by `-1`. -/
@[simp]
theorem derivative_mk (g : SL(2, ℝ)) (τ : ℍ) :
    ProjectiveSpecialLinearGroup.derivative (↑g : PSL(2, ℝ)) τ = 1 / denom (mapGL ℝ g) τ ^ 2 := by
  have hfun : (fun z : ℂ ↦ (↑((↑g : PSL(2, ℝ)) • ofComplex z) : ℂ)) =
      fun z : ℂ ↦ (↑(g • ofComplex z) : ℂ) := by
    funext z
    rw [pslMk_smul]
  rw [ProjectiveSpecialLinearGroup.derivative_def, hfun]
  simp only [MulAction.compHom_smul_def]
  rw [UpperHalfPlane.deriv_smul (by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL]
    exact zero_lt_one)]
  rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL]
  simp

end Matrix.SpecialLinearGroup

namespace Matrix.ProjectiveSpecialLinearGroup

/-- The derivative of a projective Möbius transformation never vanishes on the upper
half-plane. -/
theorem derivative_ne_zero (g : PSL(2, ℝ)) (τ : ℍ) : derivative g τ ≠ 0 := by
  refine QuotientGroup.induction_on g fun a ↦ ?_
  rw [derivative_mk]
  exact div_ne_zero one_ne_zero (pow_ne_zero _ (denom_ne_zero _ τ))

/-- The derivative is a multiplicative cocycle for the projective action. -/
theorem derivative_mul (g h : PSL(2, ℝ)) (τ : ℍ) :
    derivative (g * h) τ = derivative g (h • τ) * derivative h τ := by
  refine QuotientGroup.induction_on g fun a ↦ ?_
  refine QuotientGroup.induction_on h fun b ↦ ?_
  simp only [← QuotientGroup.mk_mul, derivative_mk, pslMk_smul, map_mul]
  rw [denom_cocycle_σ]
  have hb : 0 < (mapGL ℝ b).det.val := by
    rw [det_mapGL]
    exact zero_lt_one
  simp only [σ, ite_eq_left hb, ContinuousAlgEquiv.refl_apply]
  field_simp
  simp only [MulAction.compHom_smul_def]

/-- The identity projective transformation has derivative one everywhere. -/
@[simp]
theorem derivative_one : derivative (1 : PSL(2, ℝ)) = 1 := by
  funext τ
  rw [← QuotientGroup.mk_one (N := Subgroup.center SL(2, ℝ)), derivative_mk]
  simp [denom]

/-- At a fixed point, the derivative has complex norm one. -/
theorem norm_derivative_eq_one_of_smul_eq_self {g : PSL(2, ℝ)} {τ : ℍ}
    (hfix : g • τ = τ) : ‖derivative g τ‖ = 1 := by
  revert hfix
  refine QuotientGroup.induction_on g fun a hfix ↦ ?_
  rw [derivative_mk, norm_div, norm_one, norm_pow]
  have hact : (↑a : PSL(2, ℝ)) • τ = (mapGL ℝ a) • τ := by
    rw [pslMk_smul, MulAction.compHom_smul_def]
  have him : ((mapGL ℝ a) • τ).im = τ.im := by
    rw [← hact]
    exact congrArg UpperHalfPlane.im hfix
  rw [τ.im_smul_eq_div_normSq] at him
  have hdet : |(mapGL ℝ a).det.val| = 1 := by
    rw [det_mapGL]
    simp
  rw [hdet, one_mul] at him
  have hsq : Complex.normSq (denom (mapGL ℝ a) τ) = 1 := by
    have hpos := τ.im_pos
    have hden := normSq_denom_pos (mapGL ℝ a) τ.im_ne_zero
    field_simp at him
    nlinarith
  rw [Complex.normSq_eq_norm_sq] at hsq
  have hnorm : ‖denom (mapGL ℝ a) τ‖ = 1 := by nlinarith [norm_nonneg (denom (mapGL ℝ a) τ)]
  rw [hnorm]
  simp

end Matrix.ProjectiveSpecialLinearGroup

namespace TauCeti

/-- A positive-determinant matrix fixing `τ` whose Möbius denominator at `τ` is the real number
`r` is the scalar matrix `r`. -/
private theorem val_eq_scalar_of_smul_eq_self_of_denom_eq {A : GL (Fin 2) ℝ} {τ : ℍ} {r : ℝ}
    (hA : 0 < A.det.val) (hfix : A • τ = τ) (hden : denom A τ = r) :
    A.val = Matrix.scalar (Fin 2) r := by
  have hc : A 1 0 = 0 := by
    simpa [denom, τ.im_ne_zero] using congrArg Complex.im hden
  have hdC : (A 1 1 : ℂ) = r := by simpa [denom, hc] using hden
  have hd : A 1 1 = r := by exact_mod_cast hdC
  have hnum := gl_smul_eq_iff_num_eq.mp hfix
  simp only [σ, ite_eq_left hA] at hnum
  have ha : A 0 0 = r := by
    have hi : A 0 0 * τ.im = τ.im * r := by
      simpa [num, denom, hc, hd] using congrArg Complex.im hnum
    exact mul_right_cancel₀ τ.im_ne_zero (hi.trans (mul_comm _ _))
  have hb : A 0 1 = 0 := by
    have hr : r * τ.re + A 0 1 = τ.re * r := by
      simpa [num, denom, hc, hd, ha] using congrArg Complex.re hnum
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, ha, hb, hc, hd]

end TauCeti

namespace Matrix.SpecialLinearGroup

private theorem mem_center_of_smul_eq_self_of_derivative_eq_one (a : SL(2, ℝ)) (τ : ℍ)
    (hfix : a • τ = τ) (hderiv : 1 / denom (mapGL ℝ a) τ ^ 2 = 1) :
    a ∈ Subgroup.center SL(2, ℝ) := by
  have hApos : 0 < (mapGL ℝ a).det.val := by
    rw [det_mapGL]
    exact zero_lt_one
  have hAfix : mapGL ℝ a • τ = τ := by
    simpa only [MulAction.compHom_smul_def] using hfix
  have hsq : denom (mapGL ℝ a) τ ^ 2 = 1 := by
    field_simp at hderiv
    exact hderiv.symm
  have hAeq : (mapGL ℝ a).val = (toGL a).val := by
    ext i j
    simp [mapGL_coe_matrix, Algebra.algebraMap_self]
  apply (toGL_mem_center_iff a).mp
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, ← hAeq]
  rcases sq_eq_one_iff.mp hsq with hden | hden
  · exact ⟨1, (TauCeti.val_eq_scalar_of_smul_eq_self_of_denom_eq hApos hAfix
      (by simpa using hden)).symm⟩
  · exact ⟨-1, (TauCeti.val_eq_scalar_of_smul_eq_self_of_denom_eq hApos hAfix
      (by simpa using hden)).symm⟩

end Matrix.SpecialLinearGroup

namespace Matrix.ProjectiveSpecialLinearGroup

/-- A projective transformation fixing a point is determined by its derivative there. -/
theorem eq_one_of_smul_eq_self_of_derivative_eq_one {g : PSL(2, ℝ)} {τ : ℍ}
    (hfix : g • τ = τ) (hderiv : derivative g τ = 1) : g = 1 := by
  revert hfix hderiv
  refine QuotientGroup.induction_on g fun a hfix hderiv ↦ ?_
  rw [derivative_mk] at hderiv
  rw [QuotientGroup.eq_one_iff]
  apply mem_center_of_smul_eq_self_of_derivative_eq_one a τ
  · simpa only [pslMk_smul] using hfix
  · exact hderiv

end Matrix.ProjectiveSpecialLinearGroup
