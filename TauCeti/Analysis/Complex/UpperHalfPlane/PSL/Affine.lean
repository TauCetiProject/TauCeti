/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.SmulDeriv
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation

/-!
# Affine maps of the upper half-plane: dilations and moving `I` to a given point

The dilation `Matrix.SpecialLinearGroup.dilation s` acts on `ℍ` as `z ↦ exp s * z`
(`TauCeti.UpperHalfPlane.coe_dilation_smul`). For `P : ℍ`, the affine map
`UpperHalfPlane.toPoint P : z ↦ P.im * z + P.re` is the element of `PSL(2, ℝ)` given by a dilation
followed by a real translation; it sends `I` to `P` (`UpperHalfPlane.toPoint_smul_I`). This file
records its action, the action of its inverse, and its derivative.

Conversely, every element of `PSL(2, ℝ)` fixing the ideal point `∞` acts on `ℍ` as an affine map
`z ↦ μ * z + c` with `μ > 0` (`TauCeti.UpperHalfPlane.exists_coe_smul_eq_mul_add_of_smul_infty`).
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup TauCeti.UpperHalfPlane UpperHalfPlane
open scoped MatrixGroups OnePoint

open Matrix.SpecialLinearGroup (dilation)

namespace TauCeti.UpperHalfPlane

/-- `dilation s` acts on `ℍ` as `z ↦ exp s * z`. -/
theorem coe_dilation_smul (s : ℝ) (z : ℍ) : ((dilation s • z : ℍ) : ℂ) = Real.exp s * z := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Matrix.SpecialLinearGroup.coe_dilation, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Algebra.algebraMap_self_apply, Complex.ofReal_zero, zero_mul, add_zero, zero_add]
  have h2 : (Real.exp s : ℂ) = Real.exp (s / 2) * Real.exp (s / 2) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_halves]
  have hne : (Real.exp (-(s / 2)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  rw [div_eq_iff hne, h2, Real.exp_neg]
  push_cast
  field_simp

/-- **Elements fixing `∞` are affine.** An element of `PSL(2, ℝ)` fixing the ideal point `∞` acts
on `ℍ` as `z ↦ μ * z + c` for some real `μ > 0` and `c`: the class of `!![a, b; 0, a⁻¹]` acts by
`μ = a ^ 2` and `c = a * b`. -/
theorem exists_coe_smul_eq_mul_add_of_smul_infty {g : PSL(2, ℝ)}
    (hg : g • (∞ : OnePoint ℝ) = ∞) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ c : ℝ, ∀ z : ℍ, ((g • z : ℍ) : ℂ) = μ * z + c := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [mk_smul_infty_eq_infty_iff] at hg
  have hdet : A 0 0 * A 1 1 = 1 := by
    have := A.det_coe
    rw [Matrix.det_fin_two, hg] at this
    simpa using this
  have h00 : A 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨A 0 0 ^ 2, by positivity, A 0 0 * A 0 1, fun z ↦ ?_⟩
  have h11 : (A 1 1 : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul_eq_one hdet
  have hdetC : (A 0 0 : ℂ) * A 1 1 = 1 := by exact_mod_cast hdet
  rw [UpperHalfPlane.pslMk_smul, UpperHalfPlane.coe_specialLinearGroup_apply, hg]
  simp only [Algebra.algebraMap_self_apply, Complex.ofReal_zero, zero_mul, zero_add]
  rw [div_eq_iff h11]
  push_cast
  linear_combination -(A 0 0 * (z : ℂ) + A 0 1) * hdetC

end TauCeti.UpperHalfPlane

namespace UpperHalfPlane

/-- The affine map `z ↦ P.im * z + P.re`, an element of `PSL(2, ℝ)` sending `I` to `P`. -/
def toPoint (P : ℍ) : PSL(2, ℝ) := upperRightHom P.re * ↑(dilation (Real.log P.im))

/-- `toPoint P` acts on `ℍ` as `z ↦ P.im * z + P.re`. -/
theorem coe_toPoint_smul (P z : ℍ) : ((toPoint P • z : ℍ) : ℂ) = P.im * z + P.re := by
  rw [toPoint, mul_smul, UpperHalfPlane.pslMk_smul, upperRightHom_smul, UpperHalfPlane.coe_vadd,
    coe_dilation_smul, Real.exp_log P.im_pos, add_comm]

/-- `toPoint P` sends `I` to `P`. -/
@[simp]
theorem toPoint_smul_I (P : ℍ) : toPoint P • UpperHalfPlane.I = P := by
  apply UpperHalfPlane.coe_injective
  rw [coe_toPoint_smul, UpperHalfPlane.coe_I]
  apply Complex.ext <;> simp

/-- The inverse of `toPoint P` acts on `ℍ` as `z ↦ (z - P.re) / P.im`. -/
theorem coe_toPoint_inv_smul (P z : ℍ) :
    (((toPoint P)⁻¹ • z : ℍ) : ℂ) = ((z : ℂ) - P.re) / P.im := by
  have h := coe_toPoint_smul P ((toPoint P)⁻¹ • z)
  rw [smul_inv_smul] at h
  rw [eq_div_iff (by exact_mod_cast P.im_pos.ne')]
  linear_combination -h

/-- The derivative of the affine map `toPoint P` is `P.im`. -/
theorem smulDeriv_toPoint (P z : ℍ) : smulDeriv (toPoint P) z = P.im := by
  rw [toPoint, smulDeriv_mul, smulDeriv_upperRightHom, smulDeriv_dilation, Real.exp_log P.im_pos,
    one_mul]

/-- The real part of the normalised point `(toPoint P)⁻¹ • z`. -/
theorem re_toPoint_inv_smul (P z : ℍ) : ((toPoint P)⁻¹ • z : ℍ).re = (z.re - P.re) / P.im := by
  rw [← UpperHalfPlane.coe_re, coe_toPoint_inv_smul, div_eq_mul_inv, ← Complex.ofReal_inv,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re,
    Complex.ofReal_re, UpperHalfPlane.coe_re, div_eq_mul_inv]

/-- The norm-square of the normalised point `(toPoint P)⁻¹ • z`. -/
theorem normSq_toPoint_inv_smul (P z : ℍ) :
    Complex.normSq (((toPoint P)⁻¹ • z : ℍ) : ℂ) = Complex.normSq ((z : ℂ) - P.re) / P.im ^ 2 := by
  rw [coe_toPoint_inv_smul, map_div₀, Complex.normSq_ofReal, sq]

end UpperHalfPlane
