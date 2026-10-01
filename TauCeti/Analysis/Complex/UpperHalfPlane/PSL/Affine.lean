/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Dilation
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic

/-!
# Moving `I` to a given point of the upper half-plane

For `P : ℍ`, the affine map `UpperHalfPlane.toPoint P : z ↦ P.im * z + P.re` is the element of
`PSL(2, ℝ)` given by a dilation followed by a real translation; it sends `I` to `P`
(`UpperHalfPlane.toPoint_smul_I`). This file records its action, the action of its inverse, and
its derivative.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup TauCeti.UpperHalfPlane
open scoped MatrixGroups

namespace UpperHalfPlane

open Matrix.SpecialLinearGroup (dilation)

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
