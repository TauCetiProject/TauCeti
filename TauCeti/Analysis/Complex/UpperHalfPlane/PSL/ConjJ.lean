/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Dilation
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Conjugation by `J` on `PSL(2, ℝ)`

Mathlib's `UpperHalfPlane.J : GL (Fin 2) ℝ` acts on `ℍ` by the orientation-reversing involution
`z ↦ -conj z`, and on the ideal boundary `∂ℍ = ℝ ∪ {∞}` by `x ↦ -x`. Conjugation by `J` is the
automorphism `pslConjJ` of `PSL(2, ℝ)`, sending the class of `!![a, b; c, d]` to that of
`!![a, -b; -c, d]`, and `J` intertwines the action of each `g` with that of `pslConjJ g`.

## Main declarations

* `TauCeti.UpperHalfPlane.pslConjJ`: conjugation by `J` on `PSL(2, ℝ)`, computed on matrices by
  `pslConjJ_mk`; it is an involution (`pslConjJ_pslConjJ`, `pslConjJ_symm`).
* `TauCeti.UpperHalfPlane.J_smul_smul` and `TauCeti.UpperHalfPlane.J_smul_smul_onePoint`: `J`
  intertwines `g` with `pslConjJ g` on `ℍ` and on `∂ℍ`.
* `TauCeti.UpperHalfPlane.pslConjJ_pslS` and `TauCeti.UpperHalfPlane.pslConjJ_dilation`:
  conjugation by `J` fixes `pslS` and the dilations; it inverts the translations
  (`TauCeti.UpperHalfPlane.pslConjJ_upperRightHom`).
* `TauCeti.UpperHalfPlane.J_smul_coe`, `TauCeti.UpperHalfPlane.J_smul_infty`: `J` negates real
  ideal points and fixes `∞`.
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups OnePoint

namespace TauCeti.UpperHalfPlane

/-- Conjugation by the orientation-reversing involution `UpperHalfPlane.J : z ↦ -conj z` on
`PSL(2, ℝ)`: the class of `!![a, b; c, d]` goes to the class of `!![a, -b; -c, d]`
(`pslConjJ_mk`). It is characterised by `J_smul_smul` and `J_smul_smul_onePoint`. -/
def pslConjJ : PSL(2, ℝ) ≃* PSL(2, ℝ) :=
  QuotientGroup.congr _ _ Matrix.SpecialLinearGroup.conjJMulAut
    (Subgroup.characteristic_iff_map_eq.1 inferInstance _)

/-- Conjugation by `J` sends the class of `!![a, b; c, d]` to the class of `!![a, -b; -c, d]`. -/
theorem pslConjJ_mk (A : SL(2, ℝ)) :
    pslConjJ (A : PSL(2, ℝ)) = (Matrix.SpecialLinearGroup.conjJ A : PSL(2, ℝ)) := by
  rw [pslConjJ]
  exact (QuotientGroup.congr_mk (x := A) ..).trans
    (congrArg _ (Matrix.SpecialLinearGroup.conjJMulAut_apply A))

/-- Conjugation by `J` is an involution. -/
@[simp]
theorem pslConjJ_pslConjJ (g : PSL(2, ℝ)) : pslConjJ (pslConjJ g) = g := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [pslConjJ_mk, pslConjJ_mk, Matrix.SpecialLinearGroup.conjJ_conjJ]

/-- Conjugation by `J` is its own inverse. -/
@[simp]
theorem pslConjJ_symm : pslConjJ.symm = pslConjJ :=
  MulEquiv.ext fun g ↦ pslConjJ.symm_apply_eq.2 (pslConjJ_pslConjJ g).symm

/-- `J` intertwines the action of `g` on `ℍ` with that of its conjugate `pslConjJ g`. -/
theorem J_smul_smul (g : PSL(2, ℝ)) (z : ℍ) : J • g • z = pslConjJ g • J • z := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [pslConjJ_mk, pslMk_smul, pslMk_smul, MulAction.compHom_smul_def,
    MulAction.compHom_smul_def, smul_smul, smul_smul, Matrix.SpecialLinearGroup.J_mul_mapGL]

/-- `J` intertwines the action of `g` on the ideal boundary with that of `pslConjJ g`. -/
theorem J_smul_smul_onePoint (g : PSL(2, ℝ)) (ξ : OnePoint ℝ) :
    J • g • ξ = pslConjJ g • J • ξ := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [pslConjJ_mk, OnePoint.pslMk_smul, OnePoint.pslMk_smul, smul_smul, smul_smul]
  congr 1
  exact Matrix.SpecialLinearGroup.J_mul_mapGL A

/-- Conjugation by `J` fixes the involution `pslS : z ↦ -1/z`. -/
@[simp]
theorem pslConjJ_pslS : pslConjJ pslS = pslS := by
  rw [pslS_def, psl2zToPSL2R_mk, sl2zToPSL2R_apply, pslConjJ_mk,
    ← Matrix.ProjectiveSpecialLinearGroup.mk_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_S]

/-- Conjugation by `J` fixes the dilations `z ↦ exp s * z`. -/
@[simp]
theorem pslConjJ_dilation (s : ℝ) :
    pslConjJ (Matrix.SpecialLinearGroup.dilation s : PSL(2, ℝ)) =
      (Matrix.SpecialLinearGroup.dilation s : PSL(2, ℝ)) := by
  rw [pslConjJ_mk]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_dilation]

/-- Conjugation by `J` inverts the translations `z ↦ z + x`. -/
@[simp]
theorem pslConjJ_upperRightHom (x : ℝ) :
    pslConjJ (Matrix.ProjectiveSpecialLinearGroup.upperRightHom x) =
      Matrix.ProjectiveSpecialLinearGroup.upperRightHom (-x) := by
  rw [Matrix.ProjectiveSpecialLinearGroup.upperRightHom_apply,
    Matrix.ProjectiveSpecialLinearGroup.upperRightHom_apply, pslConjJ_mk]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe]

/-- `J` negates real ideal points. -/
@[simp]
theorem J_smul_coe (x : ℝ) : J • (x : OnePoint ℝ) = ((-x : ℝ) : OnePoint ℝ) := by
  simp [OnePoint.smul_some_eq_ite, J]

/-- `J` fixes the ideal point `∞`. -/
@[simp]
theorem J_smul_infty : J • (∞ : OnePoint ℝ) = ∞ := by
  simp [OnePoint.smul_infty_eq_ite, J]

/-- `J` is an involution of the ideal boundary. -/
@[simp]
theorem J_smul_J_smul_onePoint (ξ : OnePoint ℝ) : J • J • ξ = ξ := by
  rw [smul_smul, ← sq, J_sq, one_smul]

end TauCeti.UpperHalfPlane
