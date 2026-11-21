/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Block.Toeplitz
public import TauCeti.Analysis.Fourier.Hardy.Block.FiniteSection
public import TauCeti.Analysis.Fourier.Hardy.Index
public import TauCeti.Analysis.Fourier.Winding
import TauCeti.Analysis.Fredholm.Prod
import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Opposite shifts: zero determinant winding does not imply block Toeplitz invertibility

The symbol `diag(z, conj z)` on the circle has determinant one. Its block Toeplitz operator is
`S ⊕ S†`, Fredholm of index zero, but it kills the constant vector in its second component.
Every pure finite section is singular for the same reason.

This is the standard block-symbol obstruction to extending scalar Toeplitz invertibility
criteria to matrix symbols using only determinant winding. The scalar shift, backward shift
and Fredholm indices identify this operator with the direct sum of opposite scalar shifts.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*.

## Provenance

Mechanically extracted from the Kitware DKPS formalization's
`ForTauCeti/Analysis/Fourier/Hardy/OppositeShifts.lean` at
[d1c0bf02e](https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/d1c0bf02e/ForTauCeti/Analysis/Fourier/Hardy/OppositeShifts.lean),
with subsequent refinements to use matrix-symbol conversion and operator compression.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti
namespace ToeplitzOppositeShifts

/-- The continuous matrix symbol `diag(z, conj z)` in period-one Fourier coordinates. -/
def matrixSymbol : C(UnitAddCircle, Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨fun t => Matrix.diagonal ![fourier 1 t, fourier (-1) t], by fun_prop⟩

/-- Evaluation of the continuous diagonal symbol. -/
theorem matrixSymbol_apply (t : UnitAddCircle) :
    matrixSymbol t = Matrix.diagonal ![fourier 1 t, fourier (-1) t] := (rfl)

/-- The determinant of the opposite-shift symbol is identically one. -/
@[simp] theorem det_matrixSymbol (t : UnitAddCircle) : (matrixSymbol t).det = 1 := by
  rw [matrixSymbol_apply, Matrix.det_diagonal, Fin.prod_univ_two]
  change fourier 1 t * fourier (-1) t = 1
  rw [← fourier_add]
  simp

/-- The determinant symbol has winding zero. -/
theorem windingNumber_det_matrixSymbol :
    (⟨fun t => (matrixSymbol t).det, by fun_prop⟩ : C(UnitAddCircle, ℂ)).windingNumber
      (fun t => by simpa only [ContinuousMap.coe_mk, det_matrixSymbol] using
        (one_ne_zero : (1 : ℂ) ≠ 0)) = 0 :=
  (ContinuousMap.windingNumber_congr
    (fun t => by simpa only [ContinuousMap.coe_mk, det_matrixSymbol] using
      (one_ne_zero : (1 : ℂ) ≠ 0)) (fun _ => one_ne_zero)
    (g := (1 : C(UnitAddCircle, ℂ))) det_matrixSymbol).trans
      (ContinuousMap.windingNumber_one _)

/-- The same symbol on the native operator-valued `L∞` carrier. -/
def symbol : BlockSymbol 2 :=
  ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ
    ⟨fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (matrixSymbol t),
      Matrix.continuous_toEuclideanCLM.comp matrixSymbol.continuous⟩

/-- Entries of the operator-valued symbol are the continuous matrix entries as `L∞` classes. -/
theorem blockSymbolEntry_symbol (i j : Fin 2) :
    blockSymbolEntry 2 i j symbol = ContinuousMap.toLp ∞
      (AddCircle.haarAddCircle (T := 1)) ℂ
      (⟨fun t => matrixSymbol t i j, by fun_prop⟩ : C(UnitAddCircle, ℂ)) := by
  rw [symbol, blockSymbolEntry_toLp]
  congr 1
  ext t
  exact congrFun (Matrix.mulVec_single_one (matrixSymbol t) j) i

/-- The first diagonal entry is the forward Fourier mode. -/
@[simp] theorem blockSymbolEntry_zero_zero :
    blockSymbolEntry 2 0 0 symbol = fourierLp (T := 1) ∞ 1 := by
  rw [blockSymbolEntry_symbol]
  congr 1

/-- The second diagonal entry is the backward Fourier mode. -/
@[simp] theorem blockSymbolEntry_one_one :
    blockSymbolEntry 2 1 1 symbol = fourierLp (T := 1) ∞ (-1) := by
  rw [blockSymbolEntry_symbol]
  congr 1

/-- The upper off-diagonal entry vanishes. -/
@[simp] theorem blockSymbolEntry_zero_one : blockSymbolEntry 2 0 1 symbol = 0 := by
  rw [blockSymbolEntry_symbol]
  have h : (⟨fun t => matrixSymbol t 0 1, by fun_prop⟩ : C(UnitAddCircle, ℂ)) = 0 := by
    ext t
    simp [matrixSymbol_apply]
  rw [h, map_zero]

/-- The lower off-diagonal entry vanishes. -/
@[simp] theorem blockSymbolEntry_one_zero : blockSymbolEntry 2 1 0 symbol = 0 := by
  rw [blockSymbolEntry_symbol]
  have h : (⟨fun t => matrixSymbol t 1 0, by fun_prop⟩ : C(UnitAddCircle, ℂ)) = 0 := by
    ext t
    simp [matrixSymbol_apply]
  rw [h, map_zero]

private def split : BlockHardySpace 2 ≃L[ℂ] HardySpace × HardySpace :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => HardySpace)).trans
    (ContinuousLinearEquiv.finTwoArrow ℂ HardySpace)

/-- The first coordinate is the forward shift. -/
@[simp] theorem apply_zero (f : BlockHardySpace 2) :
    blockToeplitz 2 symbol f 0 = toeplitz (fourierLp (T := 1) ∞ 1) (f 0) := by
  simp [blockToeplitz_apply_apply, Fin.sum_univ_two]

/-- The second coordinate is the backward shift. -/
@[simp] theorem apply_one (f : BlockHardySpace 2) :
    blockToeplitz 2 symbol f 1 = toeplitz (fourierLp (T := 1) ∞ (-1)) (f 1) := by
  simp [blockToeplitz_apply_apply, Fin.sum_univ_two]

private theorem conjugate :
    blockToeplitz 2 symbol = split.symm.toContinuousLinearMap ∘L
      (toeplitz (fourierLp (T := 1) ∞ 1)).prodMap
        (toeplitz (fourierLp (T := 1) ∞ (-1))) ∘L split.toContinuousLinearMap := by
  ext f i
  fin_cases i <;> simp [split, apply_zero, apply_one]

/-- The opposite-shift block Toeplitz operator is Fredholm. -/
theorem isFredholm : ContinuousLinearMap.IsFredholm (blockToeplitz 2 symbol) := by
  rw [conjugate]
  exact ((isFredholm_toeplitz_fourierLp 1).prodMap
    (isFredholm_toeplitz_fourierLp (-1))).equiv_comp split.symm |>.comp_equiv split

/-- The opposite-shift block Toeplitz operator has Fredholm index zero. -/
theorem index_eq_zero : ContinuousLinearMap.index (blockToeplitz 2 symbol) = 0 := by
  have hS := isFredholm_toeplitz_fourierLp 1
  have hT := isFredholm_toeplitz_fourierLp (-1)
  let := hS.finite_ker
  let := hS.finite_coker
  let := hT.finite_ker
  let := hT.finite_coker
  let := Module.Free.of_divisionRing ℂ (toeplitz (fourierLp (T := 1) ∞ 1)).ker
  let := Module.Free.of_divisionRing ℂ (toeplitz (fourierLp (T := 1) ∞ (-1))).ker
  let := Module.Free.of_divisionRing ℂ
    (HardySpace ⧸ (toeplitz (fourierLp (T := 1) ∞ 1)).range)
  let := Module.Free.of_divisionRing ℂ
    (HardySpace ⧸ (toeplitz (fourierLp (T := 1) ∞ (-1))).range)
  rw [conjugate]
  norm_num [index_toeplitz_fourierLp]

/-- The operator annihilates the constant mode in its second component. -/
@[simp] theorem apply_second_constant :
    blockToeplitz 2 symbol (PiLp.single 2 1 (hardyBasis 0)) = 0 := by
  ext i
  fin_cases i <;> simp [apply_zero, apply_one]

private theorem apply_basis_second_constant :
    blockToeplitz 2 symbol (blockHardyBasis 2 (0, 1)) = 0 := by
  rw [blockHardyBasis_apply, apply_second_constant]

/-- The operator is not invertible even though its Fredholm index is zero. -/
theorem not_isUnit : ¬ IsUnit (blockToeplitz 2 symbol) := by
  intro h
  have hi := ContinuousLinearMap.isUnit_iff_bijective.mp h |>.1
  have hz := hi (apply_basis_second_constant.trans (map_zero _).symm)
  exact (blockHardyBasis 2).orthonormal.ne_zero (0, 1) hz

/-- Every pure finite block section has a zero column, hence determinant zero. -/
@[simp] theorem det_sectionMatrix (n : ℕ) :
    (blockFiniteSectionMatrix (blockToeplitz 2 symbol) n).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero (⟨0, by omega⟩, 1)
  intro i
  rw [blockFiniteSectionMatrix_apply, apply_basis_second_constant, inner_zero_right]

end ToeplitzOppositeShifts
end TauCeti
