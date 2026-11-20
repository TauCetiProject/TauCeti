/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Block.Toeplitz
public import TauCeti.Analysis.Fourier.Hardy.Fredholm
import TauCeti.Analysis.Fredholm.Prod
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Opposite shifts: zero determinant winding does not imply block Toeplitz invertibility

The symbol `diag(z, conj z)` on the circle has determinant one. Its block Toeplitz operator is
`S ⊕ S†`, Fredholm of index zero, but it kills the constant vector in its second component.
Every pure finite section is singular for the same reason.

This is the standard block-symbol obstruction to extending scalar Toeplitz invertibility
criteria to matrix symbols using only determinant winding. The scalar shift, backward shift
and Fredholm calculations are the accepted Hardy-space APIs; this example combines them.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*.

## Provenance

New example proof developed in the Kitware DKPS campaign using accepted Tau Ceti APIs;
no pre-existing DKPS theorem is claimed.
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
@[simp] theorem matrixSymbol_apply (t : UnitAddCircle) :
    matrixSymbol t = Matrix.diagonal ![fourier 1 t, fourier (-1) t] := (rfl)

/-- The determinant of the opposite-shift symbol is identically one. -/
theorem det_matrixSymbol (t : UnitAddCircle) : (matrixSymbol t).det = 1 := by
  simp only [matrixSymbol, ContinuousMap.coe_mk, Matrix.det_diagonal, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
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
  blockSymbolSingle 2 0 0 (fourierLp (T := 1) ∞ 1) +
    blockSymbolSingle 2 1 1 (fourierLp (T := 1) ∞ (-1))

/-- The scalar entries of the operator-valued symbol are exactly those of the continuous
matrix symbol, as L∞ classes. -/
theorem blockSymbolEntry_symbol (i j : Fin 2) :
    blockSymbolEntry 2 i j symbol = ContinuousMap.toLp ∞
      (AddCircle.haarAddCircle (T := 1)) ℂ
      (⟨fun t => matrixSymbol t i j, by fun_prop⟩ : C(UnitAddCircle, ℂ)) := by
  fin_cases i <;> fin_cases j
  · have h : fourier 1 = (⟨fun t => matrixSymbol t 0 0, by fun_prop⟩ :
        C(UnitAddCircle, ℂ)) := by ext t; simp [matrixSymbol]
    simpa [symbol, fourierLp] using
      congrArg (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ) h
  · have h : (0 : C(UnitAddCircle, ℂ)) = ⟨fun t => matrixSymbol t 0 1, by fun_prop⟩ := by
      ext t
      simp [matrixSymbol]
    simpa [symbol] using
      congrArg (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ) h
  · have h : (0 : C(UnitAddCircle, ℂ)) = ⟨fun t => matrixSymbol t 1 0, by fun_prop⟩ := by
      ext t
      simp [matrixSymbol]
    simpa [symbol] using
      congrArg (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ) h
  · have h : fourier (-1) = (⟨fun t => matrixSymbol t 1 1, by fun_prop⟩ :
        C(UnitAddCircle, ℂ)) := by ext t; simp [matrixSymbol]
    simpa [symbol, fourierLp] using
      congrArg (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ) h

private def split : BlockHardySpace 2 ≃L[ℂ] HardySpace × HardySpace :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => HardySpace)).trans
    (ContinuousLinearEquiv.finTwoArrow ℂ HardySpace)

private theorem apply_zero (f : BlockHardySpace 2) :
    blockToeplitz 2 symbol f 0 = toeplitz (fourierLp (T := 1) ∞ 1) (f 0) := by
  simp [blockToeplitz_apply_apply, symbol, Fin.sum_univ_two]

private theorem apply_one (f : BlockHardySpace 2) :
    blockToeplitz 2 symbol f 1 = toeplitz (fourierLp (T := 1) ∞ (-1)) (f 1) := by
  simp [blockToeplitz_apply_apply, symbol, Fin.sum_univ_two]

private theorem conjugate :
    blockToeplitz 2 symbol = split.symm.toContinuousLinearMap ∘L
      (toeplitz (fourierLp (T := 1) ∞ 1)).prodMap
        (toeplitz (fourierLp (T := 1) ∞ (-1))) ∘L split.toContinuousLinearMap := by
  ext f i
  fin_cases i <;> simp [split, apply_zero, apply_one]

/-- The block Toeplitz operator is Fredholm, using only the accepted binary product theorem. -/
theorem isFredholm : ContinuousLinearMap.IsFredholm (blockToeplitz 2 symbol) := by
  rw [conjugate]
  exact ((isFredholm_toeplitz_fourierLp 1).prodMap
    (isFredholm_toeplitz_fourierLp (-1))).equiv_comp split.symm |>.comp_equiv split

/-- The two scalar shift indices cancel. -/
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
  rw [conjugate, ContinuousLinearMap.index_equiv_comp,
    ContinuousLinearMap.index_comp_equiv, ContinuousLinearMap.index_prodMap,
    index_toeplitz_fourierLp, index_toeplitz_fourierLp]
  norm_num

/-- The second constant mode is a nonzero kernel vector. -/
@[simp] theorem apply_second_constant :
    blockToeplitz 2 symbol (PiLp.single 2 1 (hardyBasis 0)) = 0 := by
  ext i
  fin_cases i <;> simp [apply_zero, apply_one]

/-- The operator is not invertible even though its Fredholm index is zero. -/
theorem not_isUnit : ¬ IsUnit (blockToeplitz 2 symbol) := by
  intro h
  have hi := ContinuousLinearMap.isUnit_iff_bijective.mp h |>.1
  have hz := hi (show blockToeplitz 2 symbol (blockHardyBasis 2 (0, 1)) =
      blockToeplitz 2 symbol 0 by rw [blockHardyBasis_apply, apply_second_constant, map_zero])
  exact (blockHardyBasis 2).orthonormal.ne_zero (0, 1) hz

/-- The pure finite-section matrix in the first n+1 block positions, in the native Hardy basis. -/
def sectionMatrix (n : ℕ) :
    Matrix (Fin (n + 1) × Fin 2) (Fin (n + 1) × Fin 2) ℂ :=
  fun i j => ⟪blockHardyBasis 2 (i.1, i.2),
    blockToeplitz 2 symbol (blockHardyBasis 2 (j.1, j.2))⟫_ℂ

/-- The entries are the usual block Toeplitz matrix coefficients in the Hardy basis. -/
@[simp] theorem sectionMatrix_apply (n : ℕ) (i j : Fin (n + 1) × Fin 2) :
    sectionMatrix n i j = ⟪blockHardyBasis 2 (i.1, i.2),
      blockToeplitz 2 symbol (blockHardyBasis 2 (j.1, j.2))⟫_ℂ := (rfl)

/-- Every pure finite section has a zero column, hence determinant zero. -/
@[simp] theorem det_sectionMatrix (n : ℕ) : (sectionMatrix n).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero (⟨0, by omega⟩, 1)
  intro i
  simp only [sectionMatrix, blockHardyBasis_apply, apply_second_constant, inner_zero_right]

end ToeplitzOppositeShifts
end TauCeti
