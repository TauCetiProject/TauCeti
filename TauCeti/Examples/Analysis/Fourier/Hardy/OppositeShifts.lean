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

/-!
# Opposite shifts: zero determinant winding does not imply block Toeplitz invertibility

The symbol `diag(z, conj z)` on the circle has determinant one. Its block Toeplitz operator is
`S ⊕ S†`, Fredholm of index zero, but it kills the constant vector in its second component.
Compression to the first `n + 1` full blocks is singular for the same reason.

This is the standard block-symbol obstruction to extending scalar Toeplitz invertibility
criteria to matrix symbols using only determinant winding. The forward and backward shift
coordinate actions identify the direct sum; the two scalar Fredholm indices cancel.

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
  ⟨fun t => Matrix.diagonal (fun i => fourier (![1, -1] i) t), by fun_prop⟩

/-- Evaluation of the continuous diagonal symbol. -/
theorem matrixSymbol_apply (t : UnitAddCircle) :
    matrixSymbol t = Matrix.diagonal (fun i => fourier (![1, -1] i) t) := (rfl)

/-- The determinant of the opposite-shift symbol is identically one. -/
@[simp] theorem det_matrixSymbol (t : UnitAddCircle) : (matrixSymbol t).det = 1 := by
  rw [matrixSymbol_apply, Matrix.det_diagonal, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
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

/-- The native symbol is the whole continuous matrix symbol converted to `L∞`. -/
theorem symbol_def :
    symbol = ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ
      ⟨fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (matrixSymbol t),
        Matrix.continuous_toEuclideanCLM.comp matrixSymbol.continuous⟩ := by
  rw [symbol]

/-- The opposite-shift symbol is diagonal, with Fourier modes indexed by its two rows. -/
theorem blockSymbolEntry_eq (i j : Fin 2) :
    blockSymbolEntry 2 i j symbol =
      if i = j then fourierLp (T := 1) ∞ (![1, -1] i) else 0 := by
  rw [symbol_def, blockSymbolEntry_toLp_matrix]
  have h : (⟨fun t => matrixSymbol t i j, by fun_prop⟩ : C(UnitAddCircle, ℂ)) =
      if i = j then fourier (![1, -1] i) else 0 := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      ext t
      simp only [ContinuousMap.coe_mk, matrixSymbol_apply, Matrix.diagonal_apply_eq]
    · rw [ite_eq_right hij]
      ext t
      simp only [ContinuousMap.coe_mk, ContinuousMap.zero_apply, matrixSymbol_apply,
        Matrix.diagonal_apply_ne _ hij]
  rw [h]
  split_ifs <;> simp [fourierLp]

/-- Coordinatewise, the opposite-shift block operator applies the corresponding scalar shift. -/
theorem apply_coordinate (f : BlockHardySpace 2) (i : Fin 2) :
    blockToeplitz 2 symbol f i = toeplitz (fourierLp (T := 1) ∞ (![1, -1] i)) (f i) := by
  rw [blockToeplitz_apply_of_row_offDiagonal_eq_zero]
  · simp [blockSymbolEntry_eq]
  · intro j hji
    simp [blockSymbolEntry_eq, Ne.symm hji]

/-- The block operator is the direct sum of the forward and backward scalar shifts. -/
theorem conjugate :
    blockToeplitz 2 symbol = ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => HardySpace)).trans
      (ContinuousLinearEquiv.finTwoArrow ℂ HardySpace)).symm.conjContinuousAlgEquiv
        ((toeplitz (fourierLp (T := 1) ∞ 1)).prodMap
          (toeplitz (fourierLp (T := 1) ∞ (-1)))) := by
  ext f i
  fin_cases i <;> simp [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply, apply_coordinate]

/-- The opposite-shift block Toeplitz operator is Fredholm. -/
theorem isFredholm : ContinuousLinearMap.IsFredholm (blockToeplitz 2 symbol) := by
  rw [conjugate, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
  simpa only [ContinuousLinearMap.isFredholm_equiv_comp,
    ContinuousLinearMap.isFredholm_comp_equiv] using
    ((isFredholm_toeplitz_fourierLp 1).prodMap (isFredholm_toeplitz_fourierLp (-1)))

/-- The opposite-shift block Toeplitz operator has Fredholm index zero. -/
theorem index_eq_zero : ContinuousLinearMap.index (blockToeplitz 2 symbol) = 0 := by
  rw [conjugate, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply,
    ContinuousLinearMap.index_equiv_comp, ContinuousLinearMap.index_comp_equiv,
    (isFredholm_toeplitz_fourierLp 1).index_prodMap (isFredholm_toeplitz_fourierLp (-1))]
  norm_num [index_toeplitz_fourierLp]

/-- The operator annihilates the constant mode in its second component. -/
theorem apply_second_constant :
    blockToeplitz 2 symbol (blockHardyBasis 2 (0, 1)) = 0 := by
  rw [blockHardyBasis_apply]
  ext i
  fin_cases i <;> simp [apply_coordinate]

/-- The operator is not invertible even though its Fredholm index is zero. -/
theorem not_isUnit : ¬ IsUnit (blockToeplitz 2 symbol) := by
  intro h
  have hi := ContinuousLinearMap.isUnit_iff_bijective.mp h |>.1
  have hz := hi (apply_second_constant.trans (map_zero _).symm)
  exact (blockHardyBasis 2).orthonormal.ne_zero (0, 1) hz

/-- Compression to the first `n + 1` full blocks has determinant zero. -/
@[simp] theorem det_sectionMatrix (n : ℕ) :
    (blockFiniteSectionMatrix (blockToeplitz 2 symbol) n).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero (⟨0, by omega⟩, 1)
  intro i
  rw [blockFiniteSectionMatrix_apply, apply_second_constant, inner_zero_right]

/-- The native finite section at every leading full-block cutoff is noninvertible. -/
theorem not_isUnit_finiteSection (n : ℕ) :
    ¬IsUnit ((blockToeplitz 2 symbol).finiteSection (blockHardyBasisNat 2) ((n + 1) * 2 - 1)) := by
  intro h
  have hd := (LinearMap.isUnit_iff_isUnit_det _).1
    (h.map ContinuousLinearMap.toLinearMapRingHom)
  simp only [ContinuousLinearMap.toLinearMapRingHom_apply] at hd
  rw [det_finiteSection_eq_blockFiniteSectionMatrix, det_sectionMatrix] at hd
  exact not_isUnit_zero hd

end ToeplitzOppositeShifts
end TauCeti
