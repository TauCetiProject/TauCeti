/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import TauCeti.Analysis.Matrix.Exponential.SkewAdjoint
public import TauCeti.LinearAlgebra.Matrix.Triangular.Coordinates
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Schur coordinates of a complex matrix

The Schur parametrization assembles an upper triangular matrix and conjugates it by
a transverse unitary exponential in a fixed unitary frame. The characteristic polynomial
of the resulting matrix is determined by the diagonal of the triangular input.
-/

public section

noncomputable section

namespace TauCeti

open Matrix

variable {n : ℕ}

/-- The input gives the upper triangular entries and the strict lower angular coordinates.
Negatively conjugate the angles for `expStrictUpper`, apply the resulting unitary in the fixed
frame, and split the resulting matrix into its upper triangular and strict lower entries. -/
def _root_.Matrix.UnitaryGroup.schurCoordinates (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates (Fin n) ℂ) : SchurCoordinates (Fin n) ℂ :=
  schurMatrixEquiv.symm
    (Unitary.conjStarAlgAut ℂ _ (U * expStrictUpper (fun ij ↦ -star (x.2 ij)))
      (schurMatrixEquiv (x.1, 0)))

open Matrix.UnitaryGroup

/-- The Schur parametrization assembles the upper triangular input and conjugates it
by the unitary exponential in the fixed frame. -/
theorem _root_.Matrix.UnitaryGroup.schurCoordinates_apply (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates (Fin n) ℂ) :
    schurCoordinates U x = schurMatrixEquiv.symm
      (Unitary.conjStarAlgAut ℂ _ (U * expStrictUpper (fun ij ↦ -star (x.2 ij)))
        (schurMatrixEquiv (x.1, 0))) :=
  (rfl)

/-- Zero angles give the unitary conjugate of the upper triangular input by the fixed frame. -/
@[simp] theorem _root_.Matrix.UnitaryGroup.schurCoordinates_zero (U : unitaryGroup (Fin n) ℂ)
    (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) :
    schurCoordinates U (a, 0) = schurMatrixEquiv.symm
      (Unitary.conjStarAlgAut ℂ _ U (schurMatrixEquiv (a, 0))) := by
  have h : (fun ij : FinStrictUpper n ↦ -star ((0 : FinStrictUpper n → ℂ) ij)) = 0 := by
    funext ij
    simp
  rw [schurCoordinates_apply, h, expStrictUpper_zero, mul_one]

/-- The complex matrix parametrized by the upper triangular entries and the angles in a
fixed unitary frame. -/
def _root_.Matrix.UnitaryGroup.schurMatrix (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  schurMatrixEquiv (schurCoordinates U x)

/-- Reading the entries of the parametrized matrix gives the Schur coordinate map. -/
@[simp] theorem _root_.Matrix.UnitaryGroup.schurMatrixEquiv_symm_schurMatrix
    (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates (Fin n) ℂ) :
    schurMatrixEquiv.symm (schurMatrix U x) = schurCoordinates U x :=
  schurMatrixEquiv.symm_apply_apply _

/-- The matrix parametrization conjugates the triangular input by the fixed frame followed by
the transverse unitary exponential. -/
theorem _root_.Matrix.UnitaryGroup.schurMatrix_apply (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates (Fin n) ℂ) :
    schurMatrix U x = Unitary.conjStarAlgAut ℂ _
      (U * expStrictUpper (fun ij ↦ -star (x.2 ij))) (schurMatrixEquiv (x.1, 0)) := by
  rw [schurMatrix, schurCoordinates_apply, LinearEquiv.apply_symm_apply]

/-- At zero angles the matrix parametrization conjugates the upper triangular matrix by the
fixed frame. -/
@[simp] theorem _root_.Matrix.UnitaryGroup.schurMatrix_zero (U : unitaryGroup (Fin n) ℂ)
    (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) :
    schurMatrix U (a, 0) = Unitary.conjStarAlgAut ℂ _ U (schurMatrixEquiv (a, 0)) := by
  rw [schurMatrix, schurCoordinates_zero, LinearEquiv.apply_symm_apply]

/-- The characteristic polynomial of the Schur matrix has the diagonal input entries as roots,
with multiplicities. -/
theorem _root_.Matrix.UnitaryGroup.charpoly_schurMatrix (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates (Fin n) ℂ) :
    (schurMatrix U x).charpoly =
      ∏ i : Fin n, (Polynomial.X - Polynomial.C (x.1 ⟨(i, i), le_rfl⟩)) := by
  let V := U * expStrictUpper (fun ij ↦ -star (x.2 ij))
  have hconj (T : Matrix (Fin n) (Fin n) ℂ) :
      (Unitary.conjStarAlgAut ℂ _ V T).charpoly = T.charpoly := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] using
      (charpoly_unitary_conj T (star V))
  rw [schurMatrix_apply, hconj, charpoly_of_isUpperTriangular _
    ((isUpperTriangular_schurMatrixEquiv_iff (x.1, 0)).2 rfl)]
  simp only [schurMatrixEquiv_apply_of_le _ le_rfl]

end TauCeti
