/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm
public import TauCeti.Topology.Algebra.UnitaryGroup
public import TauCeti.Topology.Algebra.QuadraticForm.SpecialOrthogonal
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm

/-!
# Compactness of positive-definite real special orthogonal groups

The positive-definite real form `realCliffordForm n 0` is the standard sum of squares. Its special
orthogonal group is therefore the continuous image of the compact real special orthogonal matrix
group. This gives the quadratic-form model used as the target of the compact real Spin projection
its canonical compact-space instance.

The transfer follows the existing coordinate embedding into the general linear group. An
orthogonal matrix defines a form-preserving linear equivalence, and its inverse matrix is its
transpose, so the resulting map is continuous for the induced topology.

## Main results

* `TauCeti.QuadraticMap.instCompactSpaceSpecialOrthogonalGroupRealCliffordForm`: the associated
  special orthogonal group is compact.
-/

public section

open Matrix

namespace TauCeti

private theorem realCliffordForm_zero_eq_toQuadraticForm_one (n : ℕ) :
    realCliffordForm n 0 =
      Matrix.toQuadraticForm' (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext x
  rw [realCliffordForm_apply]
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', Matrix.one_mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [realCliffordWeight_of_lt (by omega), one_mul]

namespace QuadraticMap

noncomputable section

private def matrixSpecialOrthogonalToRealClifford (n : ℕ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ →
      specialOrthogonalGroup (realCliffordForm n 0) := fun A => by
  let U : Matrix.orthogonalGroup (Fin n) ℝ := ⟨A, A.prop.1⟩
  let e := Matrix.UnitaryGroup.toLinearEquiv U
  refine ⟨e, ?_⟩
  rw [realCliffordForm_zero_eq_toQuadraticForm_one]
  apply (TauCeti.toMatrix_mem_specialOrthogonalGroup_iff ℝ (Fin n)
    ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) e).mp
  simpa only [e, Matrix.UnitaryGroup.toLinearEquiv,
    Matrix.UnitaryGroup.toLin', LinearMap.toMatrix'_toLin'] using A.prop

private theorem matrixSpecialOrthogonalToRealClifford_surjective (n : ℕ) :
    Function.Surjective (matrixSpecialOrthogonalToRealClifford n) := by
  intro g
  let A : Matrix.specialOrthogonalGroup (Fin n) ℝ :=
    ⟨LinearMap.toMatrix' (g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)).toLinearMap, by
      apply (TauCeti.toMatrix_mem_specialOrthogonalGroup_iff ℝ (Fin n)
        ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) _).mpr
      simpa only [← realCliffordForm_zero_eq_toQuadraticForm_one] using g.prop⟩
  refine ⟨A, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  -- Unfold the coordinate equivalence just enough to use the matrix/linear-map round trip.
  change Matrix.toLin' (A : Matrix (Fin n) (Fin n) ℝ) x =
    (g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) x
  dsimp only [A]
  rw [Matrix.toLin'_toMatrix']
  rfl

private theorem specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToRealClifford
    (n : ℕ) (A : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    specialOrthogonalToGeneralLinear (realCliffordForm n 0)
        (matrixSpecialOrthogonalToRealClifford n A) =
      Unitary.toUnits (⟨A, A.prop.1⟩ : Matrix.orthogonalGroup (Fin n) ℝ) := by
  apply Units.ext
  ext i j
  rw [specialOrthogonalToGeneralLinear_apply]
  simp [matrixSpecialOrthogonalToRealClifford, Matrix.UnitaryGroup.toLinearEquiv,
    Matrix.UnitaryGroup.toLin', Matrix.toLin'_apply, Matrix.mulVec]

private theorem continuous_matrixSpecialOrthogonalToRealClifford (n : ℕ) :
    Continuous (matrixSpecialOrthogonalToRealClifford n) := by
  rw [(isEmbedding_specialOrthogonalToGeneralLinear
    (realCliffordForm n 0)).continuous_iff]
  -- Identify the composite pointwise with the coordinate inclusion into the matrix units.
  rw [show specialOrthogonalToGeneralLinear (realCliffordForm n 0) ∘
      matrixSpecialOrthogonalToRealClifford n =
        fun (A : Matrix.specialOrthogonalGroup (Fin n) ℝ) =>
          Unitary.toUnits (⟨A, A.prop.1⟩ : Matrix.orthogonalGroup (Fin n) ℝ) by
    funext A
    exact specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToRealClifford n A]
  apply Units.continuous_iff.mpr
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_transpose⟩

/-- The special orthogonal group of the positive-definite real Clifford form is compact. -/
instance instCompactSpaceSpecialOrthogonalGroupRealCliffordForm (n : ℕ) :
    CompactSpace (specialOrthogonalGroup (realCliffordForm n 0)) :=
  (matrixSpecialOrthogonalToRealClifford_surjective n).compactSpace
    (continuous_matrixSpecialOrthogonalToRealClifford n)

end

end QuadraticMap

end TauCeti
