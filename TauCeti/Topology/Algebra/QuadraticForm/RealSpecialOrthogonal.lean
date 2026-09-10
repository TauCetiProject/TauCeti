/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm
public import Mathlib.Topology.UniformSpace.Real
import TauCeti.Topology.Algebra.UnitaryGroup
public import TauCeti.Topology.Algebra.QuadraticForm.SpecialOrthogonal
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm

/-!
# Compactness of positive-definite real special orthogonal groups

The standard real sum-of-squares form has a special orthogonal group which is the continuous image
of the compact real special orthogonal matrix group. This gives the construction for any finite
coordinate type. Specializing to the positive-definite form `realCliffordForm n 0` supplies the
quadratic-form model used as the target of the compact real Spin projection with its canonical
compact-space instance.

The transfer follows the existing coordinate embedding into the general linear group. An
orthogonal matrix defines a form-preserving linear equivalence, and its inverse matrix is its
transpose, so the resulting map is continuous for the induced topology.

## Main results

* `TauCeti.QuadraticMap.instCompactSpaceSpecialOrthogonalGroupWeightedSumSquaresOne`: the special
  orthogonal group of the standard sum-of-squares form on any finite coordinate type is compact.
* `TauCeti.QuadraticMap.instCompactSpaceSpecialOrthogonalGroupRealCliffordForm`: the associated
  special orthogonal group is compact.
-/

public section

open Matrix

namespace TauCeti

universe u

private theorem weightedSumSquares_one_eq_toQuadraticForm_one
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ) =
      Matrix.toQuadraticForm' (1 : Matrix ι ι ℝ) := by
  ext x
  simp only [QuadraticMap.weightedSumSquares_apply, Pi.one_apply, one_smul,
    Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', Matrix.one_mulVec, dotProduct]

namespace QuadraticMap

noncomputable section

private def matrixSpecialOrthogonalToWeightedSumSquares
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Matrix.specialOrthogonalGroup ι ℝ →
      specialOrthogonalGroup (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) := fun A => by
  let U : Matrix.orthogonalGroup ι ℝ := ⟨A, A.prop.1⟩
  let e := Matrix.UnitaryGroup.toLinearEquiv U
  refine ⟨e, ?_⟩
  rw [weightedSumSquares_one_eq_toQuadraticForm_one]
  apply (TauCeti.toMatrix_mem_specialOrthogonalGroup_iff ℝ ι
    ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) e).mp
  simpa only [e, Matrix.UnitaryGroup.toLinearEquiv,
    Matrix.UnitaryGroup.toLin', LinearMap.toMatrix'_toLin'] using A.prop

private theorem matrixSpecialOrthogonalToWeightedSumSquares_surjective
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Function.Surjective (matrixSpecialOrthogonalToWeightedSumSquares ι) := by
  intro g
  let A : Matrix.specialOrthogonalGroup ι ℝ :=
    ⟨LinearMap.toMatrix' (g : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)).toLinearMap, by
      apply (TauCeti.toMatrix_mem_specialOrthogonalGroup_iff ℝ ι
        ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) _).mpr
      simpa only [← weightedSumSquares_one_eq_toQuadraticForm_one] using g.prop⟩
  refine ⟨A, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  -- Unfold the coordinate equivalence just enough to use the matrix/linear-map round trip.
  change Matrix.toLin' (A : Matrix ι ι ℝ) x = (g : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) x
  dsimp only [A]
  rw [Matrix.toLin'_toMatrix']
  rfl

private theorem specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquares
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Matrix.specialOrthogonalGroup ι ℝ) :
    specialOrthogonalToGeneralLinear (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))
        (matrixSpecialOrthogonalToWeightedSumSquares ι A) =
      Unitary.toUnits (⟨A, A.prop.1⟩ : Matrix.orthogonalGroup ι ℝ) := by
  apply Units.ext
  ext i j
  rw [specialOrthogonalToGeneralLinear_apply]
  simp [matrixSpecialOrthogonalToWeightedSumSquares, Matrix.UnitaryGroup.toLinearEquiv,
    Matrix.UnitaryGroup.toLin', Matrix.toLin'_apply, Matrix.mulVec]

private theorem continuous_matrixSpecialOrthogonalToWeightedSumSquares
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Continuous (matrixSpecialOrthogonalToWeightedSumSquares ι) := by
  rw [(isEmbedding_specialOrthogonalToGeneralLinear
    (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))).continuous_iff]
  -- Identify the composite pointwise with the coordinate inclusion into the matrix units.
  rw [show specialOrthogonalToGeneralLinear
      (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) ∘
      matrixSpecialOrthogonalToWeightedSumSquares ι =
        fun (A : Matrix.specialOrthogonalGroup ι ℝ) =>
          Unitary.toUnits (⟨A, A.prop.1⟩ : Matrix.orthogonalGroup ι ℝ) by
    funext A
    exact specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquares ι A]
  apply Units.continuous_iff.mpr
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_transpose⟩

/-- The special orthogonal group of the standard real sum-of-squares form is compact. -/
instance instCompactSpaceSpecialOrthogonalGroupWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    CompactSpace (specialOrthogonalGroup
      (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) :=
  (matrixSpecialOrthogonalToWeightedSumSquares_surjective ι).compactSpace
    (continuous_matrixSpecialOrthogonalToWeightedSumSquares ι)

private theorem realCliffordForm_zero_eq_weightedSumSquares_one (n : ℕ) :
    realCliffordForm n 0 =
      _root_.QuadraticMap.weightedSumSquares ℝ (1 : Fin n → ℝ) := by
  ext x
  simp only [realCliffordForm_apply, _root_.QuadraticMap.weightedSumSquares_apply,
    Pi.one_apply, one_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [realCliffordWeight_of_lt (by omega), one_mul]

/-- The special orthogonal group of the positive-definite real Clifford form is compact. -/
instance instCompactSpaceSpecialOrthogonalGroupRealCliffordForm (n : ℕ) :
    CompactSpace (specialOrthogonalGroup (realCliffordForm n 0)) := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one]
  infer_instance

end

end QuadraticMap

end TauCeti
