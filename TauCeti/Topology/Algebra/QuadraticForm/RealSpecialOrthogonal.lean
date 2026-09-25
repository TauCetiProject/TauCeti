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
import TauCeti.LinearAlgebra.QuadraticForm.Standard

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

* `TauCeti.QuadraticMap.instCompactSpaceRealSpecialOrthogonalGroupWeightedSumSquaresOne`: the
  special orthogonal group of the standard sum-of-squares form on any finite coordinate type is
  compact.
* `TauCeti.QuadraticMap.instCompactSpaceSpecialOrthogonalGroupRealCliffordForm`: the associated
  special orthogonal group is compact.
* `TauCeti.QuadraticMap.isClosed_range_specialOrthogonalToGeneralLinear_realCliffordForm`: the
  positive-definite real special-orthogonal carrier is closed in its general-linear ambient group.
-/

public section

open Matrix

namespace TauCeti

universe u

namespace QuadraticMap

noncomputable section

section ClassicalDecEq

attribute [local instance] Classical.decEq

private def matrixSpecialOrthogonalToWeightedSumSquares
    (ι : Type u) [Fintype ι] :
    Matrix.specialOrthogonalGroup ι ℝ →
      specialOrthogonalGroup (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) := fun A => by
  let U : Matrix.orthogonalGroup ι ℝ := ⟨A, A.prop.1⟩
  let e := Matrix.UnitaryGroup.toLinearEquiv U
  refine ⟨e, ?_⟩
  rw [weightedSumSquares_eq_toQuadraticForm_diagonal, Matrix.diagonal_one']
  apply (TauCeti.toMatrix_mem_specialOrthogonalGroup_iff ℝ ι
    ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) e).mp
  simpa only [e, Matrix.UnitaryGroup.toLinearEquiv,
    Matrix.UnitaryGroup.toLin', LinearMap.toMatrix'_toLin'] using A.prop

/-- The underlying linear equivalence acts by matrix-vector multiplication. -/
private theorem matrixSpecialOrthogonalToWeightedSumSquares_apply
    (ι : Type u) [Fintype ι]
    (A : Matrix.specialOrthogonalGroup ι ℝ) (x : ι → ℝ) :
    ((matrixSpecialOrthogonalToWeightedSumSquares ι A :
        specialOrthogonalGroup (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) :
      (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) x = Matrix.toLin' (A : Matrix ι ι ℝ) x :=
  rfl

private theorem matrixSpecialOrthogonalToWeightedSumSquares_surjective
    (ι : Type u) [Fintype ι] :
    Function.Surjective (matrixSpecialOrthogonalToWeightedSumSquares ι) := by
  intro g
  let A : Matrix.specialOrthogonalGroup ι ℝ :=
    ⟨LinearMap.toMatrix' (g : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)).toLinearMap, by
      apply (TauCeti.toMatrix_mem_specialOrthogonalGroup_iff ℝ ι
        ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) _).mpr
      simpa only [weightedSumSquares_eq_toQuadraticForm_diagonal, Matrix.diagonal_one'] using
        g.prop⟩
  refine ⟨A, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [matrixSpecialOrthogonalToWeightedSumSquares_apply]
  exact LinearMap.congr_fun (Matrix.toLin'_toMatrix'
    (g : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)).toLinearMap) x

private theorem specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquares
    (ι : Type u) [Fintype ι]
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
    (ι : Type u) [Fintype ι] :
    Continuous (matrixSpecialOrthogonalToWeightedSumSquares ι) := by
  rw [(isEmbedding_specialOrthogonalToGeneralLinear
    (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))).continuous_iff]
  have hcomp : specialOrthogonalToGeneralLinear
      (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) ∘
      matrixSpecialOrthogonalToWeightedSumSquares ι =
        fun (A : Matrix.specialOrthogonalGroup ι ℝ) =>
          Unitary.toUnits (⟨A, A.prop.1⟩ : Matrix.orthogonalGroup ι ℝ) := by
    funext A
    exact specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquares ι A
  rw [hcomp]
  apply Units.continuous_iff.mpr
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_transpose⟩

/-- The special orthogonal group of the standard real sum-of-squares form is compact. -/
instance instCompactSpaceRealSpecialOrthogonalGroupWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] :
    CompactSpace (specialOrthogonalGroup
      (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) := by
  exact (matrixSpecialOrthogonalToWeightedSumSquares_surjective ι).compactSpace
    (continuous_matrixSpecialOrthogonalToWeightedSumSquares ι)

/-- The special orthogonal group of the positive-definite real Clifford form is compact. -/
instance instCompactSpaceSpecialOrthogonalGroupRealCliffordForm (n : ℕ) :
    CompactSpace (specialOrthogonalGroup (realCliffordForm n 0)) := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one]
  exact instCompactSpaceRealSpecialOrthogonalGroupWeightedSumSquaresOne (Fin n)

end ClassicalDecEq

/-- The real special-orthogonal carrier is closed in its general-linear ambient group. -/
theorem isClosed_range_specialOrthogonalToGeneralLinear_realCliffordForm (n : ℕ) :
    let _ : DecidableEq (Fin (n + 0)) := Classical.decEq _
    IsClosed (Set.range (specialOrthogonalToGeneralLinear (realCliffordForm n 0))) := by
  dsimp
  have hc : IsCompact (Set.univ : Set (specialOrthogonalGroup (realCliffordForm n 0))) :=
    isCompact_univ
  simpa only [Set.image_univ] using
    (hc.image (isEmbedding_specialOrthogonalToGeneralLinear
      (realCliffordForm n 0)).continuous).isClosed

end

end QuadraticMap

end TauCeti
