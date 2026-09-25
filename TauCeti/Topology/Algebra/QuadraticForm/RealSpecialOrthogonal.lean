/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.UniformSpace.Real
import TauCeti.Topology.Algebra.UnitaryGroup
public import TauCeti.Topology.Algebra.QuadraticForm.SpecialOrthogonal
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
public import TauCeti.LinearAlgebra.QuadraticForm.Standard

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
* `TauCeti.QuadraticMap.mem_range_specialOrthogonalToGeneralLinear_weightedSumSquares_one_iff`:
  membership in its general-linear carrier is matrix special-orthogonal membership.
* `TauCeti.QuadraticMap.instCompactSpaceSpecialOrthogonalGroupRealCliffordForm`: the associated
  special orthogonal group is compact.
* `TauCeti.QuadraticMap.isClosed_range_specialOrthogonalToGeneralLinear_realCliffordForm`: the
  positive-definite real special-orthogonal carrier is closed in its general-linear ambient group.
-/

public section

open Matrix

namespace Matrix.UnitaryGroup

universe u v

variable {ι : Type u} {R : Type v} [Fintype ι] [DecidableEq ι]
  [CommRing R] [StarRing R]

/-- The coordinate matrix of the linear equivalence associated to a unitary matrix is that
matrix. -/
@[simp]
theorem toMatrix'_toLinearEquiv (A : Matrix.unitaryGroup ι R) :
    LinearMap.toMatrix' (toLinearEquiv A).toLinearMap = (A : Matrix ι ι R) := by
  exact LinearMap.toMatrix'_toLin' (A : Matrix ι ι R)

end Matrix.UnitaryGroup

namespace TauCeti

universe u

namespace QuadraticMap

noncomputable section

section CoordinateBridge

/-- Turn a real special-orthogonal matrix into an isometry of the standard sum-of-squares form. -/
@[expose] def matrixSpecialOrthogonalToWeightedSumSquares
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Matrix.specialOrthogonalGroup ι ℝ →
      specialOrthogonalGroup
        (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) := fun A => by
  let U : Matrix.orthogonalGroup ι ℝ := ⟨A, A.prop.1⟩
  let e := Matrix.UnitaryGroup.toLinearEquiv U
  refine ⟨e, ?_⟩
  rw [weightedSumSquares_eq_toQuadraticForm_diagonal, Matrix.diagonal_one']
  apply (TauCeti.toMatrix_mem_specialOrthogonalGroup_iff ℝ ι
    ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) e).mp
  simpa only [e, Matrix.UnitaryGroup.toMatrix'_toLinearEquiv] using A.prop

/-- The underlying linear equivalence acts by matrix-vector multiplication. -/
theorem matrixSpecialOrthogonalToWeightedSumSquares_apply
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Matrix.specialOrthogonalGroup ι ℝ) (x : ι → ℝ) :
    ((matrixSpecialOrthogonalToWeightedSumSquares ι A :
        specialOrthogonalGroup (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) :
      (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) x = Matrix.toLin' (A : Matrix ι ι ℝ) x :=
  rfl

/-- Every isometry of the standard sum-of-squares form comes from a special-orthogonal matrix. -/
theorem matrixSpecialOrthogonalToWeightedSumSquares_surjective
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
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

/-- The coordinate inclusion of a matrix-induced sum-of-squares isometry recovers the matrix. -/
theorem specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquares
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Matrix.specialOrthogonalGroup ι ℝ) :
    specialOrthogonalToGeneralLinear (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))
        (matrixSpecialOrthogonalToWeightedSumSquares ι A) =
      Unitary.toUnits (⟨A, A.prop.1⟩ : Matrix.orthogonalGroup ι ℝ) := by
  apply Units.ext
  ext i j
  rw [specialOrthogonalToGeneralLinear_apply]
  rw [matrixSpecialOrthogonalToWeightedSumSquares_apply]
  simp [Matrix.toLin'_apply, Matrix.mulVec]

/-- Membership in the general-linear carrier of the standard real sum-of-squares special
orthogonal group is matrix special-orthogonal membership. -/
theorem mem_range_specialOrthogonalToGeneralLinear_weightedSumSquares_one_iff
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (U : Matrix.GeneralLinearGroup ι ℝ) :
    U ∈ MonoidHom.range (specialOrthogonalToGeneralLinear
        (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) ↔
      (U : Matrix ι ι ℝ) ∈ Matrix.specialOrthogonalGroup ι ℝ := by
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨A, rfl⟩ := matrixSpecialOrthogonalToWeightedSumSquares_surjective ι g
    rw [specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquares]
    exact A.prop
  · intro hU
    let A : Matrix.specialOrthogonalGroup ι ℝ := ⟨(U : Matrix ι ι ℝ), hU⟩
    refine ⟨matrixSpecialOrthogonalToWeightedSumSquares ι A, ?_⟩
    rw [specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquares]
    apply Units.ext
    rfl

section ClassicalDecEq

attribute [local instance] Classical.decEq

/-- Membership in the positive-definite `realCliffordForm n 0` special-orthogonal carrier is matrix
special-orthogonal membership. -/
theorem mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff
    (n : ℕ) (U : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    U ∈ MonoidHom.range (specialOrthogonalToGeneralLinear (realCliffordForm n 0)) ↔
      (U : Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one]
  exact mem_range_specialOrthogonalToGeneralLinear_weightedSumSquares_one_iff (Fin n) U

private theorem continuous_matrixSpecialOrthogonalToWeightedSumSquares
    (ι : Type u) [Fintype ι] :
    Continuous (matrixSpecialOrthogonalToWeightedSumSquares ι) := by
  rw [(isEmbedding_specialOrthogonalToGeneralLinear
    (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))).continuous_iff]
  have hc : Continuous (fun (A : Matrix.specialOrthogonalGroup ι ℝ) =>
      Unitary.toUnits (⟨A, A.prop.1⟩ : Matrix.orthogonalGroup ι ℝ)) := by
    apply Units.continuous_iff.mpr
    exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_transpose⟩
  rw [Function.comp_def]
  exact hc.congr
    (g := fun A => specialOrthogonalToGeneralLinear
      (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))
        (matrixSpecialOrthogonalToWeightedSumSquares ι A)) fun A =>
      (specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquares ι A).symm

/-- The special orthogonal group of the standard real sum-of-squares form is compact. -/
instance instCompactSpaceRealSpecialOrthogonalGroupWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] :
    CompactSpace (specialOrthogonalGroup
      (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) := by
  classical
  exact (matrixSpecialOrthogonalToWeightedSumSquares_surjective ι).compactSpace
    (continuous_matrixSpecialOrthogonalToWeightedSumSquares ι)

/-- The special orthogonal group of the positive-definite real Clifford form is compact. -/
instance instCompactSpaceSpecialOrthogonalGroupRealCliffordForm (n : ℕ) :
    CompactSpace (specialOrthogonalGroup (realCliffordForm n 0)) := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one]
  exact (@matrixSpecialOrthogonalToWeightedSumSquares_surjective (Fin n) _
      (Classical.decEq _)).compactSpace
    (continuous_matrixSpecialOrthogonalToWeightedSumSquares (Fin n))

end ClassicalDecEq

end CoordinateBridge

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
