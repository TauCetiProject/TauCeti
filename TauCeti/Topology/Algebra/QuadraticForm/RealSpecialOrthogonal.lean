/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
public import Mathlib.Topology.UniformSpace.Real
public import TauCeti.Topology.Algebra.OrthogonalGroup
import TauCeti.Topology.Algebra.UnitaryGroup
public import TauCeti.Topology.Algebra.QuadraticForm.SpecialOrthogonal
public import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.WeightedSumSquares

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

* `TauCeti.QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivWeightedSumSquaresOne`: real
  special-orthogonal matrices and the determinant-one isometries of the standard sum-of-squares
  form are isomorphic topological groups.
* `TauCeti.QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm`: the same
  isomorphism with target the special orthogonal group of `realCliffordForm n 0`, acting by
  matrix-vector multiplication (`matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm_apply`).
* `TauCeti.QuadraticMap.instCompactSpaceRealSpecialOrthogonalGroupWeightedSumSquaresOne`: the
  special orthogonal group of the standard sum-of-squares form on any finite coordinate type is
  compact.
* `TauCeti.QuadraticMap.instCompactSpaceSpecialOrthogonalGroupRealCliffordForm`: the associated
  special orthogonal group is compact.
* `TauCeti.QuadraticMap.isClosed_range_specialOrthogonalToGeneralLinear_realCliffordForm`: the
  positive-definite real special-orthogonal carrier is closed in its general-linear ambient group.
-/

public section

open Matrix QuadraticMap

namespace TauCeti

universe u

namespace QuadraticMap

noncomputable section

section ClassicalDecEq

attribute [local instance] Classical.decEq

/-- The coordinate equivalence from real special-orthogonal matrices to standard
determinant-one sum-of-squares isometries is continuous. -/
theorem continuous_matrixSpecialOrthogonalEquivWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] :
    Continuous (matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι) := by
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
        (matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι A)) fun A =>
      (specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι A).symm

/-- The inverse coordinate equivalence from determinant-one sum-of-squares isometries to
real special-orthogonal matrices is continuous. -/
theorem continuous_matrixSpecialOrthogonalEquivWeightedSumSquaresOne_symm
    (ι : Type u) [Fintype ι] :
    Continuous (matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι).symm :=
  Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι).toEquiv)
    (continuous_matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι)

/-- The special orthogonal group of the standard real sum-of-squares form is compact. -/
instance instCompactSpaceRealSpecialOrthogonalGroupWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] :
    CompactSpace (specialOrthogonalGroup
      (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) := by
  exact (matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι).surjective.compactSpace
    (continuous_matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι)

/-- The special orthogonal group of the positive-definite real Clifford form is compact. -/
instance instCompactSpaceSpecialOrthogonalGroupRealCliffordForm (n : ℕ) :
  CompactSpace (specialOrthogonalGroup (realCliffordForm n 0)) := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one]
  exact instCompactSpaceRealSpecialOrthogonalGroupWeightedSumSquaresOne (Fin n)

end ClassicalDecEq

/-- Real special-orthogonal matrices and the determinant-one isometries of the standard
sum-of-squares form are isomorphic as topological groups, a matrix acting by its linear map. -/
def matrixSpecialOrthogonalContinuousMulEquivWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Matrix.specialOrthogonalGroup ι ℝ ≃ₜ*
      specialOrthogonalGroup (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) where
  toMulEquiv := matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι
  -- The continuity lemmas above are stated for the classical decidable-equality instance on `ι`;
  -- `convert` identifies it with the given one.
  continuous_toFun := (by convert continuous_matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι :
    Continuous (matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι))
  continuous_invFun := (by
    convert continuous_matrixSpecialOrthogonalEquivWeightedSumSquaresOne_symm ι :
    Continuous (matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι).symm)

/-- The topological group isomorphism applies the matrix-to-isometry equivalence. -/
@[simp]
theorem coe_matrixSpecialOrthogonalContinuousMulEquivWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    ⇑(matrixSpecialOrthogonalContinuousMulEquivWeightedSumSquaresOne ι) =
      matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι :=
  (rfl)

/-- The inverse topological group isomorphism applies the inverse equivalence. -/
@[simp]
theorem coe_matrixSpecialOrthogonalContinuousMulEquivWeightedSumSquaresOne_symm
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    ⇑(matrixSpecialOrthogonalContinuousMulEquivWeightedSumSquaresOne ι).symm =
      (matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι).symm :=
  (rfl)

/-- Real special-orthogonal matrices and the determinant-one isometries of the positive-definite
form `realCliffordForm n 0` are isomorphic as topological groups, a matrix acting by its linear
map. This is `matrixSpecialOrthogonalContinuousMulEquivWeightedSumSquaresOne` transported along
`realCliffordForm_zero_eq_weightedSumSquares_one`. -/
def matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm (n : ℕ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ ≃ₜ* specialOrthogonalGroup (realCliffordForm n 0) :=
  (realCliffordForm_zero_eq_weightedSumSquares_one n).symm ▸
    matrixSpecialOrthogonalContinuousMulEquivWeightedSumSquaresOne (Fin n)

/-- The topological group isomorphism with the `realCliffordForm n 0` special orthogonal group
acts by matrix-vector multiplication. -/
@[simp]
theorem matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm_apply (n : ℕ)
    (A : Matrix.specialOrthogonalGroup (Fin n) ℝ) (x : Fin n → ℝ) :
    ((matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm n A :
        specialOrthogonalGroup (realCliffordForm n 0)) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) x =
      Matrix.toLin' (A : Matrix (Fin n) (Fin n) ℝ) x := by
  -- Generalizing the target form lets the transport along
  -- `realCliffordForm_zero_eq_weightedSumSquares_one` be eliminated by `rfl`.
  have key : ∀ (Q : QuadraticForm ℝ (Fin n → ℝ)) (h : weightedSumSquares ℝ (1 : Fin n → ℝ) = Q),
      (((h ▸ matrixSpecialOrthogonalContinuousMulEquivWeightedSumSquaresOne (Fin n) :
        Matrix.specialOrthogonalGroup (Fin n) ℝ ≃ₜ* specialOrthogonalGroup Q) A :
          specialOrthogonalGroup Q) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) x =
        Matrix.toLin' (A : Matrix (Fin n) (Fin n) ℝ) x := by
    rintro _ rfl
    exact matrixSpecialOrthogonalEquivWeightedSumSquaresOne_apply (Fin n) A x
  exact key _ _

/-- The inverse of the topological group isomorphism with the `realCliffordForm n 0` special
orthogonal group recovers the matrix of an isometry. -/
@[simp]
theorem matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm_symm_coe (n : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm n 0)) :
    (((matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm n).symm g :
        Matrix.specialOrthogonalGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      LinearMap.toMatrix' (g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)).toLinearMap := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun x => ?_
  rw [← matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm_apply,
    ContinuousMulEquiv.apply_symm_apply, LinearEquiv.coe_coe]

/-- Membership in the positive-definite `realCliffordForm n 0` special-orthogonal carrier is matrix
special-orthogonal membership. -/
theorem mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff
    (n : ℕ) (U : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    U ∈ MonoidHom.range (specialOrthogonalToGeneralLinear (realCliffordForm n 0)) ↔
      (U : Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one]
  exact mem_range_specialOrthogonalToGeneralLinear_weightedSumSquares_one_iff (Fin n) U

/-- The real special-orthogonal carrier is closed in its general-linear ambient group. -/
theorem isClosed_range_specialOrthogonalToGeneralLinear_realCliffordForm (n : ℕ) :
    -- `realCliffordForm n 0` is indexed by `Fin (n + 0)`; retyping it over `Fin n` lets this
    -- statement use the canonical `Fin n` equality and matrix-topology instances.
    IsClosed (Set.range (specialOrthogonalToGeneralLinear
      (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0))) := by
  have hrange : Set.range (specialOrthogonalToGeneralLinear
      (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)) =
      {U : Matrix.GeneralLinearGroup (Fin n) ℝ |
        (U : Matrix (Fin n) (Fin n) ℝ) ∈
        Matrix.specialOrthogonalGroup (Fin n) ℝ} := by
    ext U
    rw [← MonoidHom.coe_range]
    exact mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff n U
  rw [hrange]
  exact (TauCeti.Matrix.isClosed_specialOrthogonalGroup (n := Fin n) (R := ℝ)).preimage
    (Units.continuous_val : Continuous (fun U : Matrix.GeneralLinearGroup (Fin n) ℝ =>
      (U : Matrix (Fin n) (Fin n) ℝ)))

end

end QuadraticMap

end TauCeti
