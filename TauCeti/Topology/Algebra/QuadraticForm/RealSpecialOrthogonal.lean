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
  exact (Matrix.isClosed_specialOrthogonalGroup (n := Fin n) (R := ℝ)).preimage
    (Units.continuous_val : Continuous (fun U : Matrix.GeneralLinearGroup (Fin n) ℝ =>
      (U : Matrix (Fin n) (Fin n) ℝ)))

end

end QuadraticMap

end TauCeti
