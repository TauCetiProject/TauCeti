/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
public import Mathlib.Topology.UniformSpace.Real
import TauCeti.Topology.Algebra.UnitaryGroup
public import TauCeti.Topology.Algebra.QuadraticForm.SpecialOrthogonal
public import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.WeightedSumSquares

/-!
# Compactness of positive-definite real special orthogonal groups

The standard real sum-of-squares form has a special orthogonal group which is the continuous image
of the compact real special orthogonal matrix group. This gives the construction for any finite
coordinate type. Specializing to the positive-definite form `realCliffordForm n 0` supplies the
quadratic-form model used as the target of the compact real Spin projection with its canonical
compact-space instance. The file also identifies that concrete carrier with the matrix special
orthogonal group in canonical coordinates.

The transfer follows the existing coordinate embedding into the general linear group. An
orthogonal matrix defines a form-preserving linear equivalence, and its inverse matrix is its
transpose, so the resulting map is continuous for the induced topology.

## Main results

* `TauCeti.QuadraticMap.instCompactSpaceRealSpecialOrthogonalGroupWeightedSumSquaresOne`: the
  special orthogonal group of the standard sum-of-squares form on any finite coordinate type is
  compact.
* `TauCeti.QuadraticMap.mem_range_specialOrthogonalToGeneralLinear_weightedSumSquares_one_iff`:
  membership in its general-linear carrier is matrix special-orthogonal membership.
* `TauCeti.QuadraticMap.mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff`:
  membership in the positive-definite Clifford-form carrier is matrix special-orthogonal
  membership.
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

/-- Membership in the positive-definite `realCliffordForm n 0` special-orthogonal carrier is matrix
special-orthogonal membership. -/
theorem mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff
    (n : ℕ) (U : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    U ∈ MonoidHom.range (specialOrthogonalToGeneralLinear (realCliffordForm n 0)) ↔
      (U : Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one]
  exact mem_range_specialOrthogonalToGeneralLinear_weightedSumSquares_one_iff (Fin n) U

private theorem continuous_matrixSpecialOrthogonalToWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Continuous (matrixSpecialOrthogonalToWeightedSumSquaresOne ι) := by
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
        (matrixSpecialOrthogonalToWeightedSumSquaresOne ι A)) fun A =>
      (specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquaresOne ι A).symm

/-- The special orthogonal group of the standard real sum-of-squares form is compact. -/
instance instCompactSpaceRealSpecialOrthogonalGroupWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    CompactSpace (specialOrthogonalGroup
      (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) := by
  exact (matrixSpecialOrthogonalToWeightedSumSquaresOne_surjective ι).compactSpace
    (continuous_matrixSpecialOrthogonalToWeightedSumSquaresOne ι)

/-- The special orthogonal group of the positive-definite real Clifford form is compact. -/
instance instCompactSpaceSpecialOrthogonalGroupRealCliffordForm (n : ℕ) :
  CompactSpace (specialOrthogonalGroup (realCliffordForm n 0)) := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one]
  exact instCompactSpaceRealSpecialOrthogonalGroupWeightedSumSquaresOne (Fin n)

/-- The real special-orthogonal carrier is closed in its general-linear ambient group. -/
theorem isClosed_range_specialOrthogonalToGeneralLinear_realCliffordForm (n : ℕ) :
    IsClosed (Set.range (specialOrthogonalToGeneralLinear
      (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0))) := by
  have hc : IsCompact (Set.univ : Set (specialOrthogonalGroup
      (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0))) := isCompact_univ
  simpa only [Set.image_univ] using
    (hc.image (isEmbedding_specialOrthogonalToGeneralLinear
      (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)).continuous).isClosed

end

end QuadraticMap

end TauCeti
