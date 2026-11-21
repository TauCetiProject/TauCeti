/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Adjoint.Units.Basic
public import TauCeti.Geometry.Lie.Exponential.Matrix.SkewAdjoint
public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Standard
import TauCeti.Topology.Algebra.QuadraticForm.SpecialOrthogonal

/-!
# Lie algebras of special orthogonal groups in matrix coordinates

This file transports the matrix-exponential characterization of skew-adjoint Lie algebras to
general-linear range carriers of special orthogonal groups. The main theorems treat any
nondegenerate quadratic form `Q` on `n → 𝕜` over a finite-dimensional normed commutative
`ℝ`-algebra `𝕜` (such as `ℝ` or `ℂ`), and specialize to the positive-definite `realCliffordForm n 0`
carrier via `LieAlgebra.Orthogonal.so (Fin n) ℝ`.

## Main results

* `TauCeti.Lie.forall_lieExp_mem_range_specialOrthogonalToGeneralLinear_iff` and
  `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_specialOrthogonal_iff`
  identify the real exponential lines and closed-subgroup Lie algebra of
  `MonoidHom.range Q.specialOrthogonalToGeneralLinear` with
  `skewAdjointMatricesLieSubalgebra (toMatrix' Q.polarBilin)` for any nondegenerate `Q`.
* `TauCeti.Lie.forall_lieExp_mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff_mem_so`
  and `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_realCliffordForm_lieSubalgebra_iff_mem_so`
  specialize these characterizations to `realCliffordForm n 0` and
  `LieAlgebra.Orthogonal.so (Fin n) ℝ`.
-/

public section

open Manifold NormedSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Matrix.linftyOpTopologicalSpace

section General

variable {n : Type*} [Fintype n] [DecidableEq n]
  {𝕜 : Type*} [NormedCommRing 𝕜] [NormedAlgebra ℝ 𝕜] [FiniteDimensional ℝ 𝕜]

attribute [local instance] NormedAlgebra.toNormedSpace

/-- In canonical matrix units coordinates, `A` generates a real one-parameter Lie exponential curve
in the coordinate range of `SO(Q)` for a nondegenerate quadratic form `Q` if and only if
`A ∈ skewAdjointMatricesLieSubalgebra (toMatrix' Q.polarBilin)`. -/
@[simp↓]
theorem forall_lieExp_mem_range_specialOrthogonalToGeneralLinear_iff
    (Q : QuadraticForm 𝕜 (n → 𝕜)) (hQ : Q.Nondegenerate) (A : Matrix n n 𝕜) :
    (∀ t : ℝ, lieExp ((unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm (t • A)) ∈
      MonoidHom.range Q.specialOrthogonalToGeneralLinear) ↔
      A ∈ skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin) := by
  rw [forall_lieExp_unitsLieAlgebraLieEquiv_symm_smul_mem_iff,
    Q.forall_expUnit_smul_mem_range_specialOrthogonalToGeneralLinear_iff hQ]

/-- In canonical matrix units coordinates, the real Lie subalgebra of the closed `SO(Q)` range
carrier of a nondegenerate quadratic form `Q` is
`skewAdjointMatricesLieSubalgebra (toMatrix' Q.polarBilin)`. -/
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_specialOrthogonal_iff
    (Q : QuadraticForm 𝕜 (n → 𝕜)) (hQ : Q.Nondegenerate) (A : Matrix n n 𝕜) :
    (unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm A ∈
        lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
          (MonoidHom.range Q.specialOrthogonalToGeneralLinear) ↔
      A ∈ skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin) := by
  have hclosed : IsClosed
      ((MonoidHom.range Q.specialOrthogonalToGeneralLinear : Subgroup (Matrix n n 𝕜)ˣ) :
        Set (Matrix n n 𝕜)ˣ) := by
    rw [MonoidHom.coe_range]
    exact Q.isClosed_range_specialOrthogonalToGeneralLinear
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff hclosed,
    Q.forall_expUnit_smul_mem_range_specialOrthogonalToGeneralLinear_iff hQ]

end General

private theorem skewAdjointMatricesLieSubalgebra_toMatrix'_polarBilin_realCliffordForm (n : ℕ) :
    skewAdjointMatricesLieSubalgebra
        (LinearMap.BilinForm.toMatrix' (realCliffordFormZero n).polarBilin) =
      LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  have hgram : LinearMap.BilinForm.toMatrix' (realCliffordFormZero n).polarBilin =
        unitOfInvertible (2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    dsimp only [realCliffordFormZero]
    rw [realCliffordForm_zero_eq_weightedSumSquares_one,
      TauCeti.QuadraticForm.polarBilin_weightedSumSquares_one, map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℝ, Units.smul_def, val_unitOfInvertible, Nat.cast_ofNat]
    exact congrArg ((2 : ℝ) • ·) (LinearMap.toMatrix'_toLinearMap₂' (1 : Matrix (Fin n) (Fin n) ℝ))
  ext A
  rw [hgram, LieAlgebra.Orthogonal.so]
  exact mem_skewAdjointMatricesLieSubalgebra_unit_smul (unitOfInvertible (2 : ℝ)) 1 A

/-- In the canonical matrix coordinates of the general linear Lie algebra, an element generates a
one-parameter subgroup in the range of the positive-definite `realCliffordForm n 0`
special-orthogonal carrier exactly when it is skew-symmetric. -/
-- Normalize the whole exponential-line predicate before range membership expands.
@[simp↓]
theorem forall_lieExp_mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff_mem_so
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ t : ℝ, lieExp ((unitsLieAlgebraLieEquiv
        (R := Matrix (Fin n) (Fin n) ℝ)).symm (t • A)) ∈
      MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (realCliffordFormZero n))) ↔
      A ∈ LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  rw [← skewAdjointMatricesLieSubalgebra_toMatrix'_polarBilin_realCliffordForm n]
  exact forall_lieExp_mem_range_specialOrthogonalToGeneralLinear_iff
    (realCliffordFormZero n) (nondegenerate_realCliffordForm n 0) A

/-- A matrix belongs to the real orthogonal Lie algebra exactly when its inverse image under the
canonical units Lie equivalence belongs to the Lie subalgebra of the positive-definite
`realCliffordForm n 0` special-orthogonal carrier. -/
-- Normalize membership before the Lie equivalence simplifies to its linear equivalence.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_realCliffordForm_lieSubalgebra_iff_mem_so
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (unitsLieAlgebraLieEquiv (R := Matrix (Fin n) (Fin n) ℝ)).symm A ∈
        lieSubalgebraOfSubgroup
          (MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
            (realCliffordFormZero n)) :
              Subgroup (Matrix (Fin n) (Fin n) ℝ)ˣ) ↔
      A ∈ LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  rw [← skewAdjointMatricesLieSubalgebra_toMatrix'_polarBilin_realCliffordForm n]
  exact unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_specialOrthogonal_iff
    (realCliffordFormZero n) (nondegenerate_realCliffordForm n 0) A

end TauCeti.Lie
