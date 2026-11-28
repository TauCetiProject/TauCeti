/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.SkewAdjoint
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Adjoint.Units.Basic
public import TauCeti.Geometry.Lie.Exponential.Matrix.SkewAdjoint
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
import TauCeti.Algebra.Lie.BaseChange.Basic
import TauCeti.Algebra.Lie.Subalgebra.RestrictScalars
import TauCeti.LinearAlgebra.QuadraticForm.Standard
import TauCeti.Topology.Algebra.QuadraticForm.SpecialOrthogonal

/-!
# Lie algebras of special orthogonal groups in matrix coordinates

This file transports the matrix-exponential characterization of skew-adjoint Lie algebras to
general-linear range carriers of special orthogonal groups. The main theorems treat any
nondegenerate quadratic form `Q` on `n → 𝕜` over a finite-dimensional normed commutative
`ℝ`-algebra `𝕜` (such as `ℝ` or `ℂ`), and specialize to the positive-definite `realCliffordForm n 0`
carrier via `LieAlgebra.Orthogonal.so (Fin n) ℝ`. Over `ℂ`, Cartan's closed-subgroup theorem
equips the range carrier of `SO(Q)` inside `(Matrix (Fin n) (Fin n) ℂ)ˣ` with a real Lie-group
structure, and when `Q` is nondegenerate its real Lie algebra is identified with
`RestrictScalars ℝ ℂ (skewAdjointMatricesLieSubalgebra (toMatrix' Q.polarBilin))` and
`RestrictScalars ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)`.

## Main definitions and results

* `TauCeti.Lie.forall_lieExp_mem_range_specialOrthogonalToGeneralLinear_iff` and
  `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_specialOrthogonal_iff`
  identify the real exponential lines and closed-subgroup Lie algebra of
  `MonoidHom.range Q.specialOrthogonalToGeneralLinear` with
  `skewAdjointMatricesLieSubalgebra (toMatrix' Q.polarBilin)` for any nondegenerate `Q`.
* `TauCeti.Lie.forall_lieExp_mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff_mem_so`
  and `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_realCliffordForm_lieSubalgebra_iff_mem_so`
  specialize these characterizations to `realCliffordForm n 0` and
  `LieAlgebra.Orthogonal.so (Fin n) ℝ`.
* `TauCeti.Lie.complexSpecialOrthogonalEmbeddedLieSubgroupData`: closed-subgroup real Lie structure
  on the coordinate range of `SO(Q)` in `(Matrix (Fin n) (Fin n) ℂ)ˣ`.
* `TauCeti.Lie.complexSpecialOrthogonalLieEquivSkewAdjointMatrices` and
  `TauCeti.Lie.complexSpecialOrthogonalLieEquivSkewAdjoint`: its real Lie algebra in polar
  skew-adjoint matrix and endomorphism coordinates when `Q` is nondegenerate.
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

section Complex

attribute [local instance] NormedAlgebra.toNormedSpace

variable {n : ℕ} {Q : QuadraticForm ℂ (Fin n → ℂ)}

local notation "SpecialOrthogonalUnitsRange" =>
  MonoidHom.range Q.specialOrthogonalToGeneralLinear

local notation "SpecialOrthogonalLieModel" =>
  LieSubalgebra.toSubmodule (lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ)) SpecialOrthogonalUnitsRange)

/-- The closed-subgroup real Lie structure on the coordinate range of `SO(Q)` inside
`(Matrix (Fin n) (Fin n) ℂ)ˣ`, modeled on its ambient one-parameter-subgroup Lie algebra. -/
def complexSpecialOrthogonalEmbeddedLieSubgroupData (Q : QuadraticForm ℂ (Fin n → ℂ)) :
    EmbeddedLieSubgroupData
      𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ)
      (MonoidHom.range Q.specialOrthogonalToGeneralLinear)
      (LieSubalgebra.toSubmodule (lieSubalgebraOfSubgroup
        (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ))
        (MonoidHom.range Q.specialOrthogonalToGeneralLinear))) :=
  EmbeddedLieSubgroupData.ofIsClosed (by
    rw [MonoidHom.coe_range]
    exact Q.isClosed_range_specialOrthogonalToGeneralLinear)

/-- The charted-space structure on the complex `SO(Q)` range carrier selected by Cartan's
theorem. -/
instance complexSpecialOrthogonalUnitsRangeChartedSpace :
    ChartedSpace SpecialOrthogonalLieModel SpecialOrthogonalUnitsRange :=
  (complexSpecialOrthogonalEmbeddedLieSubgroupData Q).chartedSpace

/-- The real Lie-group structure on the complex `SO(Q)` range carrier selected by Cartan's
theorem. -/
instance complexSpecialOrthogonalUnitsRangeLieGroup :
    LieGroup 𝓘(ℝ, SpecialOrthogonalLieModel) ∞ SpecialOrthogonalUnitsRange :=
  (complexSpecialOrthogonalEmbeddedLieSubgroupData Q).lieGroup

private def complexSpecialOrthogonalAmbientCoordinateLieEquiv (hQ : Q.Nondegenerate) :
    lieSubalgebraOfSubgroup
        (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ)) SpecialOrthogonalUnitsRange ≃ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ
        (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin)) :=
  (unitsLieAlgebraLieEquiv
    (R := Matrix (Fin n) (Fin n) ℂ)).ofSubalgebrasRestrictScalars _
      (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin)) <| by
        ext A
        simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule,
          LieSubalgebra.mem_range_restrictScalarsIncl]
        exact
          unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_specialOrthogonal_iff
            Q hQ A

/-- The real Lie algebra of the complex `SO(Q)` range carrier in polar skew-adjoint matrix
coordinates. -/
def complexSpecialOrthogonalLieEquivSkewAdjointMatrices [Fact Q.Nondegenerate] :
    LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel) SpecialOrthogonalUnitsRange ≃ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ
        (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin)) :=
  (complexSpecialOrthogonalEmbeddedLieSubgroupData Q)
    |>.lieEquivLieSubalgebraOfSubgroup.trans
      (complexSpecialOrthogonalAmbientCoordinateLieEquiv (Fact.out : Q.Nondegenerate))

/-- Matrix units coordinates of the differentiated `SO(Q)` range inclusion normalize to the polar
skew-adjoint matrix coordinates. -/
@[simp↓ high]
theorem
 unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_complexSpecialOrthogonalLieEquivSkewAdjointMatrices
    [Fact Q.Nondegenerate]
    (X : LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel) SpecialOrthogonalUnitsRange) :
    unitsLieAlgebraLieEquiv
        ((complexSpecialOrthogonalEmbeddedLieSubgroupData Q).lieMapSubtypeVal X) =
      ((RestrictScalars.addEquiv ℝ ℂ
          (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
          (complexSpecialOrthogonalLieEquivSkewAdjointMatrices (Q := Q) X)) :
        Matrix (Fin n) (Fin n) ℂ) := by
  have h := congrArg
    (fun Y : LeftInvariantDerivation 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ)ˣ ↦
      unitsLieAlgebraLieEquiv Y)
    ((complexSpecialOrthogonalEmbeddedLieSubgroupData Q).lieEquivLieSubalgebraOfSubgroup_apply X)
  simpa only [complexSpecialOrthogonalLieEquivSkewAdjointMatrices, LieEquiv.trans_apply,
    complexSpecialOrthogonalAmbientCoordinateLieEquiv,
    LieEquiv.coe_ofSubalgebrasRestrictScalars_apply] using h.symm

/-- The real Lie algebra of the complex `SO(Q)` range carrier in basis-free polar skew-adjoint
endomorphism coordinates. -/
def complexSpecialOrthogonalLieEquivSkewAdjoint [Fact Q.Nondegenerate] :
    LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel) SpecialOrthogonalUnitsRange ≃ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin) :=
  (complexSpecialOrthogonalLieEquivSkewAdjointMatrices (Q := Q)).trans <|
    (TauCeti.skewAdjointLieEquivOfBasis (Pi.basisFun ℂ (Fin n)) Q.polarBilin
      (DFunLike.congr_fun LinearMap.BilinForm.toMatrix_basisFun Q.polarBilin)).restrictScalars ℝ

/-- The polar skew-adjoint endomorphism coordinate of `X` is its polar skew-adjoint matrix
coordinate transported by the standard-basis skew-adjoint equivalence. -/
theorem coe_complexSpecialOrthogonalLieEquivSkewAdjoint [Fact Q.Nondegenerate]
    (X : LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel) SpecialOrthogonalUnitsRange) :
    RestrictScalars.addEquiv ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)
        (complexSpecialOrthogonalLieEquivSkewAdjoint (Q := Q) X) =
      TauCeti.skewAdjointLieEquivOfBasis (Pi.basisFun ℂ (Fin n)) Q.polarBilin
        (DFunLike.congr_fun LinearMap.BilinForm.toMatrix_basisFun Q.polarBilin)
        (RestrictScalars.addEquiv ℝ ℂ
          (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
          (complexSpecialOrthogonalLieEquivSkewAdjointMatrices (Q := Q) X)) := by
  simp only [complexSpecialOrthogonalLieEquivSkewAdjoint, LieEquiv.trans_apply,
    LieEquiv.restrictScalars_apply, AddEquiv.apply_symm_apply]

/-- Evaluating the polar skew-adjoint endomorphism coordinate of `X` on a vector `v` agrees with
multiplying `v` by its polar skew-adjoint matrix coordinate. -/
@[simp]
theorem coe_complexSpecialOrthogonalLieEquivSkewAdjoint_apply_apply [Fact Q.Nondegenerate]
    (X : LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel) SpecialOrthogonalUnitsRange)
    (v : Fin n → ℂ) :
    (((RestrictScalars.addEquiv ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)
        (complexSpecialOrthogonalLieEquivSkewAdjoint (Q := Q) X)) :
          Module.End ℂ (Fin n → ℂ)) v) =
      ((RestrictScalars.addEquiv ℝ ℂ
          (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
          (complexSpecialOrthogonalLieEquivSkewAdjointMatrices (Q := Q) X)) :
        Matrix (Fin n) (Fin n) ℂ) *ᵥ v := by
  have htoLin (A : Matrix (Fin n) (Fin n) ℂ) :
      Matrix.toLinAlgEquiv (Pi.basisFun ℂ (Fin n)) A = Matrix.toLin' A := by
    change Matrix.toLin (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) A = Matrix.toLin' A
    rw [Matrix.toLin_eq_toLin']
  rw [coe_complexSpecialOrthogonalLieEquivSkewAdjoint]
  simp only [TauCeti.coe_skewAdjointLieEquivOfBasis_apply, htoLin, Matrix.toLin'_apply]

end Complex

end TauCeti.Lie
