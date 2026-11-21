/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Basic
public import TauCeti.Algebra.Lie.SkewAdjoint
public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.ContinuousFunctor
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Complex.Basic
public import TauCeti.Geometry.Lie.Subgroup.SpecialOrthogonal
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.UnitsRange

/-!
# Smooth complex Spin-to-SO projection and its coordinate differentials

For any quadratic form `Q` on `Fin n → ℂ`, the coordinate range of `SO(Q)` inside
`(Matrix (Fin n) (Fin n) ℂ)ˣ` is a closed subgroup, so Cartan's theorem equips it with a real
Lie-group structure modeled on its ambient one-parameter-subgroup Lie algebra. When `Q` is
nondegenerate, canonical matrix units coordinates identify that real Lie algebra with
`RestrictScalars ℝ ℂ (skewAdjointMatricesLieSubalgebra (toMatrix' Q.polarBilin))`, and standard
basis transport identifies it further with
`RestrictScalars ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)`.

Automatic smoothness upgrades the continuous range-carrier Spin projection
`CliffordAlgebra.spinToSpecialOrthogonalUnitsRange Q` to a smooth homomorphism between the closed
complex `Spin(Q)` and `SO(Q)` unit ranges. Applying `lieMap` and conjugating by the source and
target coordinate equivalences produces the real Lie homomorphisms
`complexSpinToSpecialOrthogonalCoordinateLieHom` and
`complexSpinToSpecialOrthogonalPolarCoordinateLieHom` whose commutator action and `ℂ`-linearity are
established in `TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Complex.Differential`.

## Main definitions

* `TauCeti.CliffordAlgebra.complexSpecialOrthogonalEmbeddedLieSubgroupData`: closed-subgroup real
  Lie structure on the coordinate range of `SO(Q)` in `(Matrix (Fin n) (Fin n) ℂ)ˣ`.
* `TauCeti.CliffordAlgebra.complexSpecialOrthogonalLieEquivSkewAdjointMatrices` and
  `TauCeti.CliffordAlgebra.complexSpecialOrthogonalLieEquivSkewAdjoint`: its real Lie algebra in
  polar skew-adjoint matrix and endomorphism coordinates when `Q` is nondegenerate.
* `TauCeti.CliffordAlgebra.complexSpinToSpecialOrthogonalSmoothRange`: the smooth complex
  `Spin(Q) → SO(Q)` range-carrier projection.
* `TauCeti.CliffordAlgebra.complexSpinToSpecialOrthogonalCoordinateLieHom` and
  `TauCeti.CliffordAlgebra.complexSpinToSpecialOrthogonalPolarCoordinateLieHom`: the differential in
  quadratic-Clifford and polar skew-adjoint coordinates.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Sections 2 and 5.
* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras* (2008), Chapter 3.
-/

public section

open Manifold
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] NormedAlgebra.toNormedSpace
attribute [local instance] Matrix.linftyOpTopologicalSpace

variable {n : ℕ} {Q : QuadraticForm ℂ (Fin n → ℂ)}

local notation "SpinUnitsRange" => MonoidHom.range (spinGroup.toUnits (Q := Q))

local notation "SpecialOrthogonalUnitsRange" =>
  MonoidHom.range Q.specialOrthogonalToGeneralLinear

local notation "SpinLieModel" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra Q)) SpinUnitsRange)

local notation "SpecialOrthogonalLieModel" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ)) SpecialOrthogonalUnitsRange)

/-- The closed-subgroup real Lie structure on the coordinate range of `SO(Q)` inside
`(Matrix (Fin n) (Fin n) ℂ)ˣ`, modeled on its ambient one-parameter-subgroup Lie algebra. -/
def complexSpecialOrthogonalEmbeddedLieSubgroupData (Q : QuadraticForm ℂ (Fin n → ℂ)) :
    TauCeti.Lie.EmbeddedLieSubgroupData
      𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ)
      (MonoidHom.range Q.specialOrthogonalToGeneralLinear)
      (LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
        (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ))
        (MonoidHom.range Q.specialOrthogonalToGeneralLinear))) :=
  TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed (by
    rw [MonoidHom.coe_range]
    exact Q.isClosed_range_specialOrthogonalToGeneralLinear)

/-- The canonical real model of the complex `SO(Q)` range carrier is finite-dimensional. -/
instance complexSpecialOrthogonalLieModelFiniteDimensional :
    FiniteDimensional ℝ SpecialOrthogonalLieModel := by
  let _ : FiniteDimensional ℝ
      (LeftInvariantDerivation 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ)ˣ) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  exact FiniteDimensional.finiteDimensional_submodule _

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

private theorem map_complexSpecialOrthogonal_lieSubalgebra (hQ : Q.Nondegenerate) :
    Submodule.map
        ((TauCeti.Lie.unitsLieAlgebraLieEquiv
          (R := Matrix (Fin n) (Fin n) ℂ)).toLinearEquiv : _ →ₗ[ℝ] _)
        (TauCeti.Lie.lieSubalgebraOfSubgroup
          (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ)) SpecialOrthogonalUnitsRange).toSubmodule =
      (skewAdjointMatricesLieSubalgebra
        (LinearMap.BilinForm.toMatrix' Q.polarBilin)).toSubmodule.restrictScalars ℝ := by
  open TauCeti.Lie in
  ext A
  simp only [Submodule.mem_map_equiv, Submodule.restrictScalars_mem]
  exact unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_specialOrthogonal_iff
    Q hQ A

private def complexSpecialOrthogonalAmbientCoordinateLieEquiv (hQ : Q.Nondegenerate) :
    TauCeti.Lie.lieSubalgebraOfSubgroup
        (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ)) SpecialOrthogonalUnitsRange ≃ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ
        (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin)) :=
  { LinearEquiv.ofSubmodules
      (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix (Fin n) (Fin n) ℂ)).toLinearEquiv
      _
      ((skewAdjointMatricesLieSubalgebra
        (LinearMap.BilinForm.toMatrix' Q.polarBilin)).toSubmodule.restrictScalars ℝ)
      (map_complexSpecialOrthogonal_lieSubalgebra hQ) with
    map_lie' := fun {x y} ↦ Subtype.ext
      ((TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix (Fin n) (Fin n) ℂ)).map_lie x y) }

private theorem coe_complexSpecialOrthogonalAmbientCoordinateLieEquiv_apply
    (hQ : Q.Nondegenerate)
    (x : TauCeti.Lie.lieSubalgebraOfSubgroup
      (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ)) SpecialOrthogonalUnitsRange) :
    (RestrictScalars.addEquiv ℝ ℂ
      (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
      (complexSpecialOrthogonalAmbientCoordinateLieEquiv hQ x) : Matrix (Fin n) (Fin n) ℂ) =
      TauCeti.Lie.unitsLieAlgebraLieEquiv x := by
  -- The `LieEquiv` extends `LinearEquiv.ofSubmodules` on the same forward map, and
  -- `RestrictScalars.addEquiv` is the identity on the underlying submodule carrier.
  exact LinearEquiv.ofSubmodules_apply
    (e := (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix (Fin n) (Fin n) ℂ)).toLinearEquiv)
    (p := (TauCeti.Lie.lieSubalgebraOfSubgroup
      (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ)) SpecialOrthogonalUnitsRange).toSubmodule)
    (q := (skewAdjointMatricesLieSubalgebra
      (LinearMap.BilinForm.toMatrix' Q.polarBilin)).toSubmodule.restrictScalars ℝ)
    (map_complexSpecialOrthogonal_lieSubalgebra hQ) x

/-- The real Lie algebra of the complex `SO(Q)` range carrier in polar skew-adjoint matrix
coordinates. -/
def complexSpecialOrthogonalLieEquivSkewAdjointMatrices [Fact Q.Nondegenerate] :
    LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel) SpecialOrthogonalUnitsRange ≃ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ
        (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin)) :=
  (complexSpecialOrthogonalEmbeddedLieSubgroupData Q)
    |>.lieEquivLieSubalgebraOfSubgroup.trans
      (complexSpecialOrthogonalAmbientCoordinateLieEquiv (Fact.out : Q.Nondegenerate))

/-- In ambient matrix coordinates, `complexSpecialOrthogonalLieEquivSkewAdjointMatrices` is the
units Lie equivalence applied after differentiating the subgroup inclusion. -/
theorem coe_complexSpecialOrthogonalLieEquivSkewAdjointMatrices_apply [Fact Q.Nondegenerate]
    (X : LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel) SpecialOrthogonalUnitsRange) :
    ((RestrictScalars.addEquiv ℝ ℂ
        (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
        (complexSpecialOrthogonalLieEquivSkewAdjointMatrices (Q := Q) X)) :
      Matrix (Fin n) (Fin n) ℂ) =
      TauCeti.Lie.unitsLieAlgebraLieEquiv
        ((complexSpecialOrthogonalEmbeddedLieSubgroupData Q).lieMapSubtypeVal X) := by
  have h := congrArg
    (fun Y : LeftInvariantDerivation 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ)ˣ ↦
      TauCeti.Lie.unitsLieAlgebraLieEquiv Y)
    ((complexSpecialOrthogonalEmbeddedLieSubgroupData Q).lieEquivLieSubalgebraOfSubgroup_apply X)
  simpa only [complexSpecialOrthogonalLieEquivSkewAdjointMatrices, LieEquiv.trans_apply,
    coe_complexSpecialOrthogonalAmbientCoordinateLieEquiv_apply] using h

/-- Matrix units coordinates of the differentiated `SO(Q)` range inclusion normalize to the polar
skew-adjoint matrix coordinates. -/
@[simp↓ high]
theorem
 unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_complexSpecialOrthogonalLieEquivSkewAdjointMatrices
    [Fact Q.Nondegenerate]
    (X : LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel) SpecialOrthogonalUnitsRange) :
    TauCeti.Lie.unitsLieAlgebraLieEquiv
        ((complexSpecialOrthogonalEmbeddedLieSubgroupData Q).lieMapSubtypeVal X) =
      ((RestrictScalars.addEquiv ℝ ℂ
          (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
          (complexSpecialOrthogonalLieEquivSkewAdjointMatrices (Q := Q) X)) :
        Matrix (Fin n) (Fin n) ℂ) :=
  (coe_complexSpecialOrthogonalLieEquivSkewAdjointMatrices_apply (Q := Q) X).symm

/-- The real Lie algebra of the complex `SO(Q)` range carrier in basis-free polar skew-adjoint
endomorphism coordinates. -/
def complexSpecialOrthogonalLieEquivSkewAdjoint [Fact Q.Nondegenerate] :
    LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel) SpecialOrthogonalUnitsRange ≃ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin) :=
  (complexSpecialOrthogonalLieEquivSkewAdjointMatrices (Q := Q)).trans <|
    (TauCeti.skewAdjointLieEquivOfBasis (Pi.basisFun ℂ (Fin n)) Q.polarBilin
      (DFunLike.congr_fun LinearMap.BilinForm.toMatrix_basisFun Q.polarBilin)).restrictScalars ℝ

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
  have hrepr : ⇑((Pi.basisFun ℂ (Fin n)).repr v) = v := funext fun j ↦ by simp
  simp only [complexSpecialOrthogonalLieEquivSkewAdjoint, LieEquiv.trans_apply,
    LieEquiv.restrictScalars_apply, AddEquiv.apply_symm_apply,
    TauCeti.coe_skewAdjointLieEquivOfBasis_apply, Matrix.toLinAlgEquiv_apply, hrepr]
  ext i
  simp [Pi.basisFun_apply, Pi.single_apply]

/-- The continuous Spin-to-SO range projection over `ℂ`, upgraded to a smooth homomorphism of real
Lie groups by automatic smoothness. -/
def complexSpinToSpecialOrthogonalSmoothRange [Fact Q.Nondegenerate] :
    ContMDiffMonoidMorphism 𝓘(ℝ, SpinLieModel) 𝓘(ℝ, SpecialOrthogonalLieModel) ∞
      SpinUnitsRange SpecialOrthogonalUnitsRange :=
  ContinuousMonoidHom.toContMDiffMonoidMorphism
    𝓘(ℝ, SpinLieModel) 𝓘(ℝ, SpecialOrthogonalLieModel)
    (spinToSpecialOrthogonalUnitsRange Q)

/-- Evaluating the smooth complex Spin-to-SO range projection agrees with the continuous
range-carrier projection. -/
@[simp]
theorem complexSpinToSpecialOrthogonalSmoothRange_apply [Fact Q.Nondegenerate]
    (x : SpinUnitsRange) :
    complexSpinToSpecialOrthogonalSmoothRange (Q := Q) x =
      spinToSpecialOrthogonalUnitsRange Q x :=
  congrFun (ContinuousMonoidHom.coe_toContMDiffMonoidMorphism
    (I := 𝓘(ℝ, SpinLieModel)) (I' := 𝓘(ℝ, SpecialOrthogonalLieModel)) _) x

/-- On the canonical unit representative of `g : spinGroup Q`, the smooth complex range projection
computes `spinToSpecialOrthogonal Q g` in `GL(n, ℂ)`. -/
theorem complexSpinToSpecialOrthogonalSmoothRange_toUnits [Fact Q.Nondegenerate]
    (g : spinGroup Q) :
    complexSpinToSpecialOrthogonalSmoothRange (Q := Q) ⟨spinGroup.toUnits g, ⟨g, rfl⟩⟩ =
      Q.specialOrthogonalContinuousMulEquivRange (spinToSpecialOrthogonal Q g) := by
  rw [complexSpinToSpecialOrthogonalSmoothRange_apply,
    spinToSpecialOrthogonalUnitsRange_apply_toUnits]

/-- The real differential of the complex `Spin(Q) → SO(Q)` projection in quadratic-Clifford source
coordinates and polar skew-adjoint matrix target coordinates. -/
def complexSpinToSpecialOrthogonalCoordinateLieHom [Fact Q.Nondegenerate] :
    RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q) →ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ
        (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin)) :=
  (complexSpecialOrthogonalLieEquivSkewAdjointMatrices (Q := Q)).toLieHom.comp
    ((lieMap (complexSpinToSpecialOrthogonalSmoothRange (Q := Q))).comp
      (complexSpinLieEquivQuadratic (Q := Q)).symm.toLieHom)

/-- Evaluating `complexSpinToSpecialOrthogonalCoordinateLieHom` conjugates the abstract Lie map by
the source and matrix target coordinate equivalences. -/
@[simp]
theorem complexSpinToSpecialOrthogonalCoordinateLieHom_apply [Fact Q.Nondegenerate]
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) :
    complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q) x =
      complexSpecialOrthogonalLieEquivSkewAdjointMatrices (Q := Q)
        (lieMap (complexSpinToSpecialOrthogonalSmoothRange (Q := Q))
          ((complexSpinLieEquivQuadratic (Q := Q)).symm x)) := by
  simp only [complexSpinToSpecialOrthogonalCoordinateLieHom, LieHom.comp_apply,
    LieEquiv.coe_toLieHom]

/-- The real differential of the complex `Spin(Q) → SO(Q)` projection in quadratic-Clifford source
coordinates and basis-free polar skew-adjoint endomorphism target coordinates. -/
def complexSpinToSpecialOrthogonalPolarCoordinateLieHom [Fact Q.Nondegenerate] :
    RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q) →ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin) :=
  (complexSpecialOrthogonalLieEquivSkewAdjoint (Q := Q)).toLieHom.comp
    ((lieMap (complexSpinToSpecialOrthogonalSmoothRange (Q := Q))).comp
      (complexSpinLieEquivQuadratic (Q := Q)).symm.toLieHom)

/-- Evaluating `complexSpinToSpecialOrthogonalPolarCoordinateLieHom` conjugates the abstract Lie map
by the source and polar endomorphism target coordinate equivalences. -/
@[simp]
theorem complexSpinToSpecialOrthogonalPolarCoordinateLieHom_apply [Fact Q.Nondegenerate]
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) :
    complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q) x =
      complexSpecialOrthogonalLieEquivSkewAdjoint (Q := Q)
        (lieMap (complexSpinToSpecialOrthogonalSmoothRange (Q := Q))
          ((complexSpinLieEquivQuadratic (Q := Q)).symm x)) := by
  simp only [complexSpinToSpecialOrthogonalPolarCoordinateLieHom, LieHom.comp_apply,
    LieEquiv.coe_toLieHom]

/-- Evaluating the polar endomorphism differential on a vector `v` agrees with multiplying `v` by
the matrix coordinate differential. -/
theorem coe_complexSpinToSpecialOrthogonalPolarCoordinateLieHom_apply_apply
    [Fact Q.Nondegenerate]
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) (v : Fin n → ℂ) :
    (((RestrictScalars.addEquiv ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)
        (complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q) x)) :
          Module.End ℂ (Fin n → ℂ)) v) =
      ((RestrictScalars.addEquiv ℝ ℂ
          (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
          (complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q) x)) :
        Matrix (Fin n) (Fin n) ℂ) *ᵥ v := by
  simp only [complexSpinToSpecialOrthogonalPolarCoordinateLieHom_apply,
    complexSpinToSpecialOrthogonalCoordinateLieHom_apply,
    coe_complexSpecialOrthogonalLieEquivSkewAdjoint_apply_apply]

/-- The polar endomorphism differential is the matrix coordinate differential transported by the
standard-basis skew-adjoint equivalence. -/
theorem coe_complexSpinToSpecialOrthogonalPolarCoordinateLieHom [Fact Q.Nondegenerate]
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) :
    RestrictScalars.addEquiv ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)
        (complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q) x) =
      TauCeti.skewAdjointLieEquivOfBasis (Pi.basisFun ℂ (Fin n)) Q.polarBilin
        (DFunLike.congr_fun LinearMap.BilinForm.toMatrix_basisFun Q.polarBilin)
        (RestrictScalars.addEquiv ℝ ℂ
          (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
          (complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q) x)) := by
  simp only [complexSpinToSpecialOrthogonalPolarCoordinateLieHom_apply,
    complexSpinToSpecialOrthogonalCoordinateLieHom_apply,
    complexSpecialOrthogonalLieEquivSkewAdjoint, LieEquiv.trans_apply,
    LieEquiv.restrictScalars_apply, AddEquiv.apply_symm_apply]

end TauCeti.CliffordAlgebra
