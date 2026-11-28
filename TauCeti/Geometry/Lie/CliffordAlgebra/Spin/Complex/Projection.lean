/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SkewAdjoint
public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Complex.Basic
public import TauCeti.Geometry.Lie.Subgroup.SpecialOrthogonal
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.UnitsRange

/-!
# Smooth complex Spin-to-SO projection and its coordinate differentials

For any quadratic form `Q` on `Fin n → ℂ`, `TauCeti.Geometry.Lie.Subgroup.SpecialOrthogonal`
equips the coordinate range of `SO(Q)` inside `(Matrix (Fin n) (Fin n) ℂ)ˣ` with a real Lie-group
structure and, when `Q` is nondegenerate, identifies its real Lie algebra with
`RestrictScalars ℝ ℂ (skewAdjointMatricesLieSubalgebra (toMatrix' Q.polarBilin))` and
`RestrictScalars ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)`.

Automatic smoothness upgrades the continuous range-carrier Spin projection
`CliffordAlgebra.spinToSpecialOrthogonalUnitsRange Q` to a smooth homomorphism between the closed
complex `Spin(Q)` and `SO(Q)` unit ranges. Applying `lieMap` and conjugating by the source and
target coordinate equivalences produces the real Lie homomorphisms
`complexSpinToSpecialOrthogonalCoordinateLieHom` and
`complexSpinToSpecialOrthogonalPolarCoordinateLieHom` whose commutator action and `ℂ`-linearity are
established in `TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Complex.Differential`.

## Main definitions

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

/-- The real differential of the complex `Spin(Q) → SO(Q)` projection in quadratic-Clifford source
coordinates and polar skew-adjoint matrix target coordinates. -/
def complexSpinToSpecialOrthogonalCoordinateLieHom [Fact Q.Nondegenerate] :
    RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q) →ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ
        (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin)) :=
  (TauCeti.Lie.complexSpecialOrthogonalLieEquivSkewAdjointMatrices (Q := Q)).toLieHom.comp
    ((lieMap (complexSpinToSpecialOrthogonalSmoothRange (Q := Q))).comp
      (complexSpinLieEquivQuadratic (Q := Q)).symm.toLieHom)

/-- Evaluating `complexSpinToSpecialOrthogonalCoordinateLieHom` conjugates the abstract Lie map by
the source and matrix target coordinate equivalences. -/
@[simp]
theorem complexSpinToSpecialOrthogonalCoordinateLieHom_apply [Fact Q.Nondegenerate]
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) :
    complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q) x =
      TauCeti.Lie.complexSpecialOrthogonalLieEquivSkewAdjointMatrices (Q := Q)
        (lieMap (complexSpinToSpecialOrthogonalSmoothRange (Q := Q))
          ((complexSpinLieEquivQuadratic (Q := Q)).symm x)) := by
  simp only [complexSpinToSpecialOrthogonalCoordinateLieHom, LieHom.comp_apply,
    LieEquiv.coe_toLieHom]

/-- The real differential of the complex `Spin(Q) → SO(Q)` projection in quadratic-Clifford source
coordinates and basis-free polar skew-adjoint endomorphism target coordinates. -/
def complexSpinToSpecialOrthogonalPolarCoordinateLieHom [Fact Q.Nondegenerate] :
    RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q) →ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin) :=
  (TauCeti.Lie.complexSpecialOrthogonalLieEquivSkewAdjoint (Q := Q)).toLieHom.comp
    ((lieMap (complexSpinToSpecialOrthogonalSmoothRange (Q := Q))).comp
      (complexSpinLieEquivQuadratic (Q := Q)).symm.toLieHom)

/-- Evaluating `complexSpinToSpecialOrthogonalPolarCoordinateLieHom` conjugates the abstract Lie map
by the source and polar endomorphism target coordinate equivalences. -/
@[simp]
theorem complexSpinToSpecialOrthogonalPolarCoordinateLieHom_apply [Fact Q.Nondegenerate]
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) :
    complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q) x =
      TauCeti.Lie.complexSpecialOrthogonalLieEquivSkewAdjoint (Q := Q)
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
    TauCeti.Lie.coe_complexSpecialOrthogonalLieEquivSkewAdjoint_apply_apply]

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
    TauCeti.Lie.coe_complexSpecialOrthogonalLieEquivSkewAdjoint]

end TauCeti.CliffordAlgebra
