/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.Matrix.ToLin
public import TauCeti.Geometry.Lie.AlgebraHom
public import TauCeti.Algebra.Lie.Subalgebra.RestrictScalars
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Complex.Basic
public import TauCeti.RepresentationTheory.Spin.Representation
public import TauCeti.Analysis.Matrix.Normed

/-!
# Differentiating complex Clifford actions on Spin

A real algebra action of a complex Clifford algebra restricts to a smooth homomorphism on the
closed Spin range. In quadratic Clifford coordinates, its real differential is the original action.
For a complex-linear action, this differential is complex linear in its quadratic coordinate,
despite being computed using real manifolds.

For a polarization and any finite basis of its exterior spinor module, we apply this construction
to the matrix form of the native Fock action. The resulting smooth homomorphism is the native
`spinRep` in that basis, and its differential is the matrix of the same quadratic Fock operator.
The `ℂ`-linear Lie algebra homomorphism
`TauCeti.SpinPolarizationData.complexSpinSmoothMatrixComplexLieHom` packages the Fock
representation on `quadraticLieSubalgebra Q`, characterized pointwise by
`complexSpinSmoothMatrixComplexLieHom_apply` and identified with the real manifold differential by
`complexSpinSmoothMatrixComplexLieHom_eq_unitsLieAlgebraLieEquiv_lieMap`.
Both even and odd ambient dimensions, including dimensions zero and one, are covered.
The smooth structures require `[Fact Q.Nondegenerate]`. For a polarization `P`, obtain it with
`letI : Fact Q.Nondegenerate := ⟨P.nondegenerate (.of_ne_zero two_ne_zero)⟩`.

The argument uses `AlgHom.unitsSmoothHom` and its differential formula, following the compact
real comparison in `TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Representation`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Sections 2 and 5.
-/

public section

open Manifold TauCeti TauCeti.CliffordAlgebra CliffordAlgebra
open scoped ContDiff Manifold Matrix.Norms.Operator

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
-- Use the real normed-algebra scalar action when forming real differentials.
attribute [local instance] NormedAlgebra.toNormedSpace
attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace AlgHom

variable {n : ℕ} {Q : QuadraticForm ℂ (Fin n → ℂ)}
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  [Fact Q.Nondegenerate] (f : CliffordAlgebra Q →ₐ[ℝ] A)

local notation "SpinUnitsRange" => MonoidHom.range (spinGroup.toUnits (Q := Q))

local notation "SpinLieModel" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra Q)) SpinUnitsRange)

/-- The smooth restriction of a complex Clifford action to the closed Spin range, using
underlying real manifolds. -/
def complexSpinSmoothHom :
    ContMDiffMonoidMorphism 𝓘(ℝ, SpinLieModel) 𝓘(ℝ, A) ∞ SpinUnitsRange Aˣ := by
  exact f.unitsSmoothHom.comp
    (complexSpinEmbeddedLieSubgroupData (Fact.out : Q.Nondegenerate)).subtypeVal

/-- The smooth restriction has the usual action of the Clifford homomorphism on units. -/
@[simp]
theorem complexSpinSmoothHom_apply (g : SpinUnitsRange) :
    f.complexSpinSmoothHom g = Units.map f.toMonoidHom g.val := by
  simp only [complexSpinSmoothHom, ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
    TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply, unitsSmoothHom_apply]

/-- In quadratic coordinates, the real differential of a complex Clifford action restricted
to Spin is the original Clifford action. -/
@[simp↓ high]
theorem unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothHom
    (X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel) SpinUnitsRange) :
    TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap (f.complexSpinSmoothHom) X) =
      f (RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)
        (complexSpinLieEquivQuadratic (Q := Q) X)) := by
  simp only [complexSpinSmoothHom, lieMap_comp, LieHom.comp_apply,
    unitsLieAlgebraLieEquiv_lieMap_unitsSmoothHom,
    ← TauCeti.Lie.EmbeddedLieSubgroupData.lieMapSubtypeVal_apply,
    unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_complexSpinLieEquivQuadratic]

/-- In quadratic coordinates, the differential of the Spin action equals the restriction of
its real Clifford action, as an equality of real Lie algebra homomorphisms. -/
theorem lieMap_complexSpinSmoothHom_eq :
    (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := A)).toLieHom.comp
        ((lieMap f.complexSpinSmoothHom).comp
          (complexSpinLieEquivQuadratic (Q := Q)).symm.toLieHom) =
      f.toLieHom.comp
        ((quadraticLieSubalgebra Q).restrictScalarsIncl ℝ) := by
  ext x
  simp only [LieHom.comp_apply, LieEquiv.coe_toLieHom,
    unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothHom, LieEquiv.apply_symm_apply,
    AlgHom.toLieHom_apply, LieSubalgebra.restrictScalarsIncl_apply]

end AlgHom

namespace TauCeti.SpinPolarizationData

variable {n : ℕ} {Q : QuadraticForm ℂ (Fin n → ℂ)} (P : SpinPolarizationData Q)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℂ (ExteriorAlgebra ℂ P.W))

local notation "SpinUnitsRange" => MonoidHom.range (spinGroup.toUnits (Q := Q))

local notation "SpinLieModel" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra Q)) SpinUnitsRange)

section Smooth

variable [Fact Q.Nondegenerate]

/-- The native Fock representation, in a chosen finite spinor basis, as a smooth homomorphism
on the complex Spin range with its underlying real smooth structure. -/
def complexSpinSmoothMatrixHom :
    ContMDiffMonoidMorphism 𝓘(ℝ, SpinLieModel) 𝓘(ℝ, Matrix ι ι ℂ) ∞
      SpinUnitsRange (Matrix ι ι ℂ)ˣ := by
  exact ((((LinearMap.toMatrixAlgEquiv b).toAlgHom).comp (spinAction Q P)).restrictScalars ℝ)
    |>.complexSpinSmoothHom

/-- The smooth matrix action on any element of the Spin range is the matrix of its Fock action. -/
@[simp]
theorem coe_complexSpinSmoothMatrixHom_apply (g : SpinUnitsRange) :
    (P.complexSpinSmoothMatrixHom b g : Matrix ι ι ℂ) =
      LinearMap.toMatrix b b (spinAction Q P (g : (CliffordAlgebra Q)ˣ)) := by
  simp [complexSpinSmoothMatrixHom, LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply]

/-- On the canonical unit of a native Spin element, the smooth matrix action is precisely
`spinRep` expressed in the chosen spinor basis. -/
theorem complexSpinSmoothMatrixHom_toUnits_eq_spinRep (g : spinGroup Q) :
    (P.complexSpinSmoothMatrixHom b ⟨spinGroup.toUnits g, ⟨g, rfl⟩⟩ : Matrix ι ι ℂ) =
      LinearMap.toMatrix b b (spinRep Q P g) := by
  simp only [coe_complexSpinSmoothMatrixHom_apply, spinGroup.val_toUnits_apply, spinRep_apply]

/-- The real differential of the smooth Fock representation is the same quadratic Clifford
operator in the chosen spinor basis. -/
@[simp↓ high]
theorem unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothMatrixHom
    (X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel) SpinUnitsRange) :
    TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap (P.complexSpinSmoothMatrixHom b) X) =
      LinearMap.toMatrix b b
        (spinAction Q P (RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)
          (complexSpinLieEquivQuadratic (Q := Q) X))) := by
  simp only [complexSpinSmoothMatrixHom,
    AlgHom.unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothHom,
    AlgHom.restrictScalars_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply]

/-- The differentiated Fock representation in quadratic coordinates is the matrix Clifford
action restricted to quadratic elements, as an equality of real Lie algebra homomorphisms. -/
theorem lieMap_complexSpinSmoothMatrixHom_eq :
    (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix ι ι ℂ)).toLieHom.comp
        ((lieMap (P.complexSpinSmoothMatrixHom b)).comp
          (complexSpinLieEquivQuadratic (Q := Q)).symm.toLieHom) =
      (AlgHom.toLieHom
        ((((LinearMap.toMatrixAlgEquiv b).toAlgHom).comp (spinAction Q P)).restrictScalars ℝ)).comp
        ((quadraticLieSubalgebra Q).restrictScalarsIncl ℝ) := by
  exact AlgHom.lieMap_complexSpinSmoothHom_eq _

end Smooth

/-- The `ℂ`-linear Fock Lie algebra representation on `quadraticLieSubalgebra Q` in the chosen
spinor basis `b`. Under the real quadratic coordinate equivalence, this agrees with the
differential of `P.complexSpinSmoothMatrixHom b`. -/
def complexSpinSmoothMatrixComplexLieHom :
    quadraticLieSubalgebra Q →ₗ⁅ℂ⁆ Matrix ι ι ℂ :=
  (((LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (spinAction Q P)).toLieHom).comp
    (quadraticLieSubalgebra Q).incl

/-- In the chosen spinor basis `b`, `P.complexSpinSmoothMatrixComplexLieHom b` acts by the matrix of
`spinAction Q P x`. -/
@[simp]
theorem complexSpinSmoothMatrixComplexLieHom_apply (x : quadraticLieSubalgebra Q) :
    P.complexSpinSmoothMatrixComplexLieHom b x = LinearMap.toMatrix b b (spinAction Q P x) := by
  simp only [complexSpinSmoothMatrixComplexLieHom, LieHom.comp_apply, LieSubalgebra.coe_incl,
    AlgHom.toLieHom_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply]

/-- Under the quadratic coordinate equivalence, `P.complexSpinSmoothMatrixComplexLieHom b`
agrees with the real manifold differential `lieMap (P.complexSpinSmoothMatrixHom b)`. -/
theorem complexSpinSmoothMatrixComplexLieHom_eq_unitsLieAlgebraLieEquiv_lieMap
    [Fact Q.Nondegenerate] (x : quadraticLieSubalgebra Q) :
    P.complexSpinSmoothMatrixComplexLieHom b x =
      TauCeti.Lie.unitsLieAlgebraLieEquiv
        (lieMap (P.complexSpinSmoothMatrixHom b)
          ((complexSpinLieEquivQuadratic (Q := Q)).symm
            ((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)).symm x))) := by
  rw [complexSpinSmoothMatrixComplexLieHom_apply,
    unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothMatrixHom, LieEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

end TauCeti.SpinPolarizationData
