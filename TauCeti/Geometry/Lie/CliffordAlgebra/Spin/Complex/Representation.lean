/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.AlgebraHom
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Complex.Basic
public import TauCeti.RepresentationTheory.Spin.Representation
public import TauCeti.Analysis.Matrix.Normed

/-!
# Differentiating complex Clifford actions on Spin

A complex Clifford-algebra action restricts to a smooth homomorphism on the closed Spin range.
In quadratic Clifford coordinates, its real differential is the original action. In particular
this differential is complex linear in its quadratic coordinate, despite being computed using
real manifolds.

For a polarization and any finite basis of its exterior spinor module, we apply this construction
to the matrix form of the native Fock action. The resulting smooth homomorphism is the native
`spinRep` in that basis, and its differential is the matrix of the same quadratic Fock operator.
Both even and odd ambient dimensions, including dimensions zero and one, are covered.

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
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [Algebra ℂ A]
  [IsScalarTower ℝ ℂ A] [FiniteDimensional ℝ A]
  (f : CliffordAlgebra Q →ₐ[ℂ] A) (hQ : Q.Nondegenerate)

local notation "SpinUnitsRange" => MonoidHom.range (spinGroup.toUnits (Q := Q))

local notation "SpinLieModel" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra Q)) SpinUnitsRange)

/-- The smooth restriction of a complex Clifford action to the closed Spin range, using
underlying real manifolds. -/
def complexSpinSmoothHom :
    letI := (complexSpinEmbeddedLieSubgroupData hQ).chartedSpace
    letI := (complexSpinEmbeddedLieSubgroupData hQ).lieGroup
    ContMDiffMonoidMorphism 𝓘(ℝ, SpinLieModel) 𝓘(ℝ, A) ∞ SpinUnitsRange Aˣ := by
  letI := (complexSpinEmbeddedLieSubgroupData hQ).chartedSpace
  letI := (complexSpinEmbeddedLieSubgroupData hQ).lieGroup
  exact (f.restrictScalars ℝ).unitsSmoothHom.comp
    (complexSpinEmbeddedLieSubgroupData hQ).subtypeVal

/-- The smooth restriction has the usual action of the Clifford homomorphism on units. -/
@[simp]
theorem complexSpinSmoothHom_apply :
    letI := (complexSpinEmbeddedLieSubgroupData hQ).chartedSpace
    letI := (complexSpinEmbeddedLieSubgroupData hQ).lieGroup
    ∀ g : SpinUnitsRange, f.complexSpinSmoothHom hQ g = Units.map f.toMonoidHom g.1 := by
  intro g
  simp only [complexSpinSmoothHom, ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
    TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply, unitsSmoothHom_apply]
  rfl

/-- In quadratic coordinates, the real differential of a complex Clifford action restricted
to Spin is the original Clifford action. -/
@[simp↓ high]
theorem unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothHom :
    letI := (complexSpinEmbeddedLieSubgroupData hQ).chartedSpace
    letI := (complexSpinEmbeddedLieSubgroupData hQ).lieGroup
    ∀ X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel) SpinUnitsRange,
    TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap (f.complexSpinSmoothHom hQ) X) =
      f (RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)
        (complexSpinLieEquivQuadratic hQ X)) := by
  intro X
  simp only [complexSpinSmoothHom, lieMap_comp, LieHom.comp_apply,
    unitsLieAlgebraLieEquiv_lieMap_unitsSmoothHom,
    ← TauCeti.Lie.EmbeddedLieSubgroupData.lieMapSubtypeVal_apply,
    unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_complexSpinLieEquivQuadratic,
    AlgHom.restrictScalars_apply]

end AlgHom

namespace TauCeti.SpinPolarizationData

variable {n : ℕ} {Q : QuadraticForm ℂ (Fin n → ℂ)} (P : SpinPolarizationData Q)
  (hQ : Q.Nondegenerate) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℂ (ExteriorAlgebra ℂ P.W))

local notation "SpinUnitsRange" => MonoidHom.range (spinGroup.toUnits (Q := Q))

local notation "SpinLieModel" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra Q)) SpinUnitsRange)

/-- The native Fock representation, in a chosen finite spinor basis, as a smooth homomorphism
on the complex Spin range with its underlying real smooth structure. -/
def complexSpinSmoothMatrixHom :
    letI := (complexSpinEmbeddedLieSubgroupData hQ).chartedSpace
    letI := (complexSpinEmbeddedLieSubgroupData hQ).lieGroup
    ContMDiffMonoidMorphism 𝓘(ℝ, SpinLieModel) 𝓘(ℝ, Matrix ι ι ℂ) ∞
      SpinUnitsRange (Matrix ι ι ℂ)ˣ := by
  letI := (complexSpinEmbeddedLieSubgroupData hQ).chartedSpace
  letI := (complexSpinEmbeddedLieSubgroupData hQ).lieGroup
  exact (((LinearMap.toMatrixAlgEquiv b).toAlgHom).comp (spinAction Q P)).complexSpinSmoothHom hQ

/-- On the canonical unit of a native Spin element, the smooth matrix action is precisely
`spinRep` expressed in the chosen spinor basis. -/
@[simp]
theorem coe_complexSpinSmoothMatrixHom_apply (g : spinGroup Q) :
    letI := (complexSpinEmbeddedLieSubgroupData hQ).chartedSpace
    letI := (complexSpinEmbeddedLieSubgroupData hQ).lieGroup
    (P.complexSpinSmoothMatrixHom hQ b ⟨spinGroup.toUnits g, ⟨g, rfl⟩⟩ : Matrix ι ι ℂ) =
      LinearMap.toMatrix b b (spinRep Q P g) := by
  ext i j
  simp [complexSpinSmoothMatrixHom, spinRep_apply, LinearMap.toMatrixAlgEquiv_apply,
    LinearMap.toMatrix_apply]

/-- The real differential of the smooth Fock representation is the same quadratic Clifford
operator in the chosen spinor basis. -/
theorem unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothMatrixHom :
    letI := (complexSpinEmbeddedLieSubgroupData hQ).chartedSpace
    letI := (complexSpinEmbeddedLieSubgroupData hQ).lieGroup
    ∀ X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel) SpinUnitsRange,
    TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap (P.complexSpinSmoothMatrixHom hQ b) X) =
      LinearMap.toMatrix b b
        (spinAction Q P (RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)
          (complexSpinLieEquivQuadratic hQ X))) := by
  intro X
  simp only [complexSpinSmoothMatrixHom,
    AlgHom.unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothHom,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  ext i j
  simp only [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]

end TauCeti.SpinPolarizationData
