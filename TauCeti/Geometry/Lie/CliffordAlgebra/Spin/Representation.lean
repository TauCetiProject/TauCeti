/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.AlgebraHom
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.LocalDiffeomorph

/-!
# Differentiating Clifford actions of compact real Spin

An action of the real Clifford algebra on a finite-dimensional space restricts to an action of
compact real Spin. Its differential is the same Clifford action restricted to quadratic
elements, which are the Lie algebra of Spin. This is the compatibility needed to compare a
Spin-group representation with its algebraically constructed orthogonal Lie-algebra action.

We work with an algebra homomorphism into an arbitrary finite-dimensional normed real algebra,
so the result applies to matrix actions as well as endomorphism actions. The group is represented
by its closed range in Clifford units, with the established embedded Lie-group structure.
Transport along `realCliffordSpinContinuousMulEquivUnitsRange` recovers the original Spin group.
The final comparison uses the actual differential of the Spin-to-SO projection to identify
the quadratic source coordinate of a prescribed skew-symmetric matrix.

## Main results

* `AlgHom.realCliffordSpinSmoothHom`: the smooth restriction of a Clifford-algebra action.
* `AlgHom.unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinSmoothHom`: its differential in Clifford
  coordinates is the action of the quadratic element.
* `AlgHom.lieMap_realCliffordSpinSmoothHom_eq`: equality with the quadratic Lie-algebra action.
* `AlgHom.unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinSmoothHom_eq_bivectorExterior`:
  the differential in orthogonal coordinates,
  using the normalized exterior bivector associated with a skew-symmetric matrix.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Sections 2 and 5.
* The source coordinates and projection differential follow
  `TauCeti.CliffordAlgebra.realCliffordSpinLieEquivQuadratic` and
  `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalCoordinateLieHom_eq_bivectorEquivSo`.
-/

public section

open Manifold TauCeti TauCeti.CliffordAlgebra CliffordAlgebra
open scoped ContDiff Manifold Matrix.Norms.Operator

noncomputable section

namespace AlgHom

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace

local notation "SpinUnitsRange(" n ")" =>
  MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))

local notation "SpinLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))) (SpinUnitsRange(n)))

variable {n : ℕ} {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

/-- The smooth Spin-group action obtained by restricting a real Clifford-algebra homomorphism
to the closed Spin carrier. -/
def realCliffordSpinSmoothHom (f : CliffordAlgebra (realCliffordForm n 0) →ₐ[ℝ] A) :
    ContMDiffMonoidMorphism 𝓘(ℝ, SpinLieModel(n)) 𝓘(ℝ, A) ∞ (SpinUnitsRange(n)) Aˣ :=
  f.unitsSmoothHom.comp (realCliffordSpinEmbeddedLieSubgroupData n).subtypeVal

/-- The smooth restriction acts by the usual Clifford homomorphism on units. -/
@[simp]
theorem realCliffordSpinSmoothHom_apply
    (f : CliffordAlgebra (realCliffordForm n 0) →ₐ[ℝ] A) (g : SpinUnitsRange(n)) :
    f.realCliffordSpinSmoothHom g = Units.map f.toMonoidHom g.val := by
  simp only [realCliffordSpinSmoothHom, ContMDiffMonoidMorphism.coe_comp,
    Function.comp_apply, TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply,
    unitsSmoothHom_apply]

/-- The differential of a restricted Clifford action, in the canonical algebra coordinates,
is the action of its quadratic Clifford coordinate. -/
@[simp↓ high]
theorem unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinSmoothHom
    (f : CliffordAlgebra (realCliffordForm n 0) →ₐ[ℝ] A)
    (X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel(n)) (SpinUnitsRange(n))) :
    TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap f.realCliffordSpinSmoothHom X) =
      f (realCliffordSpinLieEquivQuadratic n X) := by
  simp only [realCliffordSpinSmoothHom, lieMap_comp, LieHom.comp_apply,
    unitsLieAlgebraLieEquiv_lieMap_unitsSmoothHom,
    ← TauCeti.Lie.EmbeddedLieSubgroupData.lieMapSubtypeVal_apply,
    unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_realCliffordSpinLieEquivQuadratic]

/-- After identifying the source Lie algebra with quadratic Clifford elements, the
differentiated Spin action equals the algebraically defined quadratic action. -/
theorem lieMap_realCliffordSpinSmoothHom_eq
    (f : CliffordAlgebra (realCliffordForm n 0) →ₐ[ℝ] A) :
    (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := A)).toLieHom.comp
        ((lieMap f.realCliffordSpinSmoothHom).comp
          (realCliffordSpinLieEquivQuadratic n).symm.toLieHom) =
      f.toLieHom.comp (quadraticLieSubalgebra (realCliffordForm n 0)).incl := by
  ext x
  simp only [LieHom.comp_apply, LieEquiv.coe_toLieHom,
    unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinSmoothHom, LieEquiv.apply_symm_apply,
    AlgHom.toLieHom_apply, LieSubalgebra.coe_incl]

/-- In orthogonal coordinates, the differentiated action is the Clifford action of the
normalized bivector of the given skew-symmetric matrix. The matrix coordinate is the actual
differential of the Spin projection. -/
theorem unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinSmoothHom_eq_bivectorExterior
    (f : CliffordAlgebra (realCliffordForm n 0) →ₐ[ℝ] A)
    (X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel(n)) (SpinUnitsRange(n))) :
    let Q := QuadraticMap.weightedSumSquares ℝ (1 : Fin n → ℝ)
    letI := bivectorLieRing Q
    letI := bivectorLieAlgebra Q
    TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap f.realCliffordSpinSmoothHom X) =
      f (bivectorExterior (realCliffordForm n 0)
        ((bivectorEquivSo n ℝ).symm
          (realCliffordSpecialOrthogonalLieEquivSo n
            (realCliffordSpinToSpecialOrthogonalRangeLieMap n X)))) := by
  let Q := QuadraticMap.weightedSumSquares ℝ (1 : Fin n → ℝ)
  let _ := bivectorLieRing Q
  let _ := bivectorLieAlgebra Q
  -- Congruence avoids costly `isDefEq` unfolding across the Spin/SO Lie-subalgebra models.
  calc
    TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap f.realCliffordSpinSmoothHom X)
      = f (realCliffordSpinLieEquivQuadratic n X) :=
      unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinSmoothHom f X
    _ = f (bivectorExteriorEquivQuadraticLieSubalgebra (realCliffordForm n 0)
          ((bivectorEquivSo n ℝ).symm
            (realCliffordSpecialOrthogonalLieEquivSo n
              (realCliffordSpinToSpecialOrthogonalRangeLieMap n X)))) :=
      congrArg (fun y : quadraticLieSubalgebra (realCliffordForm n 0) ↦ f y)
        (realCliffordSpinLieEquivQuadratic_eq_bivectorExterior n X)
    _ = _ :=
      congrArg f (coe_bivectorExteriorEquivQuadraticLieSubalgebra_apply (realCliffordForm n 0) _)

end AlgHom
