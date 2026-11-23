/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Map
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm

/-!
# The Spin projection in standard coordinates

An isometry `e` from a quadratic form `Q` to the standard sum-of-squares form identifies the
special orthogonal group `SO(Q)` with the matrix special orthogonal group, through
`TauCeti.specialOrthogonalGroupEquivMatrix`. This file computes the composite of that comparison
with the Spin projection `CliffordAlgebra.spinToSpecialOrthogonal`: the matrix attached to a Spin
element `x` is the matrix of its vector action `v ↦ x v x⁻¹`, read in the coordinates given by
`e`. Equivalently, it is the standard matrix of the Spin projection of the transported element
`e.spinGroupEquiv x` of the Spin group of the standard form.

## Main results

* `CliffordAlgebra.specialOrthogonalGroupEquivMatrix_spinToSpecialOrthogonal_mulVec`: the matrix
  of a Spin element acts on coordinates through its vector action.
* `CliffordAlgebra.ι_specialOrthogonalGroupEquivMatrix_spinToSpecialOrthogonal_mulVec`: the same
  action, read inside the Clifford algebra as conjugation by the Spin element.
* `CliffordAlgebra.specialOrthogonalGroupEquivMatrix_spinToSpecialOrthogonal`: the coordinate
  comparison of the Spin projection is the standard comparison of the Spin projection of the
  transported Spin element.
-/

public section

namespace CliffordAlgebra

open TauCeti
open scoped Matrix

variable {R : Type*} [CommRing R] [Invertible (2 : R)] {V : Type*} [AddCommGroup V] [Module R V]
  {Q : QuadraticForm R V} {n : Type*} [Fintype n] [DecidableEq n]

/-- Along an isometry `e` to the standard form, the matrix of the Spin projection of `x` acts on
coordinates through the vector action of `x`. -/
theorem specialOrthogonalGroupEquivMatrix_spinToSpecialOrthogonal_mulVec
    (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R))) (x : spinGroup Q)
    (y : n → R) :
    (specialOrthogonalGroupEquivMatrix h2 e (spinToSpecialOrthogonal Q x) : Matrix n n R) *ᵥ y =
      e (spinVectorAction Q x (e.symm y)) := by
  rw [specialOrthogonalGroupEquivMatrix_mulVec, coe_spinToSpecialOrthogonal_apply]

/-- Along an isometry `e` to the standard form, the matrix of the Spin projection of `x` is the
coordinate matrix of the vector action of `x` conjugated by `e`. -/
theorem coe_specialOrthogonalGroupEquivMatrix_spinToSpecialOrthogonal
    (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R))) (x : spinGroup Q) :
    (specialOrthogonalGroupEquivMatrix h2 e (spinToSpecialOrthogonal Q x) : Matrix n n R) =
      LinearMap.toMatrix' (e.toLinearEquiv.toLinearMap ∘ₗ (spinVectorAction Q x).toLinearMap ∘ₗ
        e.toLinearEquiv.symm.toLinearMap) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y ↦ ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_toMatrix',
    specialOrthogonalGroupEquivMatrix_spinToSpecialOrthogonal_mulVec]
  simp

/-- Pulling the coordinate action of the matrix of a Spin element `x` back along `e`, and into the
Clifford algebra, gives conjugation by `x`. -/
theorem ι_specialOrthogonalGroupEquivMatrix_spinToSpecialOrthogonal_mulVec
    (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R))) (x : spinGroup Q)
    (v : V) :
    ι Q (e.symm
        ((specialOrthogonalGroupEquivMatrix h2 e (spinToSpecialOrthogonal Q x) : Matrix n n R) *ᵥ
          e v)) =
      (x : CliffordAlgebra Q) * ι Q v * star (x : CliffordAlgebra Q) := by
  rw [specialOrthogonalGroupEquivMatrix_spinToSpecialOrthogonal_mulVec,
    QuadraticMap.IsometryEquiv.symm_apply_apply, QuadraticMap.IsometryEquiv.symm_apply_apply,
    ι_spinVectorAction_apply]

/-- The coordinate comparison of the Spin projection along `e` is the standard comparison of the
Spin projection of the Spin element transported along `e`. -/
theorem specialOrthogonalGroupEquivMatrix_spinToSpecialOrthogonal (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R))) (x : spinGroup Q) :
    specialOrthogonalGroupEquivMatrix h2 e (spinToSpecialOrthogonal Q x) =
      standardSpecialOrthogonalGroupEquiv h2
        (spinToSpecialOrthogonal (Matrix.toQuadraticForm' (1 : Matrix n n R))
          (e.spinGroupEquiv x)) := by
  rw [specialOrthogonalGroupEquivMatrix_apply,
    QuadraticMap.IsometryEquiv.specialOrthogonalGroupCongr_spinToSpecialOrthogonal]

end CliffordAlgebra
