/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.OrthonormalBasis
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Projection

/-!
# The compact Spin double cover in an orthonormal frame

Let `V` be a real inner product space with an orthonormal basis `b` indexed by `Fin n`, and `Q` the
form `Q v = ‖v‖²`. The coordinates of `b` identify the Spin group of `Q` with the compact Spin group
`Spin(n)` as a topological group. Composing with the projection between the closed Spin and
special-orthogonal unit-group carriers gives the Spin projection of `Q` written in the frame `b`:
a continuous homomorphism from the Spin group of `Q` to the determinant-one orthogonal matrices,
viewed as a subgroup of `GL(n, ℝ)`. It sends a Spin element to the matrix, in the basis `b`, of its
vector action.

This frame projection is onto and, in positive dimension, a covering map whose kernel consists of
`1` and `-1`. These are the properties of the compact Spin double cover, transported along the
frame to the unit-group carrier of `SO(n)` that serves as the structure group of orthonormal frame
bundles.

## Main definitions

* `OrthonormalBasis.realCliffordSpinFrameProjection b hQ`: the Spin projection of `Q` in the frame
  `b`, with values in the special-orthogonal carrier in `GL(n, ℝ)`.

## Main results

* `OrthonormalBasis.coe_realCliffordSpinFrameProjection_apply`: the frame projection of `x` is the
  matrix of the vector action of `x` in the basis `b`.
* `OrthonormalBasis.realCliffordSpinFrameProjection_surjective`: the frame projection is onto.
* `OrthonormalBasis.realCliffordSpinFrameProjection_eq_one_iff`: in positive dimension its kernel
  consists of `1` and `-1`.
* `OrthonormalBasis.isCoveringMap_realCliffordSpinFrameProjection`: in positive dimension it is a
  covering map.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter II, §1.
-/

public section

noncomputable section

open CliffordAlgebra TauCeti TauCeti.CliffordAlgebra

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) (hQ : ∀ v, Q v = ‖v‖ ^ 2)

/-- The Spin projection of the form `Q v = ‖v‖²` written in the orthonormal frame `b`: the frame
identification of the Spin group of `Q` with `Spin(n)`, followed by the projection between the
closed Spin and special-orthogonal unit-group carriers. -/
def realCliffordSpinFrameProjection :
    spinGroup Q →ₜ* MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
      (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)) :=
  (realCliffordSpinToSpecialOrthogonalRange n).comp
    ((b.isometryEquivRealCliffordFormZero hQ).spinGroupContinuousMulEquiv.trans
      (realCliffordSpinContinuousMulEquivUnitsRange n) :
        spinGroup Q →ₜ* MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)))

/-- The frame projection applies the carrier projection to the unit-group carrier point of the
element of `Spin(n)` that corresponds to `x` in the frame `b`. -/
theorem realCliffordSpinFrameProjection_apply (x : spinGroup Q) :
    b.realCliffordSpinFrameProjection hQ x =
      realCliffordSpinToSpecialOrthogonalRange n (realCliffordSpinContinuousMulEquivUnitsRange n
        ((b.isometryEquivRealCliffordFormZero hQ).spinGroupEquiv x)) := by
  simp [realCliffordSpinFrameProjection]

/-- The frame projection of `x` is the matrix, in the basis `b`, of the vector action of `x`. -/
@[simp]
theorem coe_realCliffordSpinFrameProjection_apply (x : spinGroup Q) :
    ((b.realCliffordSpinFrameProjection hQ x : Matrix.GeneralLinearGroup (Fin n) ℝ) :
      Matrix (Fin n) (Fin n) ℝ) =
      LinearMap.toMatrix b.toBasis b.toBasis
        ((spinToSpecialOrthogonal Q x : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V) := by
  ext i j
  rw [realCliffordSpinFrameProjection_apply, realCliffordSpinContinuousMulEquivUnitsRange_apply,
    realCliffordSpinToSpecialOrthogonalRange_apply_toUnits,
    QuadraticMap.specialOrthogonalToGeneralLinear_apply, coe_spinToSpecialOrthogonal_apply,
    ← isometryEquivRealCliffordFormZero_apply_self b hQ j,
    QuadraticMap.IsometryEquiv.spinGroupEquiv_apply,
    ← QuadraticMap.IsometryEquiv.toIsometry_apply,
    QuadraticMap.Isometry.spinGroupMap_spinVectorAction,
    QuadraticMap.IsometryEquiv.toIsometry_apply,
    isometryEquivRealCliffordFormZero_apply, LinearMap.toMatrix_apply, b.coe_toBasis_repr_apply,
    b.coe_toBasis, LinearEquiv.coe_coe, coe_spinToSpecialOrthogonal_apply]

/-- The frame projection is onto the special-orthogonal carrier. -/
theorem realCliffordSpinFrameProjection_surjective :
    Function.Surjective (b.realCliffordSpinFrameProjection hQ) :=
  (realCliffordSpinToSpecialOrthogonalRange_surjective n).comp
    ((b.isometryEquivRealCliffordFormZero hQ).spinGroupContinuousMulEquiv.trans
      (realCliffordSpinContinuousMulEquivUnitsRange n)).surjective

/-- In positive dimension, a Spin element of `Q` has trivial frame projection exactly when it is
`1` or `-1`. -/
theorem realCliffordSpinFrameProjection_eq_one_iff [NeZero n] (x : spinGroup Q) :
    b.realCliffordSpinFrameProjection hQ x = 1 ↔
      (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  have hinj : Function.Injective
      (CliffordAlgebra.map (b.isometryEquivRealCliffordFormZero hQ).toIsometry) :=
    (CliffordAlgebra.equivOfIsometry (b.isometryEquivRealCliffordFormZero hQ)).injective
  rw [realCliffordSpinFrameProjection_apply, realCliffordSpinContinuousMulEquivUnitsRange_apply,
    realCliffordSpinToSpecialOrthogonalRange_eq_one_iff, Units.ext_iff, Units.ext_iff,
    spinGroup.val_toUnits_apply,
    QuadraticMap.IsometryEquiv.spinGroupEquiv_apply, QuadraticMap.Isometry.coe_spinGroupMap_apply,
    Units.val_neg, Units.val_one, ← hinj.eq_iff, ← hinj.eq_iff, map_one, map_neg, map_one]

/-- In positive dimension, the frame projection is a covering map. -/
theorem isCoveringMap_realCliffordSpinFrameProjection [NeZero n] :
    IsCoveringMap (b.realCliffordSpinFrameProjection hQ) :=
  (isCoveringMap_realCliffordSpinToSpecialOrthogonalRange n).comp_homeomorph
    ((b.isometryEquivRealCliffordFormZero hQ).spinGroupContinuousMulEquiv.trans
      (realCliffordSpinContinuousMulEquivUnitsRange n)).toHomeomorph

end OrthonormalBasis
