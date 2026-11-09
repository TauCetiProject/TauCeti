/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Frame
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
* `OrthonormalBasis.realCliffordSpinFrameProjection_eq_conj` and
  `OrthonormalBasis.exists_realCliffordSpinFrameProjection_eq_conj`: changing to an equally
  oriented frame conjugates the frame projection by the projection of a Spin element.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter II, §1.
-/

public section

noncomputable section

open CliffordAlgebra TauCeti TauCeti.CliffordAlgebra

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  {n : ℕ} (b b' : OrthonormalBasis (Fin n) ℝ V) (hQ : ∀ v, Q v = ‖v‖ ^ 2)

/-- The Spin projection of the form `Q v = ‖v‖²` written in the orthonormal frame `b`: the frame
identification of the Spin group of `Q` with `Spin(n)`, followed by the projection between the
closed Spin and special-orthogonal unit-group carriers. -/
def realCliffordSpinFrameProjection :
    -- `realCliffordForm n 0` lives on `Fin (n + 0) → ℝ`, which is `Fin n → ℝ` by definition. As in
    -- `realCliffordSpinToSpecialOrthogonalRange`, the `show` states it on `Fin n → ℝ`, so that the
    -- codomain is a subgroup of `GL(n, ℝ)` indexed by `Fin n`.
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
  -- The frame isometry sends `b j` to the `j`-th coordinate vector and intertwines the vector
  -- actions of `x` and of its image in `Spin(n)`.
  have h := (b.isometryEquivRealCliffordFormZero hQ).toIsometry.spinGroupMap_spinVectorAction x
    (b j)
  simp only [QuadraticMap.IsometryEquiv.toIsometry_apply,
    isometryEquivRealCliffordFormZero_apply_self] at h
  simp [realCliffordSpinFrameProjection_apply, LinearMap.toMatrix_apply, h]

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
  rw [realCliffordSpinFrameProjection_apply, realCliffordSpinContinuousMulEquivUnitsRange_apply,
    realCliffordSpinToSpecialOrthogonalRange_eq_one_iff]
  simp only [Units.ext_iff, spinGroup.val_toUnits_apply, Units.val_one, Units.val_neg,
    OneMemClass.coe_eq_one, EmbeddingLike.map_eq_one_iff,
    QuadraticMap.IsometryEquiv.coe_spinGroupEquiv_eq_neg_one_iff]

/-- If the Spin element `s` acts on coordinates by the transition from the frame `b` to the frame
`b'`, then the frame projection along `b'` is the one along `b` conjugated by the carrier
projection of `s`. -/
theorem realCliffordSpinFrameProjection_eq_conj (s : realCliffordSpinGroupZero n)
    (hs : ∀ v, spinVectorAction (realCliffordForm n 0) s
      (b.isometryEquivRealCliffordFormZero hQ v) = b'.isometryEquivRealCliffordFormZero hQ v)
    (x : spinGroup Q) :
    b'.realCliffordSpinFrameProjection hQ x =
      realCliffordSpinToSpecialOrthogonalRange n
          (realCliffordSpinContinuousMulEquivUnitsRange n s) *
        b.realCliffordSpinFrameProjection hQ x *
          (realCliffordSpinToSpecialOrthogonalRange n
            (realCliffordSpinContinuousMulEquivUnitsRange n s))⁻¹ := by
  simp only [realCliffordSpinFrameProjection_apply,
    b.spinGroupEquiv_isometryEquivRealCliffordFormZero_eq_conj b' hQ s hs, map_mul, map_inv]

/-- For two orthonormal frames `b` and `b'` with the same orientation, the frame projections along
`b` and `b'` differ by an inner automorphism of the special-orthogonal carrier. -/
theorem exists_realCliffordSpinFrameProjection_eq_conj
    (h : b.toBasis.orientation = b'.toBasis.orientation) :
    ∃ g : MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)),
      ∀ x : spinGroup Q,
        b'.realCliffordSpinFrameProjection hQ x =
          g * b.realCliffordSpinFrameProjection hQ x * g⁻¹ := by
  obtain ⟨s, hs⟩ := (b.exists_spinVectorAction_eq_iff_orientation_eq b' hQ).mpr h
  exact ⟨_, b.realCliffordSpinFrameProjection_eq_conj b' hQ s hs⟩

/-- In positive dimension, the frame projection is a covering map. -/
theorem isCoveringMap_realCliffordSpinFrameProjection [NeZero n] :
    IsCoveringMap (b.realCliffordSpinFrameProjection hQ) :=
  (isCoveringMap_realCliffordSpinToSpecialOrthogonalRange n).comp_homeomorph
    ((b.isometryEquivRealCliffordFormZero hQ).spinGroupContinuousMulEquiv.trans
      (realCliffordSpinContinuousMulEquivUnitsRange n)).toHomeomorph

end OrthonormalBasis
