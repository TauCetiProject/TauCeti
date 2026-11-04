/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Map
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic
public import Mathlib.Analysis.InnerProductSpace.Orientation
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Changing the orthonormal frame of the compact Spin group

Let `V` be a real inner product space with `n`-element orthonormal bases, and `Q` the form
`Q v = ‖v‖²`. Each orthonormal basis `b` identifies `Q` with the positive-definite coordinate form
`realCliffordForm n 0` (`OrthonormalBasis.isometryEquivRealCliffordFormZero`), and hence the Spin
group of `Q` with the compact Spin group `Spin(n)` through
`QuadraticMap.IsometryEquiv.spinGroupEquiv`. This file computes how that frame identification
depends on the basis.

Two frames `b` and `b'` differ by the orthogonal coordinate transition
`x ↦ b'.repr (∑ i, x i • b i)`. If a Spin element `s` of `Spin(n)` acts on coordinates by this
transition, the two frame identifications differ by conjugation by `s`; this is the frame case of
`QuadraticMap.IsometryEquiv.spinGroupEquiv_apply_eq_conj`. Such an `s` exists if and only if `b`
and `b'` have the same orientation. Indeed, the transition has determinant
`b'.toBasis.det b = ±1` (`Module.Basis.det_equivFun_symm_trans_equivFun`), and a transition into
a positive-definite form is the vector action of a Spin element exactly when its determinant is
one (`QuadraticMap.IsometryEquiv.exists_spinVectorAction_eq_iff_det_eq_one`). Oppositely
oriented frames differ by an isometry of determinant `-1`, which is not the vector action of a Spin
element.

## Main results

* `OrthonormalBasis.det_isometryEquivRealCliffordFormZero_symm_trans`: the transition from `b` to
  `b'` has determinant `b'.toBasis.det b`.
* `OrthonormalBasis.spinGroupEquiv_isometryEquivRealCliffordFormZero_eq_conj`: if `s` acts by
  the transition from `b` to `b'`, the frame identification along `b'` is the one along `b`
  followed by conjugation by `s`.
* `OrthonormalBasis.exists_spinVectorAction_eq_iff_orientation_eq`: the transition is the vector
  action of a Spin element exactly when the two frames have the same orientation.
* `OrthonormalBasis.exists_spinGroupEquiv_isometryEquivRealCliffordFormZero_eq_conj`: the frame
  identifications along two equally oriented frames differ by an inner automorphism of `Spin(n)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter II, §1.
-/

public section

noncomputable section

open CliffordAlgebra TauCeti

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  {n : ℕ} (b b' : OrthonormalBasis (Fin n) ℝ V) (hQ : ∀ v, Q v = ‖v‖ ^ 2)

/-- The coordinate transition from the frame `b` to the frame `b'` has determinant
`b'.toBasis.det b`: it is the change of basis from `b'` to `b`, written in the coordinates of
`b'`. -/
theorem det_isometryEquivRealCliffordFormZero_symm_trans :
    (LinearEquiv.det ((b.isometryEquivRealCliffordFormZero hQ).symm.trans
      (b'.isometryEquivRealCliffordFormZero hQ)).toLinearEquiv : ℝ) = b'.toBasis.det b := by
  have h : ((b.isometryEquivRealCliffordFormZero hQ).symm.trans
      (b'.isometryEquivRealCliffordFormZero hQ)).toLinearEquiv =
        b.toBasis.equivFun.symm.trans b'.toBasis.equivFun := by
    rw [← isometryEquivRealCliffordFormZero_toLinearEquiv b hQ,
      ← isometryEquivRealCliffordFormZero_toLinearEquiv b' hQ]
    ext x : 1
    simp only [LinearEquiv.trans_apply, QuadraticMap.IsometryEquiv.coe_symm_toLinearEquiv,
      QuadraticMap.IsometryEquiv.coe_toLinearEquiv, QuadraticMap.IsometryEquiv.trans_apply]
  rw [h, Module.Basis.det_equivFun_symm_trans_equivFun, b.coe_toBasis]

/-- If the Spin element `s` acts on coordinates by the transition from the frame `b` to the frame
`b'`, then the identification of the Spin group of `Q` with `Spin(n)` along `b'` is the one along
`b` followed by conjugation by `s`. -/
theorem spinGroupEquiv_isometryEquivRealCliffordFormZero_eq_conj
    (s : realCliffordSpinGroupZero n)
    (hs : ∀ v, spinVectorAction (realCliffordForm n 0) s
      (b.isometryEquivRealCliffordFormZero hQ v) = b'.isometryEquivRealCliffordFormZero hQ v)
    (x : spinGroup Q) :
    (b'.isometryEquivRealCliffordFormZero hQ).spinGroupEquiv x =
      s * (b.isometryEquivRealCliffordFormZero hQ).spinGroupEquiv x * s⁻¹ :=
  (b.isometryEquivRealCliffordFormZero hQ).spinGroupEquiv_apply_eq_conj _ s hs x

/-- The coordinate transition from the frame `b` to the frame `b'` is the vector action of an
element of `Spin(n)` if and only if `b` and `b'` have the same orientation. -/
theorem exists_spinVectorAction_eq_iff_orientation_eq :
    (∃ s : realCliffordSpinGroupZero n, ∀ v, spinVectorAction (realCliffordForm n 0) s
      (b.isometryEquivRealCliffordFormZero hQ v) = b'.isometryEquivRealCliffordFormZero hQ v) ↔
      b.toBasis.orientation = b'.toBasis.orientation := by
  rw [QuadraticMap.IsometryEquiv.exists_spinVectorAction_eq_iff_det_eq_one
      (posDef_realCliffordForm_zero n), ← Units.val_inj,
    det_isometryEquivRealCliffordFormZero_symm_trans, Units.val_one]
  refine ⟨fun h ↦ ((b'.toBasis.orientation_eq_iff_det_pos b.toBasis).mpr ?_).symm,
    fun h ↦ b'.det_to_matrix_orthonormalBasis_of_same_orientation b h.symm⟩
  rw [b.coe_toBasis, h]
  exact one_pos

/-- For two orthonormal frames `b` and `b'` with the same orientation, the identifications of the
Spin group of `Q` with `Spin(n)` along `b` and `b'` differ by an inner automorphism of `Spin(n)`. -/
theorem exists_spinGroupEquiv_isometryEquivRealCliffordFormZero_eq_conj
    (h : b.toBasis.orientation = b'.toBasis.orientation) :
    ∃ s : realCliffordSpinGroupZero n, ∀ x : spinGroup Q,
      (b'.isometryEquivRealCliffordFormZero hQ).spinGroupEquiv x =
        s * (b.isometryEquivRealCliffordFormZero hQ).spinGroupEquiv x * s⁻¹ := by
  obtain ⟨s, hs⟩ := (b.exists_spinVectorAction_eq_iff_orientation_eq b' hQ).mpr h
  exact ⟨s, b.spinGroupEquiv_isometryEquivRealCliffordFormZero_eq_conj b' hQ s hs⟩

end OrthonormalBasis
