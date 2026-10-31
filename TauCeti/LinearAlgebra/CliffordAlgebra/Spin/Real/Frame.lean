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

/-!
# Changing the orthonormal frame of the compact Spin group

Let `V` be a real inner product space with `n`-element orthonormal bases, and `Q` the form
`Q v = ‖v‖²`. Each orthonormal basis `b` identifies `Q` with the positive-definite coordinate form
`realCliffordForm n 0` (`OrthonormalBasis.isometryEquivRealCliffordFormZero`), and hence the Spin
group of `Q` with the compact Spin group `Spin(n)` through
`QuadraticMap.IsometryEquiv.spinGroupEquiv`. This file computes how that frame identification
depends on the basis.

Two frames `b` and `b'` differ by the coordinate rotation `x ↦ b'.repr (∑ i, x i • b i)`. A Spin
element `s` of `Spin(n)` acts on coordinates by this transition exactly when the two frame
identifications differ by conjugation by `s`. Such an `s` exists if and only if `b` and `b'` have
the same orientation: the transition has determinant `b'.toBasis.det b = ±1`, and the Spin action
is onto the determinant-one isometries of a positive-definite form. Oppositely oriented frames
differ by a reflection, which is not the vector action of a Spin element.

## Main results

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
private theorem det_transition :
    (LinearEquiv.det ((b.isometryEquivRealCliffordFormZero hQ).symm.trans
      (b'.isometryEquivRealCliffordFormZero hQ)).toLinearEquiv : ℝ) = b'.toBasis.det b := by
  have hσ (i : Fin n) : b'.toBasis.equiv b.toBasis (Equiv.refl _) (b' i) = b i := by
    simpa using b'.toBasis.equiv_apply (b' := b.toBasis) (e := Equiv.refl _) i
  have hconj : ((b.isometryEquivRealCliffordFormZero hQ).symm.trans
      (b'.isometryEquivRealCliffordFormZero hQ)).toLinearEquiv =
      ((b'.isometryEquivRealCliffordFormZero hQ).toLinearEquiv.symm.trans
        (b'.toBasis.equiv b.toBasis (Equiv.refl _))).trans
          (b'.isometryEquivRealCliffordFormZero hQ).toLinearEquiv := by
    ext x : 1
    simp [isometryEquivRealCliffordFormZero_symm_apply, map_sum, map_smul, hσ]
  rw [hconj, LinearEquiv.det_conj, LinearEquiv.coe_det, Module.Basis.det_basis, b.coe_toBasis]

/-- If the Spin element `s` acts on coordinates by the transition from the frame `b` to the frame
`b'`, then the identification of the Spin group of `Q` with `Spin(n)` along `b'` is the one along
`b` followed by conjugation by `s`. -/
theorem spinGroupEquiv_isometryEquivRealCliffordFormZero_eq_conj
    (s : realCliffordSpinGroupZero n)
    (hs : ∀ v, spinVectorAction (realCliffordForm n 0) s
      (b.isometryEquivRealCliffordFormZero hQ v) = b'.isometryEquivRealCliffordFormZero hQ v)
    (x : spinGroup Q) :
    (b'.isometryEquivRealCliffordFormZero hQ).spinGroupEquiv x =
      s * (b.isometryEquivRealCliffordFormZero hQ).spinGroupEquiv x * s⁻¹ := by
  let t := (b.isometryEquivRealCliffordFormZero hQ).symm.trans
    (b'.isometryEquivRealCliffordFormZero hQ)
  have ht : t.spinGroupEquiv = MulAut.conj s :=
    t.spinGroupEquiv_eq_conj s fun y ↦ by
      simpa [t] using hs ((b.isometryEquivRealCliffordFormZero hQ).symm y)
  have he : b'.isometryEquivRealCliffordFormZero hQ =
      (b.isometryEquivRealCliffordFormZero hQ).trans t :=
    DFunLike.ext _ _ fun v ↦ by simp [t]
  rw [he, QuadraticMap.IsometryEquiv.spinGroupEquiv_trans, MulEquiv.trans_apply, ht,
    MulAut.conj_apply]

/-- The coordinate transition from the frame `b` to the frame `b'` is the vector action of an
element of `Spin(n)` if and only if `b` and `b'` have the same orientation. -/
theorem exists_spinVectorAction_eq_iff_orientation_eq :
    (∃ s : realCliffordSpinGroupZero n, ∀ v, spinVectorAction (realCliffordForm n 0) s
      (b.isometryEquivRealCliffordFormZero hQ v) = b'.isometryEquivRealCliffordFormZero hQ v) ↔
      b.toBasis.orientation = b'.toBasis.orientation := by
  let t := (b.isometryEquivRealCliffordFormZero hQ).symm.trans
    (b'.isometryEquivRealCliffordFormZero hQ)
  constructor
  · rintro ⟨s, hs⟩
    have hts : t.toLinearEquiv =
        (spinToSpecialOrthogonal (realCliffordForm n 0) s :
          (Fin (n + 0) → ℝ) ≃ₗ[ℝ] (Fin (n + 0) → ℝ)) := by
      ext y : 1
      simpa [t, coe_spinToSpecialOrthogonal_apply] using
        (hs ((b.isometryEquivRealCliffordFormZero hQ).symm y)).symm
    have hdet : b'.toBasis.det b = 1 := by
      rw [← det_transition b b' hQ]
      refine (congrArg (fun f ↦ (LinearEquiv.det f : ℝ)) hts).trans ?_
      rw [(QuadraticMap.mem_specialOrthogonalGroup_iff.mp
        (spinToSpecialOrthogonal (realCliffordForm n 0) s).2).2, Units.val_one]
    have hpos : 0 < b'.toBasis.det b := by
      rw [hdet]
      exact one_pos
    rw [← b.coe_toBasis] at hpos
    exact ((b'.toBasis.orientation_eq_iff_det_pos b.toBasis).mpr hpos).symm
  · intro h
    have hdet : LinearEquiv.det t.toLinearEquiv = 1 := by
      rw [← Units.val_inj, det_transition b b' hQ,
        b'.det_to_matrix_orthonormalBasis_of_same_orientation b h.symm, Units.val_one]
    obtain ⟨s, hs⟩ := spinToSpecialOrthogonal_surjective_of_posDef _
      (posDef_realCliffordForm_zero n)
      ⟨t.toLinearEquiv, QuadraticMap.mem_specialOrthogonalGroup_iff.mpr
        ⟨QuadraticMap.mem_orthogonalGroup_iff.mpr t.map_app, hdet⟩⟩
    refine ⟨s, fun v ↦ ?_⟩
    rw [← coe_spinToSpecialOrthogonal_apply, hs]
    exact congrArg (b'.isometryEquivRealCliffordFormZero hQ)
      ((b.isometryEquivRealCliffordFormZero hQ).symm_apply_apply v)

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
