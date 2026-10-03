/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import TauCeti.Algebra.Star.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Four
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four

/-!
# The compact four-dimensional Spin group

The reversal-preserving equivalence `Cl⁺(4,0) ≃ ℍ × ℍ` transports the even unitary carrier to a
pair of unit-quaternion groups.  The general rank-four comparison between Spin and the even
unitary carrier then gives

`Spin(4) ≃ unitary ℍ × unitary ℍ ≃ SU(2) × SU(2)`.

This is the compact real form of the exceptional type-`D₂ = A₁ × A₁` isomorphism.  Both quaternion
factors have norm one; in particular the split discriminant algebra does not make either factor a
split real group.

## Main definitions and results

* `TauCeti.realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd` identifies the even unitary
  carrier with two unit-quaternion groups.
* `TauCeti.realSpinFourEquivQuaternionUnitaryProd` identifies compact real `Spin(4)` with two
  unit-quaternion groups and exposes its forward and inverse Clifford equations.
* `TauCeti.normSq_fst_realSpinFourEquivQuaternionUnitaryProd` and
  `TauCeti.normSq_snd_realSpinFourEquivQuaternionUnitaryProd` state the two norm-one conditions.
* `TauCeti.realSpinFourEquivSpecialUnitaryProd` identifies compact real `Spin(4)` with
  `SU(2) × SU(2)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Theorem 3.7 and §4.
-/

public section

open scoped Quaternion

namespace TauCeti

/-- The even unitary carrier of the compact four-dimensional real Clifford algebra is a product
of two unit-quaternion groups. -/
noncomputable def realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 4 0) ≃*
      unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  (CliffordAlgebra.evenUnitaryGroupEquivUnitaryOfAlgEquiv
    (realCliffordForm 4 0) realCliffordFourZeroEvenEquivQuaternionProd
    realCliffordFourZeroEvenEquivQuaternionProd_reverseEven).trans
      (Unitary.prodEquiv ℍ[ℝ] ℍ[ℝ])

/-- The quaternion pair underlying the compact even-unitary equivalence is obtained by applying
the even Clifford-algebra equivalence to the Clifford value. -/
@[simp]
theorem coe_realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd_apply
    (x : CliffordAlgebra.evenUnitaryGroup (realCliffordForm 4 0)) :
    (((realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd x).1 : ℍ[ℝ]),
        ((realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd x).2 : ℍ[ℝ])) =
      realCliffordFourZeroEvenEquivQuaternionProd
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0) x) := by
  rw [realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd, MulEquiv.trans_apply,
    Unitary.coe_prodEquiv_apply]
  exact CliffordAlgebra.coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_apply
    (realCliffordForm 4 0) realCliffordFourZeroEvenEquivQuaternionProd
      realCliffordFourZeroEvenEquivQuaternionProd_reverseEven x

/-- The inverse compact even-unitary equivalence has Clifford value obtained by applying the
inverse quaternion-pair algebra equivalence. -/
@[simp]
theorem coe_realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    ((((realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd.symm q :
        CliffordAlgebra.evenUnitaryGroup (realCliffordForm 4 0)) :
          (CliffordAlgebra (realCliffordForm 4 0))ˣ) :
            CliffordAlgebra (realCliffordForm 4 0))) =
      (realCliffordFourZeroEvenEquivQuaternionProd.symm
          ((q.1 : ℍ[ℝ]), (q.2 : ℍ[ℝ])) :
        CliffordAlgebra.even (realCliffordForm 4 0)) := by
  rw [realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd,
    MulEquiv.symm_trans_apply]
  refine (CliffordAlgebra.coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_symm_apply
    (realCliffordForm 4 0) realCliffordFourZeroEvenEquivQuaternionProd
      realCliffordFourZeroEvenEquivQuaternionProd_reverseEven
      ((Unitary.prodEquiv ℍ[ℝ] ℍ[ℝ]).symm q)).trans ?_
  exact congrArg (fun p : ℍ[ℝ] × ℍ[ℝ] =>
    (realCliffordFourZeroEvenEquivQuaternionProd.symm p :
      CliffordAlgebra (realCliffordForm 4 0)))
    (Unitary.coe_prodEquiv_symm_apply ℍ[ℝ] ℍ[ℝ] q)

/-- The compact real Spin group in dimension four is a product of two unit-quaternion groups. -/
noncomputable def realSpinFourEquivQuaternionUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  (CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour
    (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0) (by simp) (by simp)).trans
    realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd

/-- The compact `Spin(4)` equivalence evaluates the quaternion-pair algebra model on the
underlying even Clifford element. -/
@[simp]
theorem coe_realSpinFourEquivQuaternionUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    (((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]),
        ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])) =
      realCliffordFourZeroEvenEquivQuaternionProd
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s)) := by
  rw [realSpinFourEquivQuaternionUnitaryProd, MulEquiv.trans_apply,
    CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour_apply]
  exact coe_realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd_apply _

/-- The inverse compact `Spin(4)` equivalence recovers the Clifford value from the inverse
quaternion-pair algebra model. -/
@[simp]
theorem coe_realSpinFourEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    (realSpinFourEquivQuaternionUnitaryProd.symm q :
        CliffordAlgebra (realCliffordForm 4 0)) =
      (realCliffordFourZeroEvenEquivQuaternionProd.symm
          ((q.1 : ℍ[ℝ]), (q.2 : ℍ[ℝ])) :
        CliffordAlgebra (realCliffordForm 4 0)) := by
  let s := realSpinFourEquivQuaternionUnitaryProd.symm q
  have hs :
      realCliffordFourZeroEvenEquivQuaternionProd
          (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
            (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s)) =
        ((q.1 : ℍ[ℝ]), (q.2 : ℍ[ℝ])) := by
    rw [← coe_realSpinFourEquivQuaternionUnitaryProd_apply]
    exact congrArg (fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] =>
      ((p.1 : ℍ[ℝ]), (p.2 : ℍ[ℝ])))
        (realSpinFourEquivQuaternionUnitaryProd.apply_symm_apply q)
  have h := congrArg
    (fun x : CliffordAlgebra.even (realCliffordForm 4 0) =>
      (x : CliffordAlgebra (realCliffordForm 4 0)))
    ((realCliffordFourZeroEvenEquivQuaternionProd.symm_apply_eq).mpr hs.symm)
  simpa [s] using h.symm

/-- The first quaternion attached to a compact `Spin(4)` element has norm one. -/
theorem normSq_fst_realSpinFourEquivQuaternionUnitaryProd
    (s : spinGroup (realCliffordForm 4 0)) :
    Quaternion.normSq
        ((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]) = (1 : ℝ) :=
  Quaternion.normSq_coe_unitary_eq_one _

/-- The second quaternion attached to a compact `Spin(4)` element has norm one. -/
theorem normSq_snd_realSpinFourEquivQuaternionUnitaryProd
    (s : spinGroup (realCliffordForm 4 0)) :
    Quaternion.normSq
        ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ]) = (1 : ℝ) :=
  Quaternion.normSq_coe_unitary_eq_one _

/-- The compact real form of the exceptional isomorphism in dimension four:
`Spin(4) ≃ SU(2) × SU(2)`. -/
noncomputable def realSpinFourEquivSpecialUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃*
      Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  realSpinFourEquivQuaternionUnitaryProd.trans
    (Quaternion.unitaryEquivSpecialUnitaryGroup.prodCongr
      Quaternion.unitaryEquivSpecialUnitaryGroup)

/-- The two matrices underlying the compact `Spin(4) ≃ SU(2) × SU(2)` equivalence are the complex
matrix models of its two quaternion components. -/
@[simp]
theorem coe_realSpinFourEquivSpecialUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    (((realSpinFourEquivSpecialUnitaryProd s).1 : Matrix (Fin 2) (Fin 2) ℂ),
        ((realSpinFourEquivSpecialUnitaryProd s).2 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (Quaternion.toComplexMatrix (realSpinFourEquivQuaternionUnitaryProd s).1,
        Quaternion.toComplexMatrix (realSpinFourEquivQuaternionUnitaryProd s).2) := by
  apply Prod.ext
  · exact Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply _
  · exact Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply _

/-- The `Spin(4)` element underlying a pair of special unitary matrices has the expected pair of
unit quaternions. -/
theorem toComplexMatrix_coe_realSpinFourEquivQuaternionUnitaryProd_symm_apply
    (M : Matrix.specialUnitaryGroup (Fin 2) ℂ ×
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (Quaternion.toComplexMatrix
        ((realSpinFourEquivQuaternionUnitaryProd
          (realSpinFourEquivSpecialUnitaryProd.symm M)).1 : ℍ[ℝ]),
      Quaternion.toComplexMatrix
        ((realSpinFourEquivQuaternionUnitaryProd
          (realSpinFourEquivSpecialUnitaryProd.symm M)).2 : ℍ[ℝ])) =
      ((M.1 : Matrix (Fin 2) (Fin 2) ℂ),
        (M.2 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [← coe_realSpinFourEquivSpecialUnitaryProd_apply]
  exact congrArg (fun p : Matrix.specialUnitaryGroup (Fin 2) ℂ ×
    Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      ((p.1 : Matrix (Fin 2) (Fin 2) ℂ),
        (p.2 : Matrix (Fin 2) (Fin 2) ℂ)))
    (realSpinFourEquivSpecialUnitaryProd.apply_symm_apply M)

end TauCeti

end
