/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Three
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary

/-!
# The compact three-dimensional even unitary carrier

The reversal-preserving algebra equivalence `Cl⁺(3,0) ≃ ℍ` transports the even unitary carrier
to the group of unitary Hamilton quaternions. The general transport mechanism lives in
`CliffordAlgebra.evenUnitaryGroupEquivUnitaryOfAlgEquiv`; this file records its compact
three-dimensional specialization.

## Main definition

* `TauCeti.realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary` identifies the even unitary
  carrier of `Cl(3,0)` with the unitary Hamilton quaternions.

## Reference

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Theorem 3.7 and §4.
-/

public section

open scoped Quaternion

namespace TauCeti

/-- The even unitary carrier of the compact three-dimensional real Clifford algebra is the group
of unitary Hamilton quaternions. -/
noncomputable def realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 0) ≃* unitary ℍ[ℝ] :=
  CliffordAlgebra.evenUnitaryGroupEquivUnitaryOfAlgEquiv
    (realCliffordForm 3 0) realCliffordThreeZeroEvenEquivQuaternion
    realCliffordThreeZeroEvenEquivQuaternion_reverseEven

/-- The quaternion underlying the compact even-unitary equivalence is obtained by applying the
even Clifford-algebra equivalence to the Clifford value. -/
@[simp]
theorem coe_realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary_apply
    (x : CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 0)) :
    (realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary x : ℍ[ℝ]) =
      realCliffordThreeZeroEvenEquivQuaternion
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0) x) := by
  apply CliffordAlgebra.coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_apply

/-- The inverse compact even-unitary equivalence has Clifford value obtained by applying the
inverse even Clifford-algebra equivalence to the quaternion. -/
@[simp]
theorem coe_realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary_symm_apply
    (q : unitary ℍ[ℝ]) :
    ((((realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary.symm q :
        CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 0)) :
          (CliffordAlgebra (realCliffordForm 3 0))ˣ) :
            CliffordAlgebra (realCliffordForm 3 0))) =
      (realCliffordThreeZeroEvenEquivQuaternion.symm (q : ℍ[ℝ]) :
        CliffordAlgebra.even (realCliffordForm 3 0)) := by
  apply CliffordAlgebra.coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_symm_apply

/-- Every quaternion in the image of the compact three-dimensional even unitary carrier has
norm-square one. -/
@[simp]
theorem normSq_realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary_eq_one
    (x : CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 0)) :
    Quaternion.normSq
        (realCliffordThreeZeroEvenEquivQuaternion
          (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0) x)) = 1 := by
  rw [← coe_realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary_apply]
  exact Quaternion.normSq_coe_unitary_eq_one
    (realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary x)

end TauCeti

end
