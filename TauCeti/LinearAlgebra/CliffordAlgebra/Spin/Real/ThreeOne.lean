/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.ThreeOne
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four

/-!
# The Lorentzian real Spin group in dimension four

The Spin group of the real quadratic form of signature `(3,1)` is `SL₂(ℂ)`. The equivalence is
obtained from the explicit complex matrix model of `Cl⁺(3,1)`: Clifford reversal becomes matrix
adjugation, and the reverse-unitary equation becomes determinant one.

## Main definitions and results

* `TauCeti.realCliffordThreeOneEvenUnitaryEquivSpecialLinear` identifies the even reverse-unitary
  carrier with `SL₂(ℂ)`.
* `TauCeti.realSpinThreeOneEquivSpecialLinear` identifies `Spin(3,1)` with `SL₂(ℂ)`.
* The accompanying coercion theorems expose the forward and inverse maps through
  `TauCeti.realCliffordThreeOneEvenEquivComplexMatrix`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4.
-/

public section

namespace TauCeti

/-- The even reverse-unitary carrier of `Cl⁺(3,1)` is the complex special linear group. -/
noncomputable def realCliffordThreeOneEvenUnitaryEquivSpecialLinear :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 1) ≃*
      Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  CliffordAlgebra.evenUnitaryGroupEquivOfAlgEquiv (realCliffordForm 3 1)
    realCliffordThreeOneEvenEquivComplexMatrix (fun A => A.det = 1)
    Matrix.SpecialLinearGroup.coeMonoidHom Matrix.SpecialLinearGroup.coeMonoidHom_injective
    (fun A hA => ⟨A, hA⟩) (fun _ _ => rfl) Matrix.SpecialLinearGroup.det_coe
    realCliffordThreeOne_reverseEven_mul_self_eq_one_iff_det_eq_one

/-- The even-unitary equivalence evaluates the Lorentzian even-Clifford matrix model. -/
@[simp]
theorem coe_realCliffordThreeOneEvenUnitaryEquivSpecialLinear_apply
    (x : CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 1)) :
    ((realCliffordThreeOneEvenUnitaryEquivSpecialLinear x :
        Matrix.SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      realCliffordThreeOneEvenEquivComplexMatrix
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1) x) := by
  exact CliffordAlgebra.coe_evenUnitaryGroupEquivOfAlgEquiv_apply
    (realCliffordForm 3 1) realCliffordThreeOneEvenEquivComplexMatrix
    (fun A => A.det = 1) Matrix.SpecialLinearGroup.coeMonoidHom
    Matrix.SpecialLinearGroup.coeMonoidHom_injective (fun A hA => ⟨A, hA⟩)
    (fun _ _ => rfl) Matrix.SpecialLinearGroup.det_coe
    realCliffordThreeOne_reverseEven_mul_self_eq_one_iff_det_eq_one x

/-- The inverse even-unitary equivalence is the inverse Lorentzian even-Clifford algebra model. -/
@[simp]
theorem realCliffordThreeOneEvenUnitaryEquivSpecialLinear_symm_apply_evenPart
    (A : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1)
        (realCliffordThreeOneEvenUnitaryEquivSpecialLinear.symm A) =
      realCliffordThreeOneEvenEquivComplexMatrix.symm
        (A : Matrix (Fin 2) (Fin 2) ℂ) := by
  exact CliffordAlgebra.evenUnitaryGroupEquivOfAlgEquiv_symm_apply_evenPart
    (realCliffordForm 3 1) realCliffordThreeOneEvenEquivComplexMatrix
    (fun A => A.det = 1) Matrix.SpecialLinearGroup.coeMonoidHom
    Matrix.SpecialLinearGroup.coeMonoidHom_injective (fun B hB => ⟨B, hB⟩)
    (fun _ _ => rfl) Matrix.SpecialLinearGroup.det_coe
    realCliffordThreeOne_reverseEven_mul_self_eq_one_iff_det_eq_one A

/-- The Lorentzian real Spin group `Spin(3,1)` is `SL₂(ℂ)`. -/
noncomputable def realSpinThreeOneEquivSpecialLinear :
    spinGroup (realCliffordForm 3 1) ≃*
      Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  (CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour
    (realCliffordForm 3 1) (nondegenerate_realCliffordForm 3 1)
    (by norm_num) (by norm_num)).trans
    realCliffordThreeOneEvenUnitaryEquivSpecialLinear

/-- The Lorentzian Spin equivalence evaluates the even-Clifford matrix model on the underlying
Spin element. -/
@[simp]
theorem coe_realSpinThreeOneEquivSpecialLinear_apply
    (s : spinGroup (realCliffordForm 3 1)) :
    ((realSpinThreeOneEquivSpecialLinear s : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      realCliffordThreeOneEvenEquivComplexMatrix
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 1) s)) := by
  rw [realSpinThreeOneEquivSpecialLinear, MulEquiv.trans_apply,
    CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour_apply]
  exact coe_realCliffordThreeOneEvenUnitaryEquivSpecialLinear_apply _

/-- The inverse Lorentzian Spin equivalence recovers the Clifford value by the inverse complex
matrix model. -/
@[simp]
theorem coe_realSpinThreeOneEquivSpecialLinear_symm_apply
    (A : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    ((realSpinThreeOneEquivSpecialLinear.symm A : spinGroup (realCliffordForm 3 1)) :
        CliffordAlgebra (realCliffordForm 3 1)) =
      (realCliffordThreeOneEvenEquivComplexMatrix.symm
        (A : Matrix (Fin 2) (Fin 2) ℂ) : CliffordAlgebra (realCliffordForm 3 1)) := by
  let s := realSpinThreeOneEquivSpecialLinear.symm A
  have hs : realCliffordThreeOneEvenEquivComplexMatrix
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 1) s)) =
      (A : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [← coe_realSpinThreeOneEquivSpecialLinear_apply]
    exact congrArg
      (fun z : Matrix.SpecialLinearGroup (Fin 2) ℂ =>
        (z : Matrix (Fin 2) (Fin 2) ℂ))
      (realSpinThreeOneEquivSpecialLinear.apply_symm_apply A)
  have h := congrArg (fun x : CliffordAlgebra.even (realCliffordForm 3 1) =>
    (x : CliffordAlgebra (realCliffordForm 3 1)))
    ((realCliffordThreeOneEvenEquivComplexMatrix.symm_apply_eq).mpr hs.symm)
  simpa [s] using h.symm

end TauCeti

end
