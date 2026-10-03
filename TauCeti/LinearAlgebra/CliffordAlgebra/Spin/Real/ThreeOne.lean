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

private noncomputable def realCliffordThreeOneEvenUnitaryToSpecialLinear :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 1) →*
      Matrix.SpecialLinearGroup (Fin 2) ℂ where
  toFun x := by
    let A := realCliffordThreeOneEvenEquivComplexMatrix
      (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1) x)
    have hA : A.det = 1 :=
      (realCliffordThreeOne_reverseEven_mul_self_eq_one_iff_det_eq_one _).mp
        (CliffordAlgebra.reverseEven_evenUnitaryGroupEvenPart_mul_self
          (realCliffordForm 3 1) x)
    exact ⟨A, hA⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    change realCliffordThreeOneEvenEquivComplexMatrix
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1) (x * y)) =
      realCliffordThreeOneEvenEquivComplexMatrix
          (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1) x) *
        realCliffordThreeOneEvenEquivComplexMatrix
          (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1) y)
    simp

private theorem realCliffordThreeOneEvenUnitaryToSpecialLinear_injective :
    Function.Injective realCliffordThreeOneEvenUnitaryToSpecialLinear := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  have he : CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1) x =
      CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1) y := by
    apply realCliffordThreeOneEvenEquivComplexMatrix.injective
    exact congrArg
      (fun z : Matrix.SpecialLinearGroup (Fin 2) ℂ =>
        (z : Matrix (Fin 2) (Fin 2) ℂ)) hxy
  simpa only [CliffordAlgebra.coe_evenUnitaryGroupEvenPart] using congrArg Subtype.val he

private theorem realCliffordThreeOneEvenUnitaryToSpecialLinear_surjective :
    Function.Surjective realCliffordThreeOneEvenUnitaryToSpecialLinear := by
  intro A
  let y : CliffordAlgebra.even (realCliffordForm 3 1) :=
    realCliffordThreeOneEvenEquivComplexMatrix.symm (A : Matrix (Fin 2) (Fin 2) ℂ)
  have hyModel : realCliffordThreeOneEvenEquivComplexMatrix y =
      (A : Matrix (Fin 2) (Fin 2) ℂ) :=
    realCliffordThreeOneEvenEquivComplexMatrix.apply_symm_apply _
  have hy : CliffordAlgebra.reverseEven (realCliffordForm 3 1) y * y = 1 :=
    (realCliffordThreeOne_reverseEven_mul_self_eq_one_iff_det_eq_one y).mpr (by
      rw [hyModel]
      exact A.det_coe)
  have hyr : y * CliffordAlgebra.reverseEven (realCliffordForm 3 1) y = 1 := by
    apply realCliffordThreeOneEvenEquivComplexMatrix.injective
    rw [map_mul, map_one, realCliffordThreeOneEvenEquivComplexMatrix_reverseEven, hyModel]
    rw [Matrix.mul_adjugate, A.det_coe, one_smul]
  let u : (CliffordAlgebra (realCliffordForm 3 1))ˣ :=
    { val := y
      inv := CliffordAlgebra.reverseEven (realCliffordForm 3 1) y
      val_inv := congrArg Subtype.val hyr
      inv_val := congrArg Subtype.val hy }
  let z : CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 1) := by
    refine ⟨u, (CliffordAlgebra.evenUnitaryGroup.mem_iff_reverse_mul_self_eq_one
      (realCliffordForm 3 1)).mpr ⟨y.2, ?_⟩⟩
    simpa only [u, CliffordAlgebra.coe_reverseEven_apply, Subalgebra.coe_mul,
      Subalgebra.coe_one] using congrArg Subtype.val hy
  have hzy : CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1) z = y := by
    apply Subtype.ext
    rw [CliffordAlgebra.coe_evenUnitaryGroupEvenPart]
  refine ⟨z, Subtype.ext ?_⟩
  change realCliffordThreeOneEvenEquivComplexMatrix
      (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1) z) =
    (A : Matrix (Fin 2) (Fin 2) ℂ)
  rw [hzy, hyModel]

/-- The even reverse-unitary carrier of `Cl⁺(3,1)` is the complex special linear group. -/
noncomputable def realCliffordThreeOneEvenUnitaryEquivSpecialLinear :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 1) ≃*
      Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  MulEquiv.ofBijective realCliffordThreeOneEvenUnitaryToSpecialLinear
    ⟨realCliffordThreeOneEvenUnitaryToSpecialLinear_injective,
      realCliffordThreeOneEvenUnitaryToSpecialLinear_surjective⟩

/-- The even-unitary equivalence evaluates the Lorentzian even-Clifford matrix model. -/
@[simp]
theorem coe_realCliffordThreeOneEvenUnitaryEquivSpecialLinear_apply
    (x : CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 1)) :
    ((realCliffordThreeOneEvenUnitaryEquivSpecialLinear x :
        Matrix.SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      realCliffordThreeOneEvenEquivComplexMatrix
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1) x) := by
  rfl

/-- The inverse even-unitary equivalence is the inverse Lorentzian even-Clifford algebra model. -/
@[simp]
theorem realCliffordThreeOneEvenUnitaryEquivSpecialLinear_symm_apply_evenPart
    (A : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 1)
        (realCliffordThreeOneEvenUnitaryEquivSpecialLinear.symm A) =
      realCliffordThreeOneEvenEquivComplexMatrix.symm
        (A : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply realCliffordThreeOneEvenEquivComplexMatrix.injective
  rw [AlgEquiv.apply_symm_apply]
  rw [← coe_realCliffordThreeOneEvenUnitaryEquivSpecialLinear_apply]
  exact congrArg
    (fun z : Matrix.SpecialLinearGroup (Fin 2) ℂ =>
      (z : Matrix (Fin 2) (Fin 2) ℂ))
    (realCliffordThreeOneEvenUnitaryEquivSpecialLinear.apply_symm_apply A)

private noncomputable def realSpinThreeOneEquivEvenUnitary :
    spinGroup (realCliffordForm 3 1) ≃*
      CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 1) :=
  MulEquiv.ofBijective
    (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 1))
    ⟨CliffordAlgebra.spinGroupToEvenUnitary_injective (realCliffordForm 3 1),
      fun x => by
        have hx : (x : (CliffordAlgebra (realCliffordForm 3 1))ˣ) ∈
            (spinGroup.toUnits : spinGroup (realCliffordForm 3 1) →*
              (CliffordAlgebra (realCliffordForm 3 1))ˣ).range := by
          rw [CliffordAlgebra.range_spinGroup_toUnits_eq_evenUnitaryGroup_of_finrank_le_four
            (realCliffordForm 3 1) (nondegenerate_realCliffordForm 3 1)
            (by norm_num) (by norm_num)]
          exact x.2
        obtain ⟨s, hs⟩ := hx
        refine ⟨s, Subtype.ext ?_⟩
        simpa only [CliffordAlgebra.coe_spinGroupToEvenUnitary_apply] using hs⟩

/-- The Lorentzian real Spin group `Spin(3,1)` is `SL₂(ℂ)`. -/
noncomputable def realSpinThreeOneEquivSpecialLinear :
    spinGroup (realCliffordForm 3 1) ≃*
      Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  realSpinThreeOneEquivEvenUnitary.trans
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
