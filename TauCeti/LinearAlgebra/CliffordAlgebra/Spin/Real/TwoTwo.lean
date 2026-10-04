/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.TwoTwo
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four

/-!
# The split real Spin group in dimension four

The Spin group of the split quadratic form of signature `(2,2)` is the product of two copies of
`SL₂(ℝ)`. The equivalence is obtained from the explicit matrix-product model of `Cl⁺(2,2)`:
Clifford reversal becomes componentwise matrix adjugation, and the reverse-unitary equation becomes
determinant one in both factors.

## Main definitions and results

* `TauCeti.realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd` identifies the even unitary
  carrier with `SL₂(ℝ) × SL₂(ℝ)`.
* `TauCeti.realSpinTwoTwoEquivSpecialLinearProd` identifies `Spin(2,2)` with
  `SL₂(ℝ) × SL₂(ℝ)`.
* The accompanying coercion theorems expose the forward and inverse maps through
  `TauCeti.realCliffordTwoTwoEvenEquivMatrixProd`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4.
-/

public section

namespace TauCeti

private def specialLinearProdToMatrixProd :
    Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ →*
      Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ where
  toFun q := ((q.1 : Matrix (Fin 2) (Fin 2) ℝ), (q.2 : Matrix (Fin 2) (Fin 2) ℝ))
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem specialLinearProdToMatrixProd_injective :
    Function.Injective specialLinearProdToMatrixProd := by
  rintro ⟨A, B⟩ ⟨C, D⟩ h
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- The even reverse-unitary carrier of `Cl⁺(2,2)` is the product of two real special linear
groups. -/
noncomputable def realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 2 2) ≃*
      Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  CliffordAlgebra.evenUnitaryGroupEquivOfAlgEquiv (realCliffordForm 2 2)
    realCliffordTwoTwoEvenEquivMatrixProd (fun y => y.1.det = 1 ∧ y.2.det = 1)
    specialLinearProdToMatrixProd specialLinearProdToMatrixProd_injective
    (fun y hy => (⟨y.1, hy.1⟩, ⟨y.2, hy.2⟩)) (fun _ _ => rfl)
    (fun q => ⟨q.1.det_coe, q.2.det_coe⟩)
    realCliffordTwoTwo_reverseEven_mul_self_eq_one_iff_det_eq_one

/-- The even-unitary equivalence evaluates the split even-Clifford algebra model. -/
@[simp]
theorem coe_realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd_apply
    (x : CliffordAlgebra.evenUnitaryGroup (realCliffordForm 2 2)) :
    (((realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd x).1 :
        Matrix (Fin 2) (Fin 2) ℝ),
      ((realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd x).2 :
        Matrix (Fin 2) (Fin 2) ℝ)) =
      realCliffordTwoTwoEvenEquivMatrixProd
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) x) := by
  exact CliffordAlgebra.coe_evenUnitaryGroupEquivOfAlgEquiv_apply
    (realCliffordForm 2 2) realCliffordTwoTwoEvenEquivMatrixProd
    (fun y => y.1.det = 1 ∧ y.2.det = 1) specialLinearProdToMatrixProd
    specialLinearProdToMatrixProd_injective (fun y hy => (⟨y.1, hy.1⟩, ⟨y.2, hy.2⟩))
    (fun _ _ => rfl) (fun q => ⟨q.1.det_coe, q.2.det_coe⟩)
    realCliffordTwoTwo_reverseEven_mul_self_eq_one_iff_det_eq_one x

/-- The inverse even-unitary equivalence is the inverse split even-Clifford algebra model. -/
@[simp]
theorem realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd_symm_apply_evenPart
    (q : Matrix.SpecialLinearGroup (Fin 2) ℝ ×
      Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2)
        (realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd.symm q) =
      realCliffordTwoTwoEvenEquivMatrixProd.symm
        ((q.1 : Matrix (Fin 2) (Fin 2) ℝ), (q.2 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  exact CliffordAlgebra.evenUnitaryGroupEquivOfAlgEquiv_symm_apply_evenPart
    (realCliffordForm 2 2) realCliffordTwoTwoEvenEquivMatrixProd
    (fun y => y.1.det = 1 ∧ y.2.det = 1) specialLinearProdToMatrixProd
    specialLinearProdToMatrixProd_injective (fun y hy => (⟨y.1, hy.1⟩, ⟨y.2, hy.2⟩))
    (fun _ _ => rfl) (fun p => ⟨p.1.det_coe, p.2.det_coe⟩)
    realCliffordTwoTwo_reverseEven_mul_self_eq_one_iff_det_eq_one q

/-- The split real Spin group `Spin(2,2)` is `SL₂(ℝ) × SL₂(ℝ)`. -/
noncomputable def realSpinTwoTwoEquivSpecialLinearProd :
    spinGroup (realCliffordForm 2 2) ≃*
      Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  (CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour
    (realCliffordForm 2 2) (nondegenerate_realCliffordForm 2 2)
    (by norm_num) (by norm_num)).trans
    realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd

/-- The split `Spin(2,2)` equivalence evaluates the even-Clifford matrix-product model on the
underlying Spin element. -/
@[simp]
theorem coe_realSpinTwoTwoEquivSpecialLinearProd_apply
    (s : spinGroup (realCliffordForm 2 2)) :
    (((realSpinTwoTwoEquivSpecialLinearProd s).1 : Matrix (Fin 2) (Fin 2) ℝ),
      ((realSpinTwoTwoEquivSpecialLinearProd s).2 : Matrix (Fin 2) (Fin 2) ℝ)) =
      realCliffordTwoTwoEvenEquivMatrixProd
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 2 2) s)) := by
  rw [realSpinTwoTwoEquivSpecialLinearProd, MulEquiv.trans_apply,
    CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour_apply]
  exact coe_realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd_apply _

/-- The inverse split `Spin(2,2)` equivalence recovers the Clifford value by the inverse
matrix-product model. -/
@[simp]
theorem coe_realSpinTwoTwoEquivSpecialLinearProd_symm_apply
    (q : Matrix.SpecialLinearGroup (Fin 2) ℝ ×
      Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ((realSpinTwoTwoEquivSpecialLinearProd.symm q : spinGroup (realCliffordForm 2 2)) :
        CliffordAlgebra (realCliffordForm 2 2)) =
      (realCliffordTwoTwoEvenEquivMatrixProd.symm
        ((q.1 : Matrix (Fin 2) (Fin 2) ℝ), (q.2 : Matrix (Fin 2) (Fin 2) ℝ)) :
          CliffordAlgebra (realCliffordForm 2 2)) := by
  let s := realSpinTwoTwoEquivSpecialLinearProd.symm q
  have hs : realCliffordTwoTwoEvenEquivMatrixProd
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 2 2) s)) =
      ((q.1 : Matrix (Fin 2) (Fin 2) ℝ), (q.2 : Matrix (Fin 2) (Fin 2) ℝ)) := by
    rw [← coe_realSpinTwoTwoEquivSpecialLinearProd_apply]
    exact congrArg
      (fun z : Matrix.SpecialLinearGroup (Fin 2) ℝ ×
          Matrix.SpecialLinearGroup (Fin 2) ℝ =>
        ((z.1 : Matrix (Fin 2) (Fin 2) ℝ), (z.2 : Matrix (Fin 2) (Fin 2) ℝ)))
      (realSpinTwoTwoEquivSpecialLinearProd.apply_symm_apply q)
  have h := congrArg (fun x : CliffordAlgebra.even (realCliffordForm 2 2) =>
    (x : CliffordAlgebra (realCliffordForm 2 2)))
    ((realCliffordTwoTwoEvenEquivMatrixProd.symm_apply_eq).mpr hs.symm)
  simpa [s] using h.symm

end TauCeti
