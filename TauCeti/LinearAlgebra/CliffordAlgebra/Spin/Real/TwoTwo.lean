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

private noncomputable def realCliffordTwoTwoEvenUnitaryToSpecialLinearProd :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 2 2) →*
      Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ where
  toFun x := by
    let y := realCliffordTwoTwoEvenEquivMatrixProd
      (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) x)
    have hy : y.1.det = 1 ∧ y.2.det = 1 :=
      (realCliffordTwoTwo_reverseEven_mul_self_eq_one_iff_det_eq_one _).mp
        (CliffordAlgebra.reverseEven_evenUnitaryGroupEvenPart_mul_self
          (realCliffordForm 2 2) x)
    exact (⟨y.1, hy.1⟩, ⟨y.2, hy.2⟩)
  map_one' := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_mul' x y := by
    apply Prod.ext
    · apply Subtype.ext
      -- The private constructor has no public coercion lemma, so expose its first matrix value.
      change (realCliffordTwoTwoEvenEquivMatrixProd
          (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) (x * y))).1 =
        (realCliffordTwoTwoEvenEquivMatrixProd
            (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) x)).1 *
          (realCliffordTwoTwoEvenEquivMatrixProd
            (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) y)).1
      simp
    · apply Subtype.ext
      -- The private constructor has no public coercion lemma, so expose its second matrix value.
      change (realCliffordTwoTwoEvenEquivMatrixProd
          (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) (x * y))).2 =
        (realCliffordTwoTwoEvenEquivMatrixProd
            (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) x)).2 *
          (realCliffordTwoTwoEvenEquivMatrixProd
            (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) y)).2
      simp

private theorem realCliffordTwoTwoEvenUnitaryToSpecialLinearProd_injective :
    Function.Injective realCliffordTwoTwoEvenUnitaryToSpecialLinearProd := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  have he : CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) x =
      CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) y := by
    apply realCliffordTwoTwoEvenEquivMatrixProd.injective
    apply Prod.ext
    · exact congrArg (fun z => (z.1 : Matrix (Fin 2) (Fin 2) ℝ)) hxy
    · exact congrArg (fun z => (z.2 : Matrix (Fin 2) (Fin 2) ℝ)) hxy
  simpa only [CliffordAlgebra.coe_evenUnitaryGroupEvenPart] using congrArg Subtype.val he

private theorem realCliffordTwoTwoEvenUnitaryToSpecialLinearProd_surjective :
    Function.Surjective realCliffordTwoTwoEvenUnitaryToSpecialLinearProd := by
  rintro ⟨A, B⟩
  let y : CliffordAlgebra.even (realCliffordForm 2 2) :=
    realCliffordTwoTwoEvenEquivMatrixProd.symm
      ((A : Matrix (Fin 2) (Fin 2) ℝ), (B : Matrix (Fin 2) (Fin 2) ℝ))
  have hyModel : realCliffordTwoTwoEvenEquivMatrixProd y =
      ((A : Matrix (Fin 2) (Fin 2) ℝ), (B : Matrix (Fin 2) (Fin 2) ℝ)) := by
    exact realCliffordTwoTwoEvenEquivMatrixProd.apply_symm_apply _
  have hy : CliffordAlgebra.reverseEven (realCliffordForm 2 2) y * y = 1 :=
    (realCliffordTwoTwo_reverseEven_mul_self_eq_one_iff_det_eq_one y).mpr (by
      rw [hyModel]
      exact ⟨A.det_coe, B.det_coe⟩)
  have hyr : y * CliffordAlgebra.reverseEven (realCliffordForm 2 2) y = 1 := by
    apply realCliffordTwoTwoEvenEquivMatrixProd.injective
    rw [map_mul, map_one, realCliffordTwoTwoEvenEquivMatrixProd_reverseEven]
    rw [hyModel]
    apply Prod.ext
    -- The transported first coordinate must be exposed before `Matrix.mul_adjugate` applies.
    · change (A : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.adjugate A = 1
      rw [Matrix.mul_adjugate, A.det_coe, one_smul]
    -- The transported second coordinate must be exposed before `Matrix.mul_adjugate` applies.
    · change (B : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.adjugate B = 1
      rw [Matrix.mul_adjugate, B.det_coe, one_smul]
  let u : (CliffordAlgebra (realCliffordForm 2 2))ˣ :=
    { val := y
      inv := CliffordAlgebra.reverseEven (realCliffordForm 2 2) y
      val_inv := congrArg Subtype.val hyr
      inv_val := congrArg Subtype.val hy }
  let z : CliffordAlgebra.evenUnitaryGroup (realCliffordForm 2 2) := by
    refine ⟨u, (CliffordAlgebra.evenUnitaryGroup.mem_iff_reverse_mul_self_eq_one
      (realCliffordForm 2 2)).mpr
      ⟨y.2, ?_⟩⟩
    simpa only [u, CliffordAlgebra.coe_reverseEven_apply, Subalgebra.coe_mul,
      Subalgebra.coe_one] using congrArg Subtype.val hy
  have hzy : CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) z = y := by
    apply Subtype.ext
    rw [CliffordAlgebra.coe_evenUnitaryGroupEvenPart]
  refine ⟨z, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    -- Unfold the private map's first coordinate; no public evaluation lemma exists for it.
    change (realCliffordTwoTwoEvenEquivMatrixProd
      (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) z)).1 =
        (A : Matrix (Fin 2) (Fin 2) ℝ)
    rw [hzy, hyModel]
  · apply Subtype.ext
    -- Unfold the private map's second coordinate; no public evaluation lemma exists for it.
    change (realCliffordTwoTwoEvenEquivMatrixProd
      (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2) z)).2 =
        (B : Matrix (Fin 2) (Fin 2) ℝ)
    rw [hzy, hyModel]

/-- The even reverse-unitary carrier of `Cl⁺(2,2)` is the product of two real special linear
groups. -/
noncomputable def realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 2 2) ≃*
      Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  MulEquiv.ofBijective realCliffordTwoTwoEvenUnitaryToSpecialLinearProd
    ⟨realCliffordTwoTwoEvenUnitaryToSpecialLinearProd_injective,
      realCliffordTwoTwoEvenUnitaryToSpecialLinearProd_surjective⟩

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
  rfl

/-- The inverse even-unitary equivalence is the inverse split even-Clifford algebra model. -/
@[simp]
theorem realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd_symm_apply_evenPart
    (q : Matrix.SpecialLinearGroup (Fin 2) ℝ ×
      Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 2)
        (realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd.symm q) =
      realCliffordTwoTwoEvenEquivMatrixProd.symm
        ((q.1 : Matrix (Fin 2) (Fin 2) ℝ), (q.2 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  apply realCliffordTwoTwoEvenEquivMatrixProd.injective
  rw [AlgEquiv.apply_symm_apply]
  rw [← coe_realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd_apply]
  exact congrArg
    (fun z : Matrix.SpecialLinearGroup (Fin 2) ℝ ×
        Matrix.SpecialLinearGroup (Fin 2) ℝ =>
      ((z.1 : Matrix (Fin 2) (Fin 2) ℝ), (z.2 : Matrix (Fin 2) (Fin 2) ℝ)))
    (realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd.apply_symm_apply q)

private noncomputable def realSpinTwoTwoEquivEvenUnitary :
    spinGroup (realCliffordForm 2 2) ≃*
      CliffordAlgebra.evenUnitaryGroup (realCliffordForm 2 2) :=
  MulEquiv.ofBijective
    (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 2 2))
    ⟨CliffordAlgebra.spinGroupToEvenUnitary_injective (realCliffordForm 2 2),
      fun x => by
        have hx : (x : (CliffordAlgebra (realCliffordForm 2 2))ˣ) ∈
            (spinGroup.toUnits : spinGroup (realCliffordForm 2 2) →*
              (CliffordAlgebra (realCliffordForm 2 2))ˣ).range := by
          rw [CliffordAlgebra.range_spinGroup_toUnits_eq_evenUnitaryGroup_of_finrank_le_four
            (realCliffordForm 2 2) (nondegenerate_realCliffordForm 2 2)
            (by norm_num) (by norm_num)]
          exact x.2
        obtain ⟨s, hs⟩ := hx
        refine ⟨s, Subtype.ext ?_⟩
        simpa only [CliffordAlgebra.coe_spinGroupToEvenUnitary_apply] using hs⟩

/-- The split real Spin group `Spin(2,2)` is `SL₂(ℝ) × SL₂(ℝ)`. -/
noncomputable def realSpinTwoTwoEquivSpecialLinearProd :
    spinGroup (realCliffordForm 2 2) ≃*
      Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  realSpinTwoTwoEquivEvenUnitary.trans
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
