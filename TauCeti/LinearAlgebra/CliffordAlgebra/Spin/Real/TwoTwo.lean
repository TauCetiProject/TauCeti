/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.TwoTwo
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Bruhat
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut

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
* `TauCeti.realSpinTwoTwoEquivSpecialLinearProd_action` identifies the vector action with
  left and inverse-right matrix multiplication.

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

/-! ### The vector action -/

private abbrev realCliffordFormTwoTwo := realCliffordForm 2 2

private def realCliffordTwoTwoLastVector : Fin 4 → ℝ := Pi.single 3 1

private def realCliffordTwoTwoVectorEven :
    (Fin 4 → ℝ) →ₗ[ℝ] CliffordAlgebra.even realCliffordFormTwoTwo where
  toFun v := (CliffordAlgebra.even.ι realCliffordFormTwoTwo).bilin v
    realCliffordTwoTwoLastVector
  map_add' v w := by simp
  map_smul' r v := by simp

private theorem coe_realCliffordTwoTwoVectorEven (v : Fin 4 → ℝ) :
    (realCliffordTwoTwoVectorEven v : CliffordAlgebra realCliffordFormTwoTwo) =
      CliffordAlgebra.ι realCliffordFormTwoTwo v *
        CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector := rfl

private theorem realCliffordTwoTwoEvenEquivMatrixProd_vectorEven (v : Fin 4 → ℝ) :
    (realCliffordTwoTwoEvenEquivMatrixProd (realCliffordTwoTwoVectorEven v)).1 *
        (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ) =
      realCliffordTwoTwoVectorEquivMatrix v := by
  -- Unfold the private vector embedding so the landed generator formula can rewrite it.
  change (realCliffordTwoTwoEvenEquivMatrixProd
    ((CliffordAlgebra.even.ι realCliffordFormTwoTwo).bilin v
      realCliffordTwoTwoLastVector)).1 *
        (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ) =
        realCliffordTwoTwoVectorEquivMatrix v
  rw [realCliffordTwoTwoEvenEquivMatrixProd_ι]
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [realCliffordTwoTwoLastVector,
    Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

private theorem realCliffordTwoTwoLastVector_sq :
    CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector *
        CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector = -1 := by
  have he : realCliffordFormTwoTwo realCliffordTwoTwoLastVector = -1 := by
    -- Expose both local abbreviations before applying the explicit coordinate formula.
    change realCliffordForm 2 2 (Pi.single 3 1) = -1
    rw [realCliffordForm_two_two_apply]
    norm_num
  rw [CliffordAlgebra.ι_sq_scalar, he, map_neg, map_one]

private theorem realCliffordTwoTwoConjugate_mul
    (x y : CliffordAlgebra realCliffordFormTwoTwo) :
    (-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector * (x * y)) *
        CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector =
      ((-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector * x) *
          CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector) *
        ((-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector * y) *
          CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector) := by
  symm
  calc
    ((-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector * x) *
          CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector) *
        ((-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector * y) *
          CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector) =
      (-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector * x) *
        (CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector *
          -CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector) * y *
        CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector := by
      noncomm_ring
    _ = (-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector * (x * y)) *
        CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector := by
      simp only [mul_neg, realCliffordTwoTwoLastVector_sq, neg_neg, mul_one]
      noncomm_ring

private noncomputable def realCliffordTwoTwoConjugateLastEvenHom :
    CliffordAlgebra.even realCliffordFormTwoTwo →ₐ[ℝ]
      CliffordAlgebra.even realCliffordFormTwoTwo where
  toFun x :=
    ⟨(-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector *
          (x : CliffordAlgebra realCliffordFormTwoTwo)) *
        CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector, by
      rw [← Subalgebra.mem_toSubmodule, CliffordAlgebra.even_toSubmodule]
      have hleft :
          -CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector ∈
            CliffordAlgebra.evenOdd realCliffordFormTwoTwo 1 :=
        Submodule.neg_mem _ (CliffordAlgebra.ι_mem_evenOdd_one _ _)
      have h := SetLike.mul_mem_graded
        (SetLike.mul_mem_graded hleft x.2)
        (CliffordAlgebra.ι_mem_evenOdd_one realCliffordFormTwoTwo
          realCliffordTwoTwoLastVector)
      -- The two odd factors add to even parity, expressed here in the `ZMod 2` grading.
      exact (show (1 + 1 : ZMod 2) = 0 by decide) ▸ (by simpa only [add_zero] using h)⟩
  map_one' := by
    apply Subtype.ext
    -- Expose the private hom's value at one so the last-vector square can rewrite it.
    change (-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector * 1) *
      CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector = 1
    rw [mul_one, neg_mul, realCliffordTwoTwoLastVector_sq, neg_neg]
  map_mul' x y := by
    apply Subtype.ext
    exact realCliffordTwoTwoConjugate_mul (x : CliffordAlgebra realCliffordFormTwoTwo) y
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp [mul_add, add_mul]
  commutes' r := by
    apply Subtype.ext
    -- Expose the scalar in the ambient Clifford algebra to commute it past the last vector.
    change (-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector *
        algebraMap ℝ (CliffordAlgebra realCliffordFormTwoTwo) r) *
      CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector =
        algebraMap ℝ (CliffordAlgebra realCliffordFormTwoTwo) r
    rw [← Algebra.commutes r
      (-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector), mul_assoc,
      neg_mul, realCliffordTwoTwoLastVector_sq, neg_neg]
    simp

private theorem coe_realCliffordTwoTwoConjugateLastEvenHom
    (x : CliffordAlgebra.even realCliffordFormTwoTwo) :
    (realCliffordTwoTwoConjugateLastEvenHom x : CliffordAlgebra realCliffordFormTwoTwo) =
      (-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector *
        (x : CliffordAlgebra realCliffordFormTwoTwo)) *
          CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector := rfl

private noncomputable def realCliffordTwoTwoWeylConjSwap :
    (Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ :=
  (AlgEquiv.ofRingEquiv
      (f := (RingEquiv.prodComm :
        (Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ) ≃+*
          Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ)) (by simp)).trans <|
    AlgEquiv.prodCongr
      (Matrix.GeneralLinearGroup.innerAut (GL2WeylElement ℝ))
      (Matrix.GeneralLinearGroup.innerAut (GL2WeylElement ℝ))

private theorem realCliffordTwoTwoEvenEquivMatrixProd_conjugate_generator
    (m n : Fin 4 → ℝ) :
    realCliffordTwoTwoEvenEquivMatrixProd
        (-((CliffordAlgebra.even.ι realCliffordFormTwoTwo).bilin
            realCliffordTwoTwoLastVector m) *
          (CliffordAlgebra.even.ι realCliffordFormTwoTwo).bilin n
            realCliffordTwoTwoLastVector) =
      ((GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ) *
          (realCliffordTwoTwoEvenEquivMatrixProd
            ((CliffordAlgebra.even.ι realCliffordFormTwoTwo).bilin m n)).2 *
            (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ),
        (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ) *
          (realCliffordTwoTwoEvenEquivMatrixProd
            ((CliffordAlgebra.even.ι realCliffordFormTwoTwo).bilin m n)).1 *
            (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [map_mul, map_neg, realCliffordTwoTwoEvenEquivMatrixProd_ι,
    realCliffordTwoTwoEvenEquivMatrixProd_ι,
    realCliffordTwoTwoEvenEquivMatrixProd_ι]
  apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [realCliffordTwoTwoLastVector,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem realCliffordTwoTwoConjugateLastEvenHom_ι (m n : Fin 4 → ℝ) :
    realCliffordTwoTwoConjugateLastEvenHom
        ((CliffordAlgebra.even.ι realCliffordFormTwoTwo).bilin m n) =
      -((CliffordAlgebra.even.ι realCliffordFormTwoTwo).bilin
          realCliffordTwoTwoLastVector m) *
        (CliffordAlgebra.even.ι realCliffordFormTwoTwo).bilin n
          realCliffordTwoTwoLastVector := by
  apply Subtype.ext
  -- Expose both even bilinear products in the ambient Clifford algebra.
  change (-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector *
      (CliffordAlgebra.ι realCliffordFormTwoTwo m *
        CliffordAlgebra.ι realCliffordFormTwoTwo n)) *
        CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector =
    -(CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector *
      CliffordAlgebra.ι realCliffordFormTwoTwo m) *
      (CliffordAlgebra.ι realCliffordFormTwoTwo n *
        CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector)
  noncomm_ring

private theorem realCliffordTwoTwoWeylConjSwap_apply
    (p : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ) :
    realCliffordTwoTwoWeylConjSwap p =
      ((GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ) * p.2 *
          (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ),
        (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ) * p.1 *
          (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ)) := by
  -- Expose the product swap followed by the two componentwise inner automorphisms.
  change
    (Matrix.GeneralLinearGroup.innerAut (GL2WeylElement ℝ) p.2,
      Matrix.GeneralLinearGroup.innerAut (GL2WeylElement ℝ) p.1) = _
  rw [Matrix.GeneralLinearGroup.innerAut_apply,
    Matrix.GeneralLinearGroup.innerAut_apply, ← Matrix.coe_units_inv,
    gl2WeylElement_inv]

private theorem realCliffordTwoTwoEvenEquivMatrixProd_conjugate
    (x : CliffordAlgebra.even realCliffordFormTwoTwo) :
    realCliffordTwoTwoEvenEquivMatrixProd (realCliffordTwoTwoConjugateLastEvenHom x) =
      realCliffordTwoTwoWeylConjSwap (realCliffordTwoTwoEvenEquivMatrixProd x) := by
  have hhom : realCliffordTwoTwoEvenEquivMatrixProd.toAlgHom.comp
        realCliffordTwoTwoConjugateLastEvenHom =
      realCliffordTwoTwoWeylConjSwap.toAlgHom.comp
        realCliffordTwoTwoEvenEquivMatrixProd.toAlgHom := by
    apply CliffordAlgebra.even.algHom_ext
    rw [CliffordAlgebra.EvenHom.ext_iff]
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro n
    simp only [CliffordAlgebra.EvenHom.compr₂_bilin, LinearMap.compr₂_apply]
    -- Expose evaluation of the two composed homomorphisms on a bilinear generator.
    change realCliffordTwoTwoEvenEquivMatrixProd
        (realCliffordTwoTwoConjugateLastEvenHom
          ((CliffordAlgebra.even.ι realCliffordFormTwoTwo).bilin m n)) =
      realCliffordTwoTwoWeylConjSwap
        (realCliffordTwoTwoEvenEquivMatrixProd
          ((CliffordAlgebra.even.ι realCliffordFormTwoTwo).bilin m n))
    rw [realCliffordTwoTwoConjugateLastEvenHom_ι,
      realCliffordTwoTwoWeylConjSwap_apply]
    exact realCliffordTwoTwoEvenEquivMatrixProd_conjugate_generator m n
  exact DFunLike.congr_fun hhom x

private theorem realCliffordTwoTwoVectorEven_spin_action
    (s : spinGroup realCliffordFormTwoTwo) (v : Fin 4 → ℝ) :
    realCliffordTwoTwoVectorEven (s • v) =
      CliffordAlgebra.evenUnitaryGroupEvenPart realCliffordFormTwoTwo
          (CliffordAlgebra.spinGroupToEvenUnitary realCliffordFormTwoTwo s) *
        realCliffordTwoTwoVectorEven v *
          realCliffordTwoTwoConjugateLastEvenHom
            (CliffordAlgebra.reverseEven realCliffordFormTwoTwo
              (CliffordAlgebra.evenUnitaryGroupEvenPart realCliffordFormTwoTwo
                (CliffordAlgebra.spinGroupToEvenUnitary realCliffordFormTwoTwo s))) := by
  apply Subtype.ext
  rw [coe_realCliffordTwoTwoVectorEven, CliffordAlgebra.spinGroup_smul_apply,
    CliffordAlgebra.ι_spinVectorAction_apply]
  simp only [Subalgebra.coe_mul, coe_realCliffordTwoTwoVectorEven,
    coe_realCliffordTwoTwoConjugateLastEvenHom]
  rw [CliffordAlgebra.coe_evenUnitaryGroupEvenPart,
    CliffordAlgebra.coe_reverseEven_apply,
    CliffordAlgebra.coe_evenUnitaryGroupEvenPart]
  rw [CliffordAlgebra.coe_spinGroupToEvenUnitary_apply]
  -- Expose every private even-part coercion in the ambient Clifford algebra.
  change ((s : CliffordAlgebra realCliffordFormTwoTwo) *
      CliffordAlgebra.ι realCliffordFormTwoTwo v *
        star (s : CliffordAlgebra realCliffordFormTwoTwo)) *
          CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector =
    (s : CliffordAlgebra realCliffordFormTwoTwo) *
      (CliffordAlgebra.ι realCliffordFormTwoTwo v *
        CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector) *
          ((-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector *
              CliffordAlgebra.reverse (s : CliffordAlgebra realCliffordFormTwoTwo)) *
            CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector)
  rw [CliffordAlgebra.reverse_eq_star_of_mem_even
    ⟨(s : CliffordAlgebra realCliffordFormTwoTwo), spinGroup.mem_even s.2⟩]
  symm
  calc
    (s : CliffordAlgebra realCliffordFormTwoTwo) *
          (CliffordAlgebra.ι realCliffordFormTwoTwo v *
            CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector) *
            ((-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector *
                star (s : CliffordAlgebra realCliffordFormTwoTwo)) *
              CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector) =
        (s : CliffordAlgebra realCliffordFormTwoTwo) *
          CliffordAlgebra.ι realCliffordFormTwoTwo v *
          (CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector *
            -CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector) *
          star (s : CliffordAlgebra realCliffordFormTwoTwo) *
          CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector := by
      noncomm_ring
    _ = (s : CliffordAlgebra realCliffordFormTwoTwo) *
        CliffordAlgebra.ι realCliffordFormTwoTwo v *
        star (s : CliffordAlgebra realCliffordFormTwoTwo) *
        CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector := by
      simp only [mul_neg, realCliffordTwoTwoLastVector_sq, neg_neg, mul_one]
    _ = ((s : CliffordAlgebra realCliffordFormTwoTwo) *
        CliffordAlgebra.ι realCliffordFormTwoTwo v *
        star (s : CliffordAlgebra realCliffordFormTwoTwo)) *
        CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector := by
      noncomm_ring

/-- Under `Spin(2,2) ≃ SL₂(ℝ) × SL₂(ℝ)` and the determinant model of the
quadratic space, the Spin vector action is left multiplication by the first factor and inverse-right
multiplication by the second. -/
theorem realSpinTwoTwoEquivSpecialLinearProd_action
    (s : spinGroup (realCliffordForm 2 2)) (v : Fin 4 → ℝ) :
    realCliffordTwoTwoVectorEquivMatrix (s • v) =
      ((realSpinTwoTwoEquivSpecialLinearProd s).1 : Matrix (Fin 2) (Fin 2) ℝ) *
        realCliffordTwoTwoVectorEquivMatrix v *
          (↑((realSpinTwoTwoEquivSpecialLinearProd s).2⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) := by
  let x := CliffordAlgebra.evenUnitaryGroupEvenPart realCliffordFormTwoTwo
    (CliffordAlgebra.spinGroupToEvenUnitary realCliffordFormTwoTwo s)
  have haction := congrArg realCliffordTwoTwoEvenEquivMatrixProd
    (realCliffordTwoTwoVectorEven_spin_action s v)
  have hfst := congrArg Prod.fst haction
  have hmulSwap := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      A * (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ)) hfst
  rw [map_mul, map_mul, realCliffordTwoTwoEvenEquivMatrixProd_conjugate,
    realCliffordTwoTwoEvenEquivMatrixProd_reverseEven] at hmulSwap
  rw [realCliffordTwoTwoEvenEquivMatrixProd_vectorEven (s • v)] at hmulSwap
  simp only [realCliffordTwoTwoWeylConjSwap_apply] at hmulSwap
  have hq := coe_realSpinTwoTwoEquivSpecialLinearProd_apply s
  have hq₁ : ((realSpinTwoTwoEquivSpecialLinearProd s).1 :
      Matrix (Fin 2) (Fin 2) ℝ) = (realCliffordTwoTwoEvenEquivMatrixProd x).1 := by
    simpa only [Prod.fst] using congrArg Prod.fst hq
  have hq₂ : ((realSpinTwoTwoEquivSpecialLinearProd s).2 :
      Matrix (Fin 2) (Fin 2) ℝ) = (realCliffordTwoTwoEvenEquivMatrixProd x).2 := by
    simpa only [Prod.snd] using congrArg Prod.snd hq
  rw [Matrix.SpecialLinearGroup.coe_inv, hq₁, hq₂]
  -- The inverse coercion has become an adjugate; expose that normalized target.
  change realCliffordTwoTwoVectorEquivMatrix (s • v) =
    (realCliffordTwoTwoEvenEquivMatrixProd x).1 *
      realCliffordTwoTwoVectorEquivMatrix v *
        Matrix.adjugate (realCliffordTwoTwoEvenEquivMatrixProd x).2
  calc
    realCliffordTwoTwoVectorEquivMatrix (s • v) =
        ((realCliffordTwoTwoEvenEquivMatrixProd x).1 *
            (realCliffordTwoTwoEvenEquivMatrixProd
              (realCliffordTwoTwoVectorEven v)).1 *
              ((GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ) *
                Matrix.adjugate (realCliffordTwoTwoEvenEquivMatrixProd x).2 *
                  (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ))) *
            (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ) := hmulSwap
    _ = (realCliffordTwoTwoEvenEquivMatrixProd x).1 *
        ((realCliffordTwoTwoEvenEquivMatrixProd
            (realCliffordTwoTwoVectorEven v)).1 *
              (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ)) *
          Matrix.adjugate (realCliffordTwoTwoEvenEquivMatrixProd x).2 := by
      have hW :
          (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ) *
              (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
        simpa only [Units.val_mul, Units.val_one] using
          congrArg Units.val (gl2WeylElement_mul_self ℝ)
      noncomm_ring [hW]
    _ = (realCliffordTwoTwoEvenEquivMatrixProd x).1 *
        realCliffordTwoTwoVectorEquivMatrix v *
          Matrix.adjugate (realCliffordTwoTwoEvenEquivMatrixProd x).2 := by
      rw [realCliffordTwoTwoEvenEquivMatrixProd_vectorEven]

end TauCeti
