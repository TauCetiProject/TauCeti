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
* `TauCeti.realSpinThreeOneEquivSpecialLinear_action` identifies the vector action with Hermitian
  congruence.

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

/-! ### The vector action -/

private abbrev realCliffordFormThreeOne := realCliffordForm 3 1

private def realCliffordThreeOneLastVector : Fin 4 → ℝ := Pi.single 3 1

private def realCliffordThreeOneVectorEven :
    (Fin 4 → ℝ) →ₗ[ℝ] CliffordAlgebra.even realCliffordFormThreeOne where
  toFun v := -((CliffordAlgebra.even.ι realCliffordFormThreeOne).bilin v
    realCliffordThreeOneLastVector)
  map_add' v w := by simp [add_comm]
  map_smul' r v := by simp

private theorem coe_realCliffordThreeOneVectorEven (v : Fin 4 → ℝ) :
    (realCliffordThreeOneVectorEven v : CliffordAlgebra realCliffordFormThreeOne) =
      -(CliffordAlgebra.ι realCliffordFormThreeOne v *
        CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector) :=
  rfl

private theorem realCliffordThreeOneEvenEquivComplexMatrix_vectorEven (v : Fin 4 → ℝ) :
    realCliffordThreeOneEvenEquivComplexMatrix (realCliffordThreeOneVectorEven v) =
      (realCliffordThreeOneVectorEquivHermitian v : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [show realCliffordThreeOneVectorEven v =
      -((CliffordAlgebra.even.ι realCliffordFormThreeOne).bilin v
        realCliffordThreeOneLastVector) from rfl,
    map_neg, realCliffordThreeOneEvenEquivComplexMatrix_ι,
    coe_realCliffordThreeOneVectorEquivHermitian_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realCliffordThreeOneLastVector] <;> ring

private theorem realCliffordThreeOneLastVector_sq :
    CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector *
        CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector = -1 := by
  have he : realCliffordFormThreeOne realCliffordThreeOneLastVector = -1 := by
    change realCliffordForm 3 1 (Pi.single 3 1) = -1
    simp [realCliffordForm_three_one_apply]
  rw [CliffordAlgebra.ι_sq_scalar, he, map_neg, map_one]

private def realCliffordThreeOneLastVectorUnit :
    (CliffordAlgebra realCliffordFormThreeOne)ˣ where
  val := -CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector
  inv := CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector
  val_inv := by
    rw [neg_mul, realCliffordThreeOneLastVector_sq, neg_neg]
  inv_val := by
    rw [mul_neg, realCliffordThreeOneLastVector_sq, neg_neg]

private noncomputable def realCliffordThreeOneConjugateLast :
    CliffordAlgebra realCliffordFormThreeOne ≃ₐ[ℝ]
      CliffordAlgebra realCliffordFormThreeOne :=
  MulSemiringAction.toAlgEquiv ℝ _
    (ConjAct.toConjAct realCliffordThreeOneLastVectorUnit)

private theorem realCliffordThreeOneConjugateLast_apply
    (x : CliffordAlgebra realCliffordFormThreeOne) :
    realCliffordThreeOneConjugateLast x =
      (-CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector * x) *
        CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector := by
  simp [realCliffordThreeOneConjugateLast,
    realCliffordThreeOneLastVectorUnit, ConjAct.units_smul_def]

private noncomputable def realCliffordThreeOneConjugateLastEvenHom :
    CliffordAlgebra.even realCliffordFormThreeOne →ₐ[ℝ]
      CliffordAlgebra.even realCliffordFormThreeOne where
  toFun x :=
    ⟨realCliffordThreeOneConjugateLast
        (x : CliffordAlgebra realCliffordFormThreeOne), by
      rw [realCliffordThreeOneConjugateLast_apply]
      rw [← Subalgebra.mem_toSubmodule, CliffordAlgebra.even_toSubmodule]
      have hleft :
          -CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector ∈
            CliffordAlgebra.evenOdd realCliffordFormThreeOne 1 :=
        Submodule.neg_mem _ (CliffordAlgebra.ι_mem_evenOdd_one _ _)
      have h := SetLike.mul_mem_graded (SetLike.mul_mem_graded hleft x.2)
        (CliffordAlgebra.ι_mem_evenOdd_one realCliffordFormThreeOne
          realCliffordThreeOneLastVector)
      exact (show (1 + 1 : ZMod 2) = 0 by decide) ▸ (by simpa only [add_zero] using h)⟩
  map_one' := Subtype.ext (map_one realCliffordThreeOneConjugateLast)
  map_mul' x y := Subtype.ext (map_mul realCliffordThreeOneConjugateLast
    (x : CliffordAlgebra realCliffordFormThreeOne) y)
  map_zero' := Subtype.ext (map_zero realCliffordThreeOneConjugateLast)
  map_add' x y := Subtype.ext (map_add realCliffordThreeOneConjugateLast
    (x : CliffordAlgebra realCliffordFormThreeOne) y)
  commutes' r := Subtype.ext (AlgEquiv.commutes realCliffordThreeOneConjugateLast r)

private theorem coe_realCliffordThreeOneConjugateLastEvenHom
    (x : CliffordAlgebra.even realCliffordFormThreeOne) :
    (realCliffordThreeOneConjugateLastEvenHom x :
        CliffordAlgebra realCliffordFormThreeOne) =
      (-CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector *
        (x : CliffordAlgebra realCliffordFormThreeOne)) *
          CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector :=
  realCliffordThreeOneConjugateLast_apply x

private noncomputable def realCliffordThreeOneStarAdjugateHom :
    Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun A := star (Matrix.adjugate A)
  map_zero' := by
    rw [← Matrix.adjugateFinTwoLinearMap_apply, map_zero, star_zero]
  map_add' A B := by
    rw [← Matrix.adjugateFinTwoLinearMap_apply, map_add,
      Matrix.adjugateFinTwoLinearMap_apply, Matrix.adjugateFinTwoLinearMap_apply, star_add]
  map_one' := by simp
  map_mul' A B := by simp [Matrix.adjugate_mul_distrib, star_mul]
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.algebraMap_eq_smul_one] <;> ring

private theorem realCliffordThreeOneStarAdjugateHom_apply
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    realCliffordThreeOneStarAdjugateHom A = star (Matrix.adjugate A) :=
  rfl

private theorem realCliffordThreeOneConjugateLastEvenHom_ι (m n : Fin 4 → ℝ) :
    realCliffordThreeOneConjugateLastEvenHom
        ((CliffordAlgebra.even.ι realCliffordFormThreeOne).bilin m n) =
      -((CliffordAlgebra.even.ι realCliffordFormThreeOne).bilin
          realCliffordThreeOneLastVector m) *
        (CliffordAlgebra.even.ι realCliffordFormThreeOne).bilin n
          realCliffordThreeOneLastVector := by
  apply Subtype.ext
  change (-CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector *
      (CliffordAlgebra.ι realCliffordFormThreeOne m *
        CliffordAlgebra.ι realCliffordFormThreeOne n)) *
        CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector =
    -(CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector *
      CliffordAlgebra.ι realCliffordFormThreeOne m) *
      (CliffordAlgebra.ι realCliffordFormThreeOne n *
        CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector)
  noncomm_ring

private theorem realCliffordThreeOneEvenEquivComplexMatrix_conjugate_generator
    (m n : Fin 4 → ℝ) :
    realCliffordThreeOneEvenEquivComplexMatrix
        (-((CliffordAlgebra.even.ι realCliffordFormThreeOne).bilin
            realCliffordThreeOneLastVector m) *
          (CliffordAlgebra.even.ι realCliffordFormThreeOne).bilin n
            realCliffordThreeOneLastVector) =
      star (Matrix.adjugate
        (realCliffordThreeOneEvenEquivComplexMatrix
          ((CliffordAlgebra.even.ι realCliffordFormThreeOne).bilin m n))) := by
  rw [map_mul, map_neg, realCliffordThreeOneEvenEquivComplexMatrix_ι,
    realCliffordThreeOneEvenEquivComplexMatrix_ι,
    realCliffordThreeOneEvenEquivComplexMatrix_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realCliffordThreeOneLastVector, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem realCliffordThreeOneEvenEquivComplexMatrix_conjugate
    (x : CliffordAlgebra.even realCliffordFormThreeOne) :
    realCliffordThreeOneEvenEquivComplexMatrix
        (realCliffordThreeOneConjugateLastEvenHom x) =
      star (Matrix.adjugate (realCliffordThreeOneEvenEquivComplexMatrix x)) := by
  have hhom : realCliffordThreeOneEvenEquivComplexMatrix.toAlgHom.comp
        realCliffordThreeOneConjugateLastEvenHom =
      realCliffordThreeOneStarAdjugateHom.comp
        realCliffordThreeOneEvenEquivComplexMatrix.toAlgHom := by
    apply CliffordAlgebra.even.algHom_ext
    rw [CliffordAlgebra.EvenHom.ext_iff]
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro n
    simp only [CliffordAlgebra.EvenHom.compr₂_bilin, LinearMap.compr₂_apply]
    change realCliffordThreeOneEvenEquivComplexMatrix
        (realCliffordThreeOneConjugateLastEvenHom
          ((CliffordAlgebra.even.ι realCliffordFormThreeOne).bilin m n)) =
      realCliffordThreeOneStarAdjugateHom
        (realCliffordThreeOneEvenEquivComplexMatrix
          ((CliffordAlgebra.even.ι realCliffordFormThreeOne).bilin m n))
    rw [realCliffordThreeOneConjugateLastEvenHom_ι,
      realCliffordThreeOneStarAdjugateHom_apply]
    exact realCliffordThreeOneEvenEquivComplexMatrix_conjugate_generator m n
  exact DFunLike.congr_fun hhom x

private theorem realCliffordThreeOneVectorEven_spin_action
    (s : spinGroup realCliffordFormThreeOne) (v : Fin 4 → ℝ) :
    realCliffordThreeOneVectorEven (s • v) =
      CliffordAlgebra.evenUnitaryGroupEvenPart realCliffordFormThreeOne
          (CliffordAlgebra.spinGroupToEvenUnitary realCliffordFormThreeOne s) *
        realCliffordThreeOneVectorEven v *
          realCliffordThreeOneConjugateLastEvenHom
            (CliffordAlgebra.reverseEven realCliffordFormThreeOne
              (CliffordAlgebra.evenUnitaryGroupEvenPart realCliffordFormThreeOne
                (CliffordAlgebra.spinGroupToEvenUnitary realCliffordFormThreeOne s))) := by
  apply Subtype.ext
  rw [coe_realCliffordThreeOneVectorEven, CliffordAlgebra.spinGroup_smul_apply,
    CliffordAlgebra.ι_spinVectorAction_apply]
  simp only [Subalgebra.coe_mul, coe_realCliffordThreeOneVectorEven,
    coe_realCliffordThreeOneConjugateLastEvenHom]
  rw [CliffordAlgebra.coe_evenUnitaryGroupEvenPart,
    CliffordAlgebra.coe_reverseEven_apply,
    CliffordAlgebra.coe_evenUnitaryGroupEvenPart,
    CliffordAlgebra.coe_spinGroupToEvenUnitary_apply]
  change -((s : CliffordAlgebra realCliffordFormThreeOne) *
      CliffordAlgebra.ι realCliffordFormThreeOne v *
      star (s : CliffordAlgebra realCliffordFormThreeOne) *
      CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector) =
    (s : CliffordAlgebra realCliffordFormThreeOne) *
      -(CliffordAlgebra.ι realCliffordFormThreeOne v *
        CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector) *
        ((-CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector *
            CliffordAlgebra.reverse (s : CliffordAlgebra realCliffordFormThreeOne)) *
          CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector)
  rw [CliffordAlgebra.reverse_eq_star_of_mem_even
    ⟨(s : CliffordAlgebra realCliffordFormThreeOne), spinGroup.mem_even s.2⟩]
  symm
  calc
    (s : CliffordAlgebra realCliffordFormThreeOne) *
        -(CliffordAlgebra.ι realCliffordFormThreeOne v *
          CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector) *
          ((-CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector *
              star (s : CliffordAlgebra realCliffordFormThreeOne)) *
            CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector) =
      (s : CliffordAlgebra realCliffordFormThreeOne) *
        CliffordAlgebra.ι realCliffordFormThreeOne v *
        (CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector *
          CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector) *
        star (s : CliffordAlgebra realCliffordFormThreeOne) *
        CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector := by
      noncomm_ring
    _ = -((s : CliffordAlgebra realCliffordFormThreeOne) *
        CliffordAlgebra.ι realCliffordFormThreeOne v *
        star (s : CliffordAlgebra realCliffordFormThreeOne) *
        CliffordAlgebra.ι realCliffordFormThreeOne realCliffordThreeOneLastVector) := by
      rw [realCliffordThreeOneLastVector_sq]
      simp

/-- Under `Spin(3,1) ≃ SL₂(ℂ)` and the Hermitian-matrix model of Lorentz four-space, the
Spin vector action is Hermitian congruence `X ↦ A X Aᴴ`. -/
theorem realSpinThreeOneEquivSpecialLinear_action
    (s : spinGroup (realCliffordForm 3 1)) (v : Fin 4 → ℝ) :
    (realCliffordThreeOneVectorEquivHermitian (s • v) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((realSpinThreeOneEquivSpecialLinear s : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) *
        (realCliffordThreeOneVectorEquivHermitian v : Matrix (Fin 2) (Fin 2) ℂ) *
          star ((realSpinThreeOneEquivSpecialLinear s :
            Matrix.SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  let x := CliffordAlgebra.evenUnitaryGroupEvenPart realCliffordFormThreeOne
    (CliffordAlgebra.spinGroupToEvenUnitary realCliffordFormThreeOne s)
  have haction := congrArg realCliffordThreeOneEvenEquivComplexMatrix
    (realCliffordThreeOneVectorEven_spin_action s v)
  rw [map_mul, map_mul, realCliffordThreeOneEvenEquivComplexMatrix_conjugate,
    realCliffordThreeOneEvenEquivComplexMatrix_reverseEven,
    realCliffordThreeOneEvenEquivComplexMatrix_vectorEven,
    realCliffordThreeOneEvenEquivComplexMatrix_vectorEven] at haction
  have hdouble (A : Matrix (Fin 2) (Fin 2) ℂ) :
      Matrix.adjugate (Matrix.adjugate A) = A := by
    simpa using Matrix.adjugate_adjugate A (by norm_num)
  rw [hdouble] at haction
  have hq := coe_realSpinThreeOneEquivSpecialLinear_apply s
  change ((realSpinThreeOneEquivSpecialLinear s : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = realCliffordThreeOneEvenEquivComplexMatrix x at hq
  rw [hq]
  exact haction

end TauCeti

end
