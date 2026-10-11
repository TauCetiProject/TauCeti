/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.TwoOne
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four
import TauCeti.LinearAlgebra.Matrix.Adjugate.FinTwo

/-!
# The split real Spin group in dimension three

The Spin group of the real quadratic form of signature `(2,1)` is `SL₂(ℝ)`. The equivalence is
obtained from the explicit matrix model of `Cl⁺(2,1)`: Clifford reversal becomes matrix
adjugation, and the reverse-unitary equation becomes determinant one.

Under the symmetric-matrix model of the quadratic space, the vector action becomes matrix
congruence `X ↦ A X Aᵀ`. This simultaneously records the group identification, the norm-one
carrier, and the standard double-cover action on the split real three-dimensional form.

## Main definitions and results

* `TauCeti.realCliffordTwoOneEvenUnitaryEquivSpecialLinear` identifies the even reverse-unitary
  carrier with `SL₂(ℝ)`.
* `TauCeti.realSpinTwoOneEquivSpecialLinear` identifies `Spin(2,1)` with `SL₂(ℝ)`.
* The accompanying coercion theorems expose both equivalences through
  `TauCeti.realCliffordTwoOneEvenEquivMatrix`.
* `TauCeti.realSpinTwoOneEquivSpecialLinear_action` identifies the vector action with congruence
  on symmetric matrices.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4.
-/

public section

open scoped Matrix

namespace TauCeti

/-- The even reverse-unitary carrier of `Cl⁺(2,1)` is the real special linear group. -/
noncomputable def realCliffordTwoOneEvenUnitaryEquivSpecialLinear :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 2 1) ≃*
      Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  CliffordAlgebra.evenUnitaryGroupEquivOfAlgEquiv (realCliffordForm 2 1)
    realCliffordTwoOneEvenEquivMatrix (fun A => A.det = 1)
    Matrix.SpecialLinearGroup.coeMonoidHom Matrix.SpecialLinearGroup.coeMonoidHom_injective
    (fun A hA => ⟨A, hA⟩) (fun _ _ => rfl) Matrix.SpecialLinearGroup.det_coe
    realCliffordTwoOne_reverseEven_mul_self_eq_one_iff_det_eq_one

/-- The even-unitary equivalence evaluates the split even-Clifford matrix model. -/
@[simp]
theorem coe_realCliffordTwoOneEvenUnitaryEquivSpecialLinear_apply
    (x : CliffordAlgebra.evenUnitaryGroup (realCliffordForm 2 1)) :
    ((realCliffordTwoOneEvenUnitaryEquivSpecialLinear x :
        Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      realCliffordTwoOneEvenEquivMatrix
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 1) x) := by
  exact CliffordAlgebra.coe_evenUnitaryGroupEquivOfAlgEquiv_apply
    (realCliffordForm 2 1) realCliffordTwoOneEvenEquivMatrix
    (fun A => A.det = 1) Matrix.SpecialLinearGroup.coeMonoidHom
    Matrix.SpecialLinearGroup.coeMonoidHom_injective (fun A hA => ⟨A, hA⟩)
    (fun _ _ => rfl) Matrix.SpecialLinearGroup.det_coe
    realCliffordTwoOne_reverseEven_mul_self_eq_one_iff_det_eq_one x

/-- The inverse even-unitary equivalence is the inverse split even-Clifford algebra model. -/
@[simp]
theorem realCliffordTwoOneEvenUnitaryEquivSpecialLinear_symm_apply_evenPart
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 1)
        (realCliffordTwoOneEvenUnitaryEquivSpecialLinear.symm A) =
      realCliffordTwoOneEvenEquivMatrix.symm
        (A : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact CliffordAlgebra.evenUnitaryGroupEquivOfAlgEquiv_symm_apply_evenPart
    (realCliffordForm 2 1) realCliffordTwoOneEvenEquivMatrix
    (fun B => B.det = 1) Matrix.SpecialLinearGroup.coeMonoidHom
    Matrix.SpecialLinearGroup.coeMonoidHom_injective (fun B hB => ⟨B, hB⟩)
    (fun _ _ => rfl) Matrix.SpecialLinearGroup.det_coe
    realCliffordTwoOne_reverseEven_mul_self_eq_one_iff_det_eq_one A

/-- The split real three-dimensional Spin group `Spin(2,1)` is `SL₂(ℝ)`. -/
noncomputable def realSpinTwoOneEquivSpecialLinear :
    spinGroup (realCliffordForm 2 1) ≃* Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  (CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour
    (realCliffordForm 2 1) (nondegenerate_realCliffordForm 2 1)
    (by norm_num) (by norm_num)).trans
    realCliffordTwoOneEvenUnitaryEquivSpecialLinear

/-- The split `Spin(2,1)` equivalence evaluates the even-Clifford matrix model on the underlying
Spin element. -/
@[simp]
theorem coe_realSpinTwoOneEquivSpecialLinear_apply
    (s : spinGroup (realCliffordForm 2 1)) :
    ((realSpinTwoOneEquivSpecialLinear s : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      realCliffordTwoOneEvenEquivMatrix
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 1)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 2 1) s)) := by
  rw [realSpinTwoOneEquivSpecialLinear, MulEquiv.trans_apply,
    CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour_apply]
  exact coe_realCliffordTwoOneEvenUnitaryEquivSpecialLinear_apply _

/-- The inverse split `Spin(2,1)` equivalence recovers the Clifford value by the inverse matrix
model. -/
@[simp]
theorem coe_realSpinTwoOneEquivSpecialLinear_symm_apply
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ((realSpinTwoOneEquivSpecialLinear.symm A : spinGroup (realCliffordForm 2 1)) :
        CliffordAlgebra (realCliffordForm 2 1)) =
      (realCliffordTwoOneEvenEquivMatrix.symm
        (A : Matrix (Fin 2) (Fin 2) ℝ) :
          CliffordAlgebra (realCliffordForm 2 1)) := by
  let s := realSpinTwoOneEquivSpecialLinear.symm A
  have hs : realCliffordTwoOneEvenEquivMatrix
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 2 1)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 2 1) s)) =
      (A : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [← coe_realSpinTwoOneEquivSpecialLinear_apply]
    exact congrArg
      (fun B : Matrix.SpecialLinearGroup (Fin 2) ℝ =>
        (B : Matrix (Fin 2) (Fin 2) ℝ))
      (realSpinTwoOneEquivSpecialLinear.apply_symm_apply A)
  have h := congrArg (fun x : CliffordAlgebra.even (realCliffordForm 2 1) =>
    (x : CliffordAlgebra (realCliffordForm 2 1)))
    ((realCliffordTwoOneEvenEquivMatrix.symm_apply_eq).mpr hs.symm)
  simpa [s] using h.symm

/-! ### The vector action -/

private abbrev realCliffordFormTwoOne := realCliffordForm 2 1

private def realCliffordTwoOneLastVector : Fin 3 → ℝ := Pi.single 2 1

private theorem realCliffordTwoOneLastVector_negOne :
    realCliffordFormTwoOne realCliffordTwoOneLastVector = -1 := by
  -- Unfold the local abbreviations so the coordinate formula applies directly.
  change realCliffordForm 2 1 (Pi.single 2 1) = -1
  rw [realCliffordForm_apply_single, realCliffordWeight_of_le (by simp), one_pow, mul_one]

private def realCliffordTwoOneVectorEven :
    (Fin 3 → ℝ) →ₗ[ℝ] CliffordAlgebra.even realCliffordFormTwoOne :=
  CliffordAlgebra.rightIotaEven realCliffordFormTwoOne realCliffordTwoOneLastVector

private theorem realCliffordTwoOneEvenEquivMatrix_vectorEven (v : Fin 3 → ℝ) :
    realCliffordTwoOneEvenEquivMatrix (realCliffordTwoOneVectorEven v) =
      (realCliffordTwoOneVectorEquivSymmetric v : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [realCliffordTwoOneVectorEven, CliffordAlgebra.rightIotaEven_apply,
    realCliffordTwoOneEvenEquivMatrix_ι,
    coe_realCliffordTwoOneVectorEquivSymmetric_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realCliffordTwoOneLastVector]
  all_goals ring

private noncomputable def realCliffordTwoOneConjugateLastEvenHom :
    CliffordAlgebra.even realCliffordFormTwoOne →ₐ[ℝ]
      CliffordAlgebra.even realCliffordFormTwoOne :=
  CliffordAlgebra.conjugateNegativeIotaEven realCliffordFormTwoOne
    realCliffordTwoOneLastVector realCliffordTwoOneLastVector_negOne

private theorem realCliffordTwoOneConjugateLastEvenHom_ι (m n : Fin 3 → ℝ) :
    realCliffordTwoOneConjugateLastEvenHom
        ((CliffordAlgebra.even.ι realCliffordFormTwoOne).bilin m n) =
      -((CliffordAlgebra.even.ι realCliffordFormTwoOne).bilin
          realCliffordTwoOneLastVector m) *
        (CliffordAlgebra.even.ι realCliffordFormTwoOne).bilin n
          realCliffordTwoOneLastVector := by
  apply Subtype.ext
  simp only [realCliffordTwoOneConjugateLastEvenHom]
  rw [CliffordAlgebra.coe_conjugateNegativeIotaEven]
  -- Move from the even-subalgebra wrapper to the ambient Clifford product.
  change (-CliffordAlgebra.ι realCliffordFormTwoOne realCliffordTwoOneLastVector *
      (CliffordAlgebra.ι realCliffordFormTwoOne m *
        CliffordAlgebra.ι realCliffordFormTwoOne n)) *
      CliffordAlgebra.ι realCliffordFormTwoOne realCliffordTwoOneLastVector =
    -(CliffordAlgebra.ι realCliffordFormTwoOne realCliffordTwoOneLastVector *
      CliffordAlgebra.ι realCliffordFormTwoOne m) *
      (CliffordAlgebra.ι realCliffordFormTwoOne n *
        CliffordAlgebra.ι realCliffordFormTwoOne realCliffordTwoOneLastVector)
  noncomm_ring

private theorem realCliffordTwoOneEvenEquivMatrix_conjugate_generator
    (m n : Fin 3 → ℝ) :
    realCliffordTwoOneEvenEquivMatrix
        (-((CliffordAlgebra.even.ι realCliffordFormTwoOne).bilin
            realCliffordTwoOneLastVector m) *
          (CliffordAlgebra.even.ι realCliffordFormTwoOne).bilin n
            realCliffordTwoOneLastVector) =
      (Matrix.adjugate (realCliffordTwoOneEvenEquivMatrix
        ((CliffordAlgebra.even.ι realCliffordFormTwoOne).bilin m n)))ᵀ := by
  rw [map_mul, map_neg, realCliffordTwoOneEvenEquivMatrix_ι,
    realCliffordTwoOneEvenEquivMatrix_ι, realCliffordTwoOneEvenEquivMatrix_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realCliffordTwoOneLastVector, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem realCliffordTwoOneEvenEquivMatrix_conjugate
    (x : CliffordAlgebra.even realCliffordFormTwoOne) :
    realCliffordTwoOneEvenEquivMatrix
        (realCliffordTwoOneConjugateLastEvenHom x) =
      (Matrix.adjugate (realCliffordTwoOneEvenEquivMatrix x))ᵀ := by
  -- Package transpose after adjugation as an algebra hom so the even-algebra extensionality
  -- theorem reduces the comparison to generator pairs.
  let transposeAdjugate :
      Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    { toFun := fun A => (Matrix.adjugate A)ᵀ
      map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
      map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
      map_add' := by
        intro A B
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> ring
      map_mul' := by
        intro A B
        rw [Matrix.adjugate_mul_distrib, Matrix.transpose_mul]
      commutes' := by
        intro r
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Algebra.algebraMap_eq_smul_one] <;> ring }
  have hhom : realCliffordTwoOneEvenEquivMatrix.toAlgHom.comp
        realCliffordTwoOneConjugateLastEvenHom =
      transposeAdjugate.comp
        realCliffordTwoOneEvenEquivMatrix.toAlgHom := by
    apply CliffordAlgebra.even.algHom_ext
    rw [CliffordAlgebra.EvenHom.ext_iff]
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro n
    simp only [CliffordAlgebra.EvenHom.compr₂_bilin, LinearMap.compr₂_apply]
    -- Unfold both composed algebra homomorphisms at an even Clifford generator pair.
    change realCliffordTwoOneEvenEquivMatrix
        (realCliffordTwoOneConjugateLastEvenHom
          ((CliffordAlgebra.even.ι realCliffordFormTwoOne).bilin m n)) =
      transposeAdjugate
        (realCliffordTwoOneEvenEquivMatrix
          ((CliffordAlgebra.even.ι realCliffordFormTwoOne).bilin m n))
    rw [realCliffordTwoOneConjugateLastEvenHom_ι]
    exact realCliffordTwoOneEvenEquivMatrix_conjugate_generator m n
  exact DFunLike.congr_fun hhom x

private theorem realCliffordTwoOneVectorEven_spin_action
    (s : spinGroup realCliffordFormTwoOne) (v : Fin 3 → ℝ) :
    realCliffordTwoOneVectorEven (s • v) =
      CliffordAlgebra.evenUnitaryGroupEvenPart realCliffordFormTwoOne
          (CliffordAlgebra.spinGroupToEvenUnitary realCliffordFormTwoOne s) *
        realCliffordTwoOneVectorEven v *
          realCliffordTwoOneConjugateLastEvenHom
            (CliffordAlgebra.reverseEven realCliffordFormTwoOne
              (CliffordAlgebra.evenUnitaryGroupEvenPart realCliffordFormTwoOne
                (CliffordAlgebra.spinGroupToEvenUnitary realCliffordFormTwoOne s))) := by
  exact CliffordAlgebra.rightIotaEven_spinGroup_smul realCliffordFormTwoOne
    realCliffordTwoOneLastVector realCliffordTwoOneLastVector_negOne s v

/-- Under `Spin(2,1) ≃ SL₂(ℝ)` and the symmetric-matrix model of the quadratic space, the Spin
vector action is matrix congruence `X ↦ A X Aᵀ`. -/
theorem realSpinTwoOneEquivSpecialLinear_action
    (s : spinGroup (realCliffordForm 2 1)) (v : Fin 3 → ℝ) :
    (realCliffordTwoOneVectorEquivSymmetric (s • v) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((realSpinTwoOneEquivSpecialLinear s : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        (realCliffordTwoOneVectorEquivSymmetric v : Matrix (Fin 2) (Fin 2) ℝ) *
          (((realSpinTwoOneEquivSpecialLinear s :
            Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))ᵀ := by
  rw [← realCliffordTwoOneEvenEquivMatrix_vectorEven,
    realCliffordTwoOneVectorEven_spin_action, map_mul, map_mul,
    realCliffordTwoOneEvenEquivMatrix_vectorEven,
    realCliffordTwoOneEvenEquivMatrix_conjugate,
    realCliffordTwoOneEvenEquivMatrix_reverseEven,
    coe_realSpinTwoOneEquivSpecialLinear_apply]
  rw [Matrix.adjugate_adjugate _ (by decide)]
  norm_num

end TauCeti

end
