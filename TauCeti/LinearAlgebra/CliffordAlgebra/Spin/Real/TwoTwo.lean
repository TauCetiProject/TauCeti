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

/-- The even reverse-unitary carrier of `Cl⁺(2,2)` is the product of two real special linear
groups. -/
noncomputable def realCliffordTwoTwoEvenUnitaryEquivSpecialLinearProd :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 2 2) ≃*
      Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  CliffordAlgebra.evenUnitaryGroupEquivOfAlgEquiv (realCliffordForm 2 2)
    realCliffordTwoTwoEvenEquivMatrixProd (fun y => y.1.det = 1 ∧ y.2.det = 1)
    ((Matrix.SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := ℝ)).prodMap
      (Matrix.SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := ℝ)))
    ((Matrix.SpecialLinearGroup.coeMonoidHom_injective (ι := Fin 2) (R := ℝ)).prodMap
      (Matrix.SpecialLinearGroup.coeMonoidHom_injective (ι := Fin 2) (R := ℝ)))
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
    (fun y => y.1.det = 1 ∧ y.2.det = 1)
    ((Matrix.SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := ℝ)).prodMap
      (Matrix.SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := ℝ)))
    ((Matrix.SpecialLinearGroup.coeMonoidHom_injective (ι := Fin 2) (R := ℝ)).prodMap
      (Matrix.SpecialLinearGroup.coeMonoidHom_injective (ι := Fin 2) (R := ℝ)))
    (fun y hy => (⟨y.1, hy.1⟩, ⟨y.2, hy.2⟩))
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
    (fun y => y.1.det = 1 ∧ y.2.det = 1)
    ((Matrix.SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := ℝ)).prodMap
      (Matrix.SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := ℝ)))
    ((Matrix.SpecialLinearGroup.coeMonoidHom_injective (ι := Fin 2) (R := ℝ)).prodMap
      (Matrix.SpecialLinearGroup.coeMonoidHom_injective (ι := Fin 2) (R := ℝ)))
    (fun y hy => (⟨y.1, hy.1⟩, ⟨y.2, hy.2⟩))
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

/-! ### The vector action -/

private abbrev realCliffordFormTwoTwo := realCliffordForm 2 2

private def realCliffordTwoTwoLastVector : Fin 4 → ℝ := Pi.single 3 1

private def realCliffordTwoTwoVectorEven :
    (Fin 4 → ℝ) →ₗ[ℝ] CliffordAlgebra.even realCliffordFormTwoTwo :=
  CliffordAlgebra.rightIotaEven realCliffordFormTwoTwo realCliffordTwoTwoLastVector

private theorem coe_realCliffordTwoTwoVectorEven (v : Fin 4 → ℝ) :
    (realCliffordTwoTwoVectorEven v : CliffordAlgebra realCliffordFormTwoTwo) =
      CliffordAlgebra.ι realCliffordFormTwoTwo v *
        CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector :=
  CliffordAlgebra.coe_rightIotaEven realCliffordFormTwoTwo realCliffordTwoTwoLastVector v

private theorem realCliffordTwoTwoEvenEquivMatrixProd_vectorEven (v : Fin 4 → ℝ) :
    (realCliffordTwoTwoEvenEquivMatrixProd (realCliffordTwoTwoVectorEven v)).1 *
        (GL2WeylElement ℝ : Matrix (Fin 2) (Fin 2) ℝ) =
      realCliffordTwoTwoVectorEquivMatrix v := by
  -- Unfold the private vector embedding so the landed generator formula can rewrite it.
  rw [realCliffordTwoTwoVectorEven, CliffordAlgebra.rightIotaEven_apply]
  rw [realCliffordTwoTwoEvenEquivMatrixProd_ι]
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [realCliffordTwoTwoLastVector,
    Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

private theorem realCliffordTwoTwoLastVector_negOne :
    realCliffordFormTwoTwo realCliffordTwoTwoLastVector = -1 := by
  -- Expose the signature and basis vector so the coordinate formula applies.
  change realCliffordForm 2 2 (Pi.single 3 1) = -1
  rw [realCliffordForm_two_two_apply]
  norm_num

private noncomputable def realCliffordTwoTwoConjugateLastEvenHom :
    CliffordAlgebra.even realCliffordFormTwoTwo →ₐ[ℝ]
      CliffordAlgebra.even realCliffordFormTwoTwo :=
  CliffordAlgebra.conjugateNegativeIotaEven realCliffordFormTwoTwo
    realCliffordTwoTwoLastVector realCliffordTwoTwoLastVector_negOne

private theorem coe_realCliffordTwoTwoConjugateLastEvenHom
    (x : CliffordAlgebra.even realCliffordFormTwoTwo) :
    (realCliffordTwoTwoConjugateLastEvenHom x : CliffordAlgebra realCliffordFormTwoTwo) =
      (-CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector *
        (x : CliffordAlgebra realCliffordFormTwoTwo)) *
          CliffordAlgebra.ι realCliffordFormTwoTwo realCliffordTwoTwoLastVector :=
  CliffordAlgebra.coe_conjugateNegativeIotaEven realCliffordFormTwoTwo
    realCliffordTwoTwoLastVector realCliffordTwoTwoLastVector_negOne x

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
  rw [coe_realCliffordTwoTwoConjugateLastEvenHom]
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
    Matrix.GeneralLinearGroup.innerAut_apply, gl2WeylElement_inv]

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
  simpa [realCliffordTwoTwoVectorEven,
    realCliffordTwoTwoConjugateLastEvenHom] using
    (CliffordAlgebra.rightIotaEven_spinGroup_smul realCliffordFormTwoTwo
      realCliffordTwoTwoLastVector realCliffordTwoTwoLastVector_negOne s v)

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
