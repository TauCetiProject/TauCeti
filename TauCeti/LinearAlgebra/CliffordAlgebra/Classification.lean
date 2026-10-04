/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.EightPeriodicity

import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.CentralSimple.Quaternion
import TauCeti.Algebra.CentralSimple.Splitting
import TauCeti.LinearAlgebra.Matrix.TensorProduct
import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Four

/-!
# Classification of real Clifford algebras

The signature recurrences reduce every standard real Clifford algebra to one of eight matrix,
complex, quaternionic, or split matrix models.

## Main results

* `realCliffordResidue` records `(q - p) mod 8` without integer coercions.
* `IsRealCliffordClassified` states the exact algebra in each residue class.
* `realClifford_classification` proves the classification for every signature.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Chapter I.
* [TauCeti SpinRepresentations roadmap, Layer 7](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md#layer-7-real-clifford-algebras-bott-periodicity-and-spinp-q),
  the `(q - p) mod 8` classification-table target.
-/

public section

open scoped Matrix Quaternion TensorProduct

namespace TauCeti

private abbrev C (p q : ℕ) :=
  _root_.CliffordAlgebra (realCliffordForm p q)

/-- The residue `q - p` modulo eight, represented as a natural number in `[0, 8)`. -/
def realCliffordResidue (p q : ℕ) : ℕ :=
  (q + 8 - p % 8) % 8

/-- The real Clifford residue of signature `(p, q)` is the natural-number representative
`(q + 8 - p % 8) % 8` of `q - p` modulo eight, which selects the row of the classification table
for that signature. -/
theorem realCliffordResidue_def (p q : ℕ) : realCliffordResidue p q = (q + 8 - p % 8) % 8 :=
  (rfl)

/-- The real Clifford residue is one of the eight table indices. -/
theorem realCliffordResidue_lt_eight (p q : ℕ) : realCliffordResidue p q < 8 := by
  rw [realCliffordResidue]
  exact Nat.mod_lt _ (by norm_num)

@[simp]
theorem realCliffordResidue_add_add_right (p q n : ℕ) :
    realCliffordResidue (p + n) (q + n) = realCliffordResidue p q := by
  simp only [realCliffordResidue]
  omega

@[simp]
theorem realCliffordResidue_add_eight_left (p q : ℕ) :
    realCliffordResidue (p + 8) q = realCliffordResidue p q := by
  simp only [realCliffordResidue]
  omega

@[simp]
theorem realCliffordResidue_add_eight_right (p q : ℕ) :
    realCliffordResidue p (q + 8) = realCliffordResidue p q := by
  simp only [realCliffordResidue]
  omega

/-- The exact real algebra classification of the standard Clifford algebra of signature `(p,q)`.
The matrix size is stated uniformly in terms of the total dimension. -/
def IsRealCliffordClassified (p q : ℕ) : Prop :=
  match realCliffordResidue p q with
  | 0 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q) / 2))) (Fin (2 ^ ((p + q) / 2))) ℝ)
  | 1 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 1) / 2))) (Fin (2 ^ ((p + q - 1) / 2))) ℂ)
  | 2 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 2) / 2))) (Fin (2 ^ ((p + q - 2) / 2))) ℍ[ℝ])
  | 3 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 3) / 2))) (Fin (2 ^ ((p + q - 3) / 2))) ℍ[ℝ] ×
        Matrix (Fin (2 ^ ((p + q - 3) / 2))) (Fin (2 ^ ((p + q - 3) / 2))) ℍ[ℝ])
  | 4 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 2) / 2))) (Fin (2 ^ ((p + q - 2) / 2))) ℍ[ℝ])
  | 5 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 1) / 2))) (Fin (2 ^ ((p + q - 1) / 2))) ℂ)
  | 6 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q) / 2))) (Fin (2 ^ ((p + q) / 2))) ℝ)
  | 7 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 1) / 2))) (Fin (2 ^ ((p + q - 1) / 2))) ℝ ×
        Matrix (Fin (2 ^ ((p + q - 1) / 2))) (Fin (2 ^ ((p + q - 1) / 2))) ℝ)
  | _ => False

private noncomputable def realCliffordZeroZeroEquiv :
    _root_.CliffordAlgebra (realCliffordForm 0 0) ≃ₐ[ℝ] ℝ := by
  letI : Subsingleton (Fin (0 + 0) → ℝ) :=
    ⟨fun f g ↦ funext fun i ↦ Fin.elim0 i⟩
  exact (CliffordAlgebra.equivOfIsometry
    (QuadraticMap.IsometryEquiv.mk
      (LinearEquiv.ofSubsingleton (Fin (0 + 0) → ℝ) Unit)
      (by
        intro v
        have hv : v = 0 := funext fun i ↦ Fin.elim0 i
        subst v
        simp))).trans
    CliffordAlgebraRing.equiv

private def prodTensorAlgebraEquiv (R A B : Type*) [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] :
    (A × A) ⊗[R] B ≃ₐ[R] (A ⊗[R] B) × (A ⊗[R] B) :=
  (Algebra.TensorProduct.comm R _ _).trans <|
    (Algebra.TensorProduct.prodRight R R B A A).trans <|
    AlgEquiv.prodCongr (Algebra.TensorProduct.comm R B A)
      (Algebra.TensorProduct.comm R B A)

private noncomputable def complexTensorQuaternionEquiv :
    ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := by
  have hdeg : Algebra.deg ℝ ℍ[ℝ] = 2 :=
    Algebra.deg_eq_of_finrank_eq_sq (by rw [Quaternion.finrank_eq_four]; norm_num)
  let e : ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
    Classical.choice <| hdeg ▸
      (Algebra.isSplittingField_of_isSepClosed ℝ ℍ[ℝ] ℂ).nonempty_algEquiv_matrix_deg ..
  exact e.restrictScalars ℝ

private def matrixTensorAlgebraEquiv (R A B : Type*) [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] (m : ℕ) :
    Matrix (Fin m) (Fin m) A ⊗[R] B ≃ₐ[R]
      Matrix (Fin m) (Fin m) (A ⊗[R] B) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : Matrix (Fin m) (Fin m) A ≃ₐ[R] _)
    (Matrix.finOneAlgEquiv R B)).trans <|
  (Matrix.kroneckerTMulFinAlgEquiv m 1 R A B).trans <|
  Matrix.reindexAlgEquiv R _ (finCongr (Nat.mul_one m))

private def flattenMatrixEquiv (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    {m n k : ℕ} (h : m * n = k) :
    Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) A) ≃ₐ[R] Matrix (Fin k) (Fin k) A :=
  (Matrix.compAlgEquiv (Fin m) (Fin n) A R).trans
    (Matrix.reindexAlgEquiv R A (finProdFinEquiv.trans (finCongr h)))

private def matrixTensorByCoefficientEquiv {R A B D : Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Semiring D] [Algebra R A] [Algebra R B] [Algebra R D]
    {n k : ℕ} (m : ℕ) (coeff : A ⊗[R] B ≃ₐ[R] Matrix (Fin n) (Fin n) D) (h : m * n = k) :
    Matrix (Fin m) (Fin m) A ⊗[R] B ≃ₐ[R] Matrix (Fin k) (Fin k) D :=
  (matrixTensorAlgebraEquiv R A B m).trans <|
    coeff.mapMatrix.trans <| flattenMatrixEquiv R D h

private def matrixModelTensorEquiv {R S T A B D : Type*} [CommSemiring R]
    [Semiring S] [Semiring T] [Semiring A] [Semiring B] [Semiring D]
    [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B] [Algebra R D]
    {m n k : ℕ} (step : T ≃ₐ[R] S ⊗[R] B)
    (model : S ≃ₐ[R] Matrix (Fin m) (Fin m) A)
    (coeff : A ⊗[R] B ≃ₐ[R] Matrix (Fin n) (Fin n) D) (h : m * n = k) :
    T ≃ₐ[R] Matrix (Fin k) (Fin k) D :=
  step.trans <| (Algebra.TensorProduct.congr model (AlgEquiv.refl : B ≃ₐ[R] B)).trans <|
    matrixTensorByCoefficientEquiv m coeff h

private def matrixProdModelTensorEquiv {R S T A B D : Type*} [CommSemiring R]
    [Semiring S] [Semiring T] [Semiring A] [Semiring B] [Semiring D]
    [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B] [Algebra R D]
    {m n k : ℕ} (step : T ≃ₐ[R] S ⊗[R] B)
    (model : S ≃ₐ[R]
      Matrix (Fin m) (Fin m) A × Matrix (Fin m) (Fin m) A)
    (coeff : A ⊗[R] B ≃ₐ[R] Matrix (Fin n) (Fin n) D) (h : m * n = k) :
    T ≃ₐ[R] Matrix (Fin k) (Fin k) D × Matrix (Fin k) (Fin k) D :=
  step.trans <| (Algebra.TensorProduct.congr model (AlgEquiv.refl : B ≃ₐ[R] B)).trans <|
    (prodTensorAlgebraEquiv R (Matrix (Fin m) (Fin m) A) B).trans <|
      AlgEquiv.prodCongr (matrixTensorByCoefficientEquiv m coeff h)
        (matrixTensorByCoefficientEquiv m coeff h)

private theorem pow_half_sub_mul_pow (n d s t : ℕ)
    (h : (n - d) / 2 + s = t / 2) :
    2 ^ ((n - d) / 2) * 2 ^ s = 2 ^ (t / 2) := by
  rw [← pow_add, h]

private noncomputable def realCliffordPositiveZeroEquiv :
    C 0 0 ≃ₐ[ℝ] Matrix (Fin 1) (Fin 1) ℝ :=
  realCliffordZeroZeroEquiv.trans
    (Matrix.finOneAlgEquiv ℝ ℝ)

private noncomputable def realCliffordPositiveOneEquiv :
    C 1 0 ≃ₐ[ℝ]
      Matrix (Fin 1) (Fin 1) ℝ × Matrix (Fin 1) (Fin 1) ℝ :=
  realCliffordOneZeroEquivProd.trans <|
    AlgEquiv.prodCongr (Matrix.finOneAlgEquiv ℝ ℝ) (Matrix.finOneAlgEquiv ℝ ℝ)

private noncomputable def realCliffordPositiveTwoEquiv :
    C 2 0 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  (realCliffordSignatureSwitchRecurrenceEquiv 0 0).trans <|
    (Algebra.TensorProduct.congr realCliffordZeroZeroEquiv
      (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans <|
    Algebra.TensorProduct.lid ℝ _

private noncomputable def realCliffordPositiveThreeEquiv :
    C 3 0 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (realCliffordSignatureSwitchRecurrenceEquiv 1 0).trans <|
    (Algebra.TensorProduct.congr realCliffordZeroOneEquivComplex
      (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans <|
    (matrixEquivTensor (Fin 2) ℝ ℂ).symm

private noncomputable def realCliffordPositiveFourEquiv :
    C 4 0 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] :=
  (realCliffordSignatureSwitchRecurrenceEquiv 2 0).trans <|
    (Algebra.TensorProduct.congr realCliffordZeroTwoEquivQuaternion
      (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans <|
    (matrixEquivTensor (Fin 2) ℝ ℍ[ℝ]).symm

private noncomputable def realCliffordZeroThreeEquiv :
    C 0 3 ≃ₐ[ℝ]
      Matrix (Fin 1) (Fin 1) ℍ[ℝ] × Matrix (Fin 1) (Fin 1) ℍ[ℝ] :=
  realCliffordZeroThreeEquivQuaternionProd.trans <|
    AlgEquiv.prodCongr (Matrix.finOneAlgEquiv ℝ ℍ[ℝ])
      (Matrix.finOneAlgEquiv ℝ ℍ[ℝ])

private noncomputable def realCliffordPositiveFiveEquiv :
    C 5 0 ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℍ[ℝ] × Matrix (Fin 2) (Fin 2) ℍ[ℝ] :=
  matrixProdModelTensorEquiv (realCliffordSignatureSwitchRecurrenceEquiv 3 0)
    realCliffordZeroThreeEquiv (matrixEquivTensor (Fin 2) ℝ ℍ[ℝ]).symm (by norm_num)

private noncomputable def realCliffordZeroFourEquiv :
    C 0 4 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] :=
  matrixModelTensorEquiv (realCliffordQuaternionRecurrenceEquiv 0 2)
    realCliffordPositiveTwoEquiv
    ((Algebra.TensorProduct.lid ℝ ℍ[ℝ]).trans (Matrix.finOneAlgEquiv ℝ ℍ[ℝ])) (by norm_num)

private noncomputable def realCliffordPositiveSixEquiv :
    C 6 0 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℍ[ℝ] :=
  matrixModelTensorEquiv (realCliffordSignatureSwitchRecurrenceEquiv 4 0)
    realCliffordZeroFourEquiv (matrixEquivTensor (Fin 2) ℝ ℍ[ℝ]).symm (by norm_num)

private noncomputable def realCliffordZeroFiveEquiv :
    C 0 5 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℂ :=
  matrixModelTensorEquiv (realCliffordQuaternionRecurrenceEquiv 0 3)
    realCliffordPositiveThreeEquiv complexTensorQuaternionEquiv (by norm_num)

private noncomputable def realCliffordPositiveSevenEquiv :
    C 7 0 ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℂ :=
  matrixModelTensorEquiv (realCliffordSignatureSwitchRecurrenceEquiv 5 0)
    realCliffordZeroFiveEquiv (matrixEquivTensor (Fin 2) ℝ ℂ).symm (by norm_num)

/-- Tensoring every model of the table with a real matrix algebra `M_{2^k}(ℝ)`: if `(p, q)` is
classified and `C p' q' ≃ C p q ⊗ M_{2^k}(ℝ)` with the same residue and `2k` more generators, then
`(p', q')` is classified. -/
private theorem IsRealCliffordClassified.of_tensor_matrix {p q p' q' : ℕ} (k : ℕ)
    (h : IsRealCliffordClassified p q)
    (step : C p' q' ≃ₐ[ℝ] C p q ⊗[ℝ] Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ)
    (hres : realCliffordResidue p' q' = realCliffordResidue p q)
    (hdim : p' + q' = p + q + 2 * k) :
    IsRealCliffordClassified p' q' := by
  rw [IsRealCliffordClassified, hres]
  rw [IsRealCliffordClassified] at h
  generalize hr : realCliffordResidue p q = r at h
  have hrlt : r < 8 := hr ▸ realCliffordResidue_lt_eight p q
  have hsize (d : ℕ) (hd : d ≤ p + q) :
      2 ^ ((p + q - d) / 2) * 2 ^ k = 2 ^ ((p' + q' - d) / 2) :=
    pow_half_sub_mul_pow (p + q) d k (p' + q' - d) (by omega)
  interval_cases r <;> simp only at h ⊢
  all_goals obtain ⟨e⟩ := h
  all_goals simp only [realCliffordResidue] at hr
  · exact ⟨matrixModelTensorEquiv step e (matrixEquivTensor _ ℝ ℝ).symm (hsize 0 (by omega))⟩
  · exact ⟨matrixModelTensorEquiv step e (matrixEquivTensor _ ℝ ℂ).symm (hsize 1 (by omega))⟩
  · exact ⟨matrixModelTensorEquiv step e (matrixEquivTensor _ ℝ ℍ[ℝ]).symm (hsize 2 (by omega))⟩
  · exact ⟨matrixProdModelTensorEquiv step e (matrixEquivTensor _ ℝ ℍ[ℝ]).symm
      (hsize 3 (by omega))⟩
  · exact ⟨matrixModelTensorEquiv step e (matrixEquivTensor _ ℝ ℍ[ℝ]).symm (hsize 2 (by omega))⟩
  · exact ⟨matrixModelTensorEquiv step e (matrixEquivTensor _ ℝ ℂ).symm (hsize 1 (by omega))⟩
  · exact ⟨matrixModelTensorEquiv step e (matrixEquivTensor _ ℝ ℝ).symm (hsize 0 (by omega))⟩
  · exact ⟨matrixProdModelTensorEquiv step e (matrixEquivTensor _ ℝ ℝ).symm (hsize 1 (by omega))⟩

private theorem realClifford_positiveAxis_base (p : ℕ) (hp : p < 8) :
    IsRealCliffordClassified p 0 := by
  interval_cases p
  · exact ⟨realCliffordPositiveZeroEquiv⟩
  · exact ⟨realCliffordPositiveOneEquiv⟩
  · exact ⟨realCliffordPositiveTwoEquiv⟩
  · exact ⟨realCliffordPositiveThreeEquiv⟩
  · exact ⟨realCliffordPositiveFourEquiv⟩
  · exact ⟨realCliffordPositiveFiveEquiv⟩
  · exact ⟨realCliffordPositiveSixEquiv⟩
  · exact ⟨realCliffordPositiveSevenEquiv⟩

private theorem realClifford_positiveAxis_classification (p : ℕ) :
    IsRealCliffordClassified p 0 := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
      by_cases hp : p < 8
      · exact realClifford_positiveAxis_base p hp
      · obtain ⟨n, rfl⟩ : ∃ n, p = n + 8 := ⟨p - 8, by omega⟩
        obtain ⟨periodicity⟩ := nonempty_realCliffordEightPeriodicityEquiv n 0
        exact (ih n (by omega)).of_tensor_matrix 4 periodicity (by simp) (by omega)

private theorem realClifford_negativeAxis_classification (q : ℕ) :
    IsRealCliffordClassified 0 q := by
  rcases q with _ | _ | n
  · exact realClifford_positiveAxis_classification 0
  · simp only [IsRealCliffordClassified, realCliffordResidue, zero_add, Nat.reduceAdd,
      Nat.zero_mod, tsub_zero, Nat.reduceMod, Nat.add_one_sub_one, Nat.reduceDiv, Nat.pow_zero]
    exact ⟨realCliffordZeroOneEquivComplex.trans (Matrix.finOneAlgEquiv ℝ ℂ)⟩
  · have prev := realClifford_positiveAxis_classification n
    have hmod : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases hn : n % 8 <;>
      simp only [IsRealCliffordClassified, realCliffordResidue, zero_add, hn, tsub_zero,
        Nat.mod_self, Nat.add_zero, Nat.zero_mod, Nat.add_mod_right, Nat.add_mod, Nat.one_mod,
        Nat.reduceAdd, Nat.reduceMod, Nat.add_one_sub_one, Nat.add_succ_sub_one,
        Nat.mod_succ] at prev ⊢
    all_goals obtain ⟨e⟩ := prev
    · exact ⟨matrixModelTensorEquiv (realCliffordQuaternionRecurrenceEquiv 0 n) e
        ((Algebra.TensorProduct.lid ℝ ℍ[ℝ]).trans (Matrix.finOneAlgEquiv ℝ ℍ[ℝ]))
        (by simpa only [Nat.sub_zero, Nat.reducePow, mul_one, Nat.zero_add] using
          pow_half_sub_mul_pow n 0 0 (n + 1 + 1 - 2) (by omega))⟩
    · exact ⟨matrixProdModelTensorEquiv (realCliffordQuaternionRecurrenceEquiv 0 n) e
        ((Algebra.TensorProduct.lid ℝ ℍ[ℝ]).trans (Matrix.finOneAlgEquiv ℝ ℍ[ℝ]))
        (by simpa only [Nat.reducePow, mul_one, Nat.zero_add] using
          pow_half_sub_mul_pow n 1 0 (n + 1 + 1 - 3) (by omega))⟩
    · exact ⟨matrixModelTensorEquiv (realCliffordQuaternionRecurrenceEquiv 0 n) e
        ((Algebra.TensorProduct.lid ℝ ℍ[ℝ]).trans (Matrix.finOneAlgEquiv ℝ ℍ[ℝ]))
        (by simpa only [Nat.sub_zero, Nat.reducePow, mul_one, Nat.zero_add] using
          pow_half_sub_mul_pow n 0 0 (n + 1 + 1 - 2) (by omega))⟩
    · exact ⟨matrixModelTensorEquiv (realCliffordQuaternionRecurrenceEquiv 0 n) e
        complexTensorQuaternionEquiv
        (by simpa only [Nat.reducePow, Nat.zero_add] using
          pow_half_sub_mul_pow n 1 1 (n + 1) (by omega))⟩
    · exact ⟨matrixModelTensorEquiv (realCliffordQuaternionRecurrenceEquiv 0 n) e
        Quaternion.tensorSelfAlgEquivMatrix
        (by simpa only [Nat.reducePow, Nat.zero_add] using
          pow_half_sub_mul_pow n 2 2 (n + 1 + 1) (by omega))⟩
    · exact ⟨matrixProdModelTensorEquiv (realCliffordQuaternionRecurrenceEquiv 0 n) e
        Quaternion.tensorSelfAlgEquivMatrix
        (by simpa only [Nat.reducePow, Nat.zero_add] using
          pow_half_sub_mul_pow n 3 2 (n + 1) (by omega))⟩
    · exact ⟨matrixModelTensorEquiv (realCliffordQuaternionRecurrenceEquiv 0 n) e
        Quaternion.tensorSelfAlgEquivMatrix
        (by simpa only [Nat.reducePow, Nat.zero_add] using
          pow_half_sub_mul_pow n 2 2 (n + 1 + 1) (by omega))⟩
    · exact ⟨matrixModelTensorEquiv (realCliffordQuaternionRecurrenceEquiv 0 n) e
        complexTensorQuaternionEquiv
        (by simpa only [Nat.reducePow, Nat.zero_add] using
          pow_half_sub_mul_pow n 1 1 (n + 1) (by omega))⟩

private theorem isRealCliffordClassified_add_add_right (p q n : ℕ)
    (h : IsRealCliffordClassified p q) :
    IsRealCliffordClassified (p + n) (q + n) :=
  h.of_tensor_matrix n (realCliffordBottIterEquiv p q n) (realCliffordResidue_add_add_right p q n)
    (by omega)

/-- The real Clifford algebra of every finite signature is the full matrix algebra, complex
matrix algebra, quaternionic matrix algebra, or split algebra prescribed by `(q - p) mod 8`. -/
theorem realClifford_classification (p q : ℕ) :
    IsRealCliffordClassified p q := by
  rcases le_total p q with hpq | hqp
  · have h := isRealCliffordClassified_add_add_right 0 (q - p) p
      (realClifford_negativeAxis_classification (q - p))
    simpa [Nat.sub_add_cancel hpq] using h
  · have h := isRealCliffordClassified_add_add_right (p - q) 0 q
      (realClifford_positiveAxis_classification (p - q))
    simpa [Nat.sub_add_cancel hqp] using h

/-- The residue-zero case of the real Clifford classification table. -/
theorem realClifford_classification_of_residue_eq_zero (p q : ℕ)
    (h : realCliffordResidue p q = 0) :
    Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q) / 2))) (Fin (2 ^ ((p + q) / 2))) ℝ) := by
  simpa only [IsRealCliffordClassified, h] using realClifford_classification p q

/-- The residue-one case of the real Clifford classification table. -/
theorem realClifford_classification_of_residue_eq_one (p q : ℕ)
    (h : realCliffordResidue p q = 1) :
    Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 1) / 2))) (Fin (2 ^ ((p + q - 1) / 2))) ℂ) := by
  simpa only [IsRealCliffordClassified, h] using realClifford_classification p q

/-- The residue-two case of the real Clifford classification table. -/
theorem realClifford_classification_of_residue_eq_two (p q : ℕ)
    (h : realCliffordResidue p q = 2) :
    Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 2) / 2))) (Fin (2 ^ ((p + q - 2) / 2))) ℍ[ℝ]) := by
  simpa only [IsRealCliffordClassified, h] using realClifford_classification p q

/-- The residue-three case of the real Clifford classification table. -/
theorem realClifford_classification_of_residue_eq_three (p q : ℕ)
    (h : realCliffordResidue p q = 3) :
    Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 3) / 2))) (Fin (2 ^ ((p + q - 3) / 2))) ℍ[ℝ] ×
        Matrix (Fin (2 ^ ((p + q - 3) / 2))) (Fin (2 ^ ((p + q - 3) / 2))) ℍ[ℝ]) := by
  simpa only [IsRealCliffordClassified, h] using realClifford_classification p q

/-- The residue-four case of the real Clifford classification table. -/
theorem realClifford_classification_of_residue_eq_four (p q : ℕ)
    (h : realCliffordResidue p q = 4) :
    Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 2) / 2))) (Fin (2 ^ ((p + q - 2) / 2))) ℍ[ℝ]) := by
  simpa only [IsRealCliffordClassified, h] using realClifford_classification p q

/-- The residue-five case of the real Clifford classification table. -/
theorem realClifford_classification_of_residue_eq_five (p q : ℕ)
    (h : realCliffordResidue p q = 5) :
    Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 1) / 2))) (Fin (2 ^ ((p + q - 1) / 2))) ℂ) := by
  simpa only [IsRealCliffordClassified, h] using realClifford_classification p q

/-- The residue-six case of the real Clifford classification table. -/
theorem realClifford_classification_of_residue_eq_six (p q : ℕ)
    (h : realCliffordResidue p q = 6) :
    Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q) / 2))) (Fin (2 ^ ((p + q) / 2))) ℝ) := by
  simpa only [IsRealCliffordClassified, h] using realClifford_classification p q

/-- The residue-seven case of the real Clifford classification table. -/
theorem realClifford_classification_of_residue_eq_seven (p q : ℕ)
    (h : realCliffordResidue p q = 7) :
    Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 1) / 2))) (Fin (2 ^ ((p + q - 1) / 2))) ℝ ×
        Matrix (Fin (2 ^ ((p + q - 1) / 2))) (Fin (2 ^ ((p + q - 1) / 2))) ℝ) := by
  simpa only [IsRealCliffordClassified, h] using realClifford_classification p q

end TauCeti
