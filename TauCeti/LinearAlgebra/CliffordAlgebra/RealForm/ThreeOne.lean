/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.LinearAlgebra.CliffordAlgebra.BottPeriodicity
public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Scaling
public import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
public import TauCeti.LinearAlgebra.Matrix.Adjugate.FinTwo

/-!
# The Lorentzian four-dimensional real even Clifford algebra

The even Clifford algebra of the real quadratic form of signature `(3,1)` is the algebra of
two-by-two complex matrices. Under this identification, Clifford reversal is matrix adjugation,
so the reverse norm-one equation is exactly the determinant-one equation.

The construction first uses hyperbolic Bott periodicity to identify `Cl(1,2)` with
`Cl(0,1) ⊗ M₂(ℝ) ≃ M₂(ℂ)`. Even-algebra dimension reduction then identifies `Cl⁺(3,1)` with
`Cl(1,2)` and carries reversal to Clifford conjugation.

## Main definitions and results

* `TauCeti.realCliffordOneTwoEquivComplexMatrix` identifies `Cl(1,2)` with `M₂(ℂ)`.
* `TauCeti.realCliffordOneTwoEquivComplexMatrix_star` identifies Clifford conjugation with
  matrix adjugation.
* `TauCeti.realCliffordThreeOneEvenEquivComplexMatrix` identifies `Cl⁺(3,1)` with `M₂(ℂ)`.
* `TauCeti.realCliffordThreeOneEvenEquivComplexMatrix_reverseEven` identifies reversal with
  matrix adjugation.
* `TauCeti.realCliffordThreeOne_reverseEven_mul_self_eq_one_iff_det_eq_one` characterizes the
  reverse-unitary carrier by determinant one.
* `TauCeti.realCliffordThreeOneVectorEquivHermitian` identifies the quadratic space with the
  Hermitian two-by-two complex matrices, carrying the negative quadratic form to the determinant.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4.
* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §8.
-/

public section

open scoped Matrix TensorProduct

namespace TauCeti

/-! ## The quadratic space as Hermitian matrices -/

/-- The real Clifford form of signature `(3,1)` in coordinates. -/
@[simp]
theorem realCliffordForm_three_one_apply (v : Fin 4 → ℝ) :
    realCliffordForm 3 1 v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 - v 3 ^ 2 := by
  rw [realCliffordForm_apply, Fin.sum_univ_four]
  rw [realCliffordWeight_of_lt (p := 3) (q := 1) (i := (0 : Fin 4)) (by decide),
    realCliffordWeight_of_lt (p := 3) (q := 1) (i := (1 : Fin 4)) (by decide),
    realCliffordWeight_of_lt (p := 3) (q := 1) (i := (2 : Fin 4)) (by decide),
    realCliffordWeight_of_le (p := 3) (q := 1) (i := (3 : Fin 4)) (by decide)]
  simp only [one_mul, neg_one_mul]
  ring

private def realCliffordThreeOneVectorMatrix (v : Fin 4 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 3 : ℂ) + v 2, -(v 1 : ℂ) - (v 0 : ℂ) * Complex.I;
     -(v 1 : ℂ) + (v 0 : ℂ) * Complex.I, (v 3 : ℂ) - v 2]

private theorem realCliffordThreeOneVectorMatrix_isHermitian (v : Fin 4 → ℝ) :
    (realCliffordThreeOneVectorMatrix v).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [realCliffordThreeOneVectorMatrix, sub_eq_add_neg]

/-- Lorentz four-space as the real vector space of Hermitian two-by-two complex matrices. The
coordinate convention is compatible with `realCliffordThreeOneEvenEquivComplexMatrix`; the Spin
action becomes Hermitian congruence in `realSpinThreeOneEquivSpecialLinear_action`. -/
noncomputable def realCliffordThreeOneVectorEquivHermitian :
    (Fin 4 → ℝ) ≃ₗ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun v := ⟨realCliffordThreeOneVectorMatrix v, by
    -- Restate subtype membership through the Hermitian predicate proved above.
    change IsSelfAdjoint (realCliffordThreeOneVectorMatrix v)
    exact (realCliffordThreeOneVectorMatrix_isHermitian v).isSelfAdjoint⟩
  invFun A := ![-(A.1 0 1).im, -(A.1 0 1).re,
    ((A.1 0 0).re - (A.1 1 1).re) / 2,
    ((A.1 0 0).re + (A.1 1 1).re) / 2]
  map_add' v w := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realCliffordThreeOneVectorMatrix] <;> ring
  map_smul' r v := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realCliffordThreeOneVectorMatrix] <;> ring
  left_inv v := by
    funext i
    fin_cases i <;> simp [realCliffordThreeOneVectorMatrix]
  right_inv A := by
    have h00 := Matrix.IsHermitian.apply A.2 0 0
    have h01 := Matrix.IsHermitian.apply A.2 1 0
    have h11 := Matrix.IsHermitian.apply A.2 1 1
    have h00im : (A.1 0 0).im = 0 := by
      have h := congrArg Complex.im h00
      simp at h
      linarith
    have h11im : (A.1 1 1).im = 0 := by
      have h := congrArg Complex.im h11
      simp at h
      linarith
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · apply Complex.ext
      · simp [realCliffordThreeOneVectorMatrix]
        ring
      · simp [realCliffordThreeOneVectorMatrix, h00im]
    · apply Complex.ext <;> simp [realCliffordThreeOneVectorMatrix]
    · -- Expose the matrix entry before using Hermitian symmetry across the diagonal.
      change realCliffordThreeOneVectorMatrix _ 1 0 = A.1 1 0
      rw [← h01]
      apply Complex.ext <;> simp [realCliffordThreeOneVectorMatrix]
    · apply Complex.ext
      · simp [realCliffordThreeOneVectorMatrix]
        ring
      · simp [realCliffordThreeOneVectorMatrix, h11im]

/-- The Hermitian matrix coordinates of a Lorentz vector. -/
@[simp]
theorem coe_realCliffordThreeOneVectorEquivHermitian_apply (v : Fin 4 → ℝ) :
    (realCliffordThreeOneVectorEquivHermitian v : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(v 3 : ℂ) + v 2, -(v 1 : ℂ) - (v 0 : ℂ) * Complex.I;
         -(v 1 : ℂ) + (v 0 : ℂ) * Complex.I, (v 3 : ℂ) - v 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The Lorentz-vector coordinates recovered from a Hermitian two-by-two matrix. -/
theorem realCliffordThreeOneVectorEquivHermitian_symm_apply
    (A : selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ)) :
    realCliffordThreeOneVectorEquivHermitian.symm A =
      ![-(A.1 0 1).im, -(A.1 0 1).re,
        ((A.1 0 0).re - (A.1 1 1).re) / 2,
        ((A.1 0 0).re + (A.1 1 1).re) / 2] := by
  funext i
  fin_cases i <;> rfl

/-- The determinant of the Hermitian matrix model is the negative Lorentzian quadratic form. -/
theorem realCliffordThreeOneVectorEquivHermitian_det (v : Fin 4 → ℝ) :
    ((realCliffordThreeOneVectorEquivHermitian v :
      selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ).det = -(realCliffordForm 3 1 v) := by
  rw [coe_realCliffordThreeOneVectorEquivHermitian_apply,
    realCliffordForm_three_one_apply]
  apply Complex.ext <;>
    norm_num [Matrix.det_fin_two, pow_two] <;> ring

/-! ## The even Clifford algebra -/

/-- The Lorentzian algebra model `Cl(1,2) ≃ M₂(ℂ)`. -/
noncomputable def realCliffordOneTwoEquivComplexMatrix :
    CliffordAlgebra (realCliffordForm 1 2) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (realCliffordBottEquiv 0 1).trans <|
    (Algebra.TensorProduct.congr realCliffordZeroOneEquivComplex
      (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans <|
      (matrixEquivTensor (Fin 2) ℝ ℂ).symm

private theorem realBottSplitIsometry_zero_one_apply (v : Fin (1 + 2) → ℝ) :
    realBottSplitIsometry 0 1 v = (![v 1], ![v 0, v 2]) := by
  apply Prod.ext
  · funext i
    fin_cases i
    simpa using realBottSplitIsometry_fst_neg 0 1 v (0 : Fin 1)
  · funext i
    fin_cases i
    · simpa using realBottSplitIsometry_snd_zero 0 1 v
    · simpa using realBottSplitIsometry_snd_one 0 1 v

/-- The matrix coordinates of a generator in the Lorentzian model of `Cl(1,2)`. -/
@[simp]
theorem realCliffordOneTwoEquivComplexMatrix_ι (v : Fin (1 + 2) → ℝ) :
    realCliffordOneTwoEquivComplexMatrix (CliffordAlgebra.ι _ v) =
      !![(v 0 : ℂ), (v 2 : ℂ) + (v 1 : ℂ) * Complex.I;
         -(v 2 : ℂ) + (v 1 : ℂ) * Complex.I, -(v 0 : ℂ)] := by
  simp only [realCliffordOneTwoEquivComplexMatrix, AlgEquiv.trans_apply,
    realCliffordBottEquiv_ι, map_add, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one]
  rw [realBottSplitIsometry_zero_one_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixEquivTensor_apply_symm] <;> ring

private theorem realCliffordOneTwoEquivComplexMatrix_ι_trace
    (v : Fin (1 + 2) → ℝ) :
    (realCliffordOneTwoEquivComplexMatrix (CliffordAlgebra.ι _ v)).trace = 0 := by
  simp [Matrix.trace, Fin.sum_univ_two]

/-- In the complex matrix model of `Cl(1,2)`, Clifford conjugation is matrix adjugation. -/
@[simp]
theorem realCliffordOneTwoEquivComplexMatrix_star
    (x : CliffordAlgebra (realCliffordForm 1 2)) :
    realCliffordOneTwoEquivComplexMatrix (star x) =
      Matrix.adjugate (realCliffordOneTwoEquivComplexMatrix x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Algebra.algebraMap_eq_smul_one,
          Matrix.adjugate_fin_two_eq_trace_smul_one_sub, Matrix.trace] <;> ring
  | ι v =>
      rw [CliffordAlgebra.star_ι, map_neg,
        Matrix.adjugate_fin_two_eq_trace_smul_one_sub,
        realCliffordOneTwoEquivComplexMatrix_ι_trace]
      simp
  | add x y hx hy =>
      simp only [star_add, map_add, hx, hy]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> ring
  | mul x y hx hy =>
      simp only [star_mul, map_mul, hx, hy, Matrix.adjugate_mul_distrib]

private def realCliffordThreeOneAugmentedIsometry :
    (realCliffordForm 3 1).IsometryEquiv
      ((realCliffordForm 2 1).prod
        ((↑(1 : ℝˣ) : ℝ) • QuadraticMap.sq)) where
  toLinearEquiv := (realCliffordPositiveSplitIsometry 2 1).toLinearEquiv
  map_app' v := by
    rw [Units.val_one, one_smul]
    exact (realCliffordPositiveSplitIsometry 2 1).map_app v

private theorem realCliffordThreeOneAugmentedIsometry_apply (v : Fin (3 + 1) → ℝ) :
    realCliffordThreeOneAugmentedIsometry v = (![v 0, v 1, v 3], v 2) := by
  -- The two isometries share their linear equivalence; only the target form differs.
  change realCliffordPositiveSplitIsometry 2 1 v = _
  apply Prod.ext
  · funext i
    fin_cases i
    · simpa using realCliffordPositiveSplitIsometry_fst_pos 2 1 v 0
    · simpa using realCliffordPositiveSplitIsometry_fst_pos 2 1 v 1
    · simpa using realCliffordPositiveSplitIsometry_fst_neg 2 1 v 0
  · simpa using realCliffordPositiveSplitIsometry_snd 2 1 v

private def realCliffordTwoOneScaleIsometry :
    (-(↑((1 : ℝˣ)⁻¹) : ℝ) • realCliffordForm 2 1).IsometryEquiv
      (realCliffordForm 1 2) where
  toLinearEquiv := (realCliffordFormNegIsometry 2 1).toLinearEquiv
  map_app' v := by
    simp [neg_apply]

@[simp]
private theorem realCliffordTwoOneScaleIsometry_apply (v : Fin (2 + 1) → ℝ) :
    realCliffordTwoOneScaleIsometry v = ![v 2, v 0, v 1] := by
  funext i
  fin_cases i
  · simpa [realCliffordTwoOneScaleIsometry, ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv] using
      realCliffordFormNegIsometry_apply_castAdd 2 1 v (0 : Fin 1)
  · simpa [realCliffordTwoOneScaleIsometry, ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv] using
      realCliffordFormNegIsometry_apply_natAdd 2 1 v (0 : Fin 2)
  · simpa [realCliffordTwoOneScaleIsometry, ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv] using
      realCliffordFormNegIsometry_apply_natAdd 2 1 v (1 : Fin 2)

private noncomputable def realCliffordThreeOneEvenEquivOneTwo :
    CliffordAlgebra.even (realCliffordForm 3 1) ≃ₐ[ℝ]
      CliffordAlgebra (realCliffordForm 1 2) :=
  (CliffordAlgebra.evenEquivOfIsometry realCliffordThreeOneAugmentedIsometry).trans <|
    (CliffordAlgebra.evenProdSMulSqEquiv (realCliffordForm 2 1) 1).trans <|
      CliffordAlgebra.equivOfIsometry realCliffordTwoOneScaleIsometry

private theorem realCliffordThreeOneEvenEquivOneTwo_reverseEven
    (x : CliffordAlgebra.even (realCliffordForm 3 1)) :
    realCliffordThreeOneEvenEquivOneTwo
        (CliffordAlgebra.reverseEven (realCliffordForm 3 1) x) =
      star (realCliffordThreeOneEvenEquivOneTwo x) := by
  simp only [realCliffordThreeOneEvenEquivOneTwo, AlgEquiv.trans_apply]
  rw [CliffordAlgebra.evenEquivOfIsometry_reverseEven,
    CliffordAlgebra.evenProdSMulSqEquiv_reverseEven,
    CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_star]
  rfl

/-- The Lorentzian even-algebra model `Cl⁺(3,1) ≃ M₂(ℂ)`. -/
noncomputable def realCliffordThreeOneEvenEquivComplexMatrix :
    CliffordAlgebra.even (realCliffordForm 3 1) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℂ :=
  realCliffordThreeOneEvenEquivOneTwo.trans realCliffordOneTwoEquivComplexMatrix

/-- The complex matrix coordinates of a product of two generators of `Cl⁺(3,1)`. -/
@[simp]
theorem realCliffordThreeOneEvenEquivComplexMatrix_ι
    (m n : Fin (3 + 1) → ℝ) :
    realCliffordThreeOneEvenEquivComplexMatrix
        ((CliffordAlgebra.even.ι (realCliffordForm 3 1)).bilin m n) =
      -(!![(m 3 : ℂ) + m 2, (m 1 : ℂ) + (m 0 : ℂ) * Complex.I;
           -(m 1 : ℂ) + (m 0 : ℂ) * Complex.I, -(m 3 : ℂ) + m 2] *
        !![(n 3 : ℂ) - n 2, (n 1 : ℂ) + (n 0 : ℂ) * Complex.I;
           -(n 1 : ℂ) + (n 0 : ℂ) * Complex.I, -(n 3 : ℂ) - n 2]) := by
  simp only [realCliffordThreeOneEvenEquivComplexMatrix, AlgEquiv.trans_apply,
    realCliffordThreeOneEvenEquivOneTwo, CliffordAlgebra.evenEquivOfIsometry_ι,
    realCliffordThreeOneAugmentedIsometry_apply,
    CliffordAlgebra.evenProdSMulSqEquiv_ι, map_smul,
    CliffordAlgebra.equivOfIsometry_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- In the complex matrix model of `Cl⁺(3,1)`, Clifford reversal is matrix adjugation. -/
@[simp]
theorem realCliffordThreeOneEvenEquivComplexMatrix_reverseEven
    (x : CliffordAlgebra.even (realCliffordForm 3 1)) :
    realCliffordThreeOneEvenEquivComplexMatrix
        (CliffordAlgebra.reverseEven (realCliffordForm 3 1) x) =
      Matrix.adjugate (realCliffordThreeOneEvenEquivComplexMatrix x) := by
  rw [realCliffordThreeOneEvenEquivComplexMatrix, AlgEquiv.trans_apply,
    realCliffordThreeOneEvenEquivOneTwo_reverseEven,
    realCliffordOneTwoEquivComplexMatrix_star]
  rfl

/-- In the Lorentzian matrix model of `Cl⁺(3,1)`, the reverse norm-one equation is determinant
one. -/
@[simp high]
theorem realCliffordThreeOne_reverseEven_mul_self_eq_one_iff_det_eq_one
    (x : CliffordAlgebra.even (realCliffordForm 3 1)) :
    CliffordAlgebra.reverseEven (realCliffordForm 3 1) x * x = 1 ↔
      (realCliffordThreeOneEvenEquivComplexMatrix x).det = 1 := by
  let A := realCliffordThreeOneEvenEquivComplexMatrix x
  rw [← Matrix.adjugate_mul_self_eq_one_iff_det_eq_one A]
  constructor
  · intro h
    have hm := congrArg realCliffordThreeOneEvenEquivComplexMatrix h
    simpa [A] using hm
  · intro h
    apply realCliffordThreeOneEvenEquivComplexMatrix.injective
    simpa [A] using h

end TauCeti

end
