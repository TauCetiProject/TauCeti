/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Scaling
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
public import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Three
import TauCeti.LinearAlgebra.Matrix.Adjugate.FinTwo

/-!
# The split three-dimensional real even Clifford algebra

The even Clifford algebra of the real quadratic form of signature `(2,1)` is the algebra of real
two-by-two matrices. Under this identification, Clifford reversal is matrix adjugation, so the
reverse norm-one equation is the determinant-one equation.

The construction splits off a positive line and uses even-algebra dimension reduction to identify
`Cl⁺(2,1)` with `Cl(1,1)`, followed by the existing split matrix model of `Cl(1,1)`. The quadratic
space itself is identified with the real symmetric two-by-two matrices, where the determinant is
the negative of the signature form.

## Main definitions and results

* `TauCeti.realCliffordTwoOneVectorEquivSymmetric` identifies the quadratic space with symmetric
  real two-by-two matrices.
* `TauCeti.realCliffordTwoOneVectorEquivSymmetric_det` identifies the quadratic form with the
  negative determinant.
* `TauCeti.realCliffordTwoOneEvenEquivMatrix` identifies `Cl⁺(2,1)` with `M₂(ℝ)`.
* `TauCeti.realCliffordTwoOneEvenEquivMatrix_reverseEven` identifies Clifford reversal with matrix
  adjugation.
* `TauCeti.realCliffordTwoOne_reverseEven_mul_self_eq_one_iff_det_eq_one` characterizes the
  reverse-unitary carrier by determinant one.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4.
-/

public section

open scoped Matrix

namespace TauCeti

/-! ## The quadratic space as symmetric matrices -/

/-- The real Clifford form of signature `(2,1)` in coordinates. -/
@[simp]
theorem realCliffordForm_two_one_apply (v : Fin 3 → ℝ) :
    realCliffordForm 2 1 v = v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2 := by
  rw [realCliffordForm_apply, Fin.sum_univ_three]
  rw [realCliffordWeight_of_lt (p := 2) (q := 1) (i := (0 : Fin 3)) (by decide),
    realCliffordWeight_of_lt (p := 2) (q := 1) (i := (1 : Fin 3)) (by decide),
    realCliffordWeight_of_le (p := 2) (q := 1) (i := (2 : Fin 3)) (by decide)]
  simp only [one_mul, neg_one_mul]
  ring

private def realCliffordTwoOneVectorMatrix (v : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![-v 2 - v 1, v 0; v 0, -v 2 + v 1]

private theorem realCliffordTwoOneVectorMatrix_isHermitian (v : Fin 3 → ℝ) :
    (realCliffordTwoOneVectorMatrix v).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [realCliffordTwoOneVectorMatrix]

/-- The signature `(2,1)` quadratic space as the real vector space of symmetric two-by-two
matrices. The coordinate convention is compatible with
`realCliffordTwoOneEvenEquivMatrix`; the Spin action becomes matrix congruence in
`realSpinTwoOneEquivSpecialLinear_action`. -/
noncomputable def realCliffordTwoOneVectorEquivSymmetric :
    (Fin 3 → ℝ) ≃ₗ[ℝ] selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) where
  toFun v := ⟨realCliffordTwoOneVectorMatrix v,
    (realCliffordTwoOneVectorMatrix_isHermitian v).isSelfAdjoint⟩
  invFun A := ![A.1 0 1, (A.1 1 1 - A.1 0 0) / 2,
    -(A.1 0 0 + A.1 1 1) / 2]
  map_add' v w := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [realCliffordTwoOneVectorMatrix] <;> ring
  map_smul' r v := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [realCliffordTwoOneVectorMatrix] <;> ring
  left_inv v := by
    funext i
    fin_cases i <;> simp [realCliffordTwoOneVectorMatrix]
  right_inv A := by
    have hA := A.2
    -- Expose the self-adjoint subtype predicate as the matrix equation used below.
    change IsSelfAdjoint (A.1 : Matrix (Fin 2) (Fin 2) ℝ) at hA
    rw [isSelfAdjoint_iff] at hA
    have h01 := congrFun (congrFun hA 0) 1
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realCliffordTwoOneVectorMatrix] at h01 ⊢ <;> linarith

/-- The symmetric-matrix coordinates of a vector in the split real three-dimensional model. -/
@[simp]
theorem coe_realCliffordTwoOneVectorEquivSymmetric_apply (v : Fin 3 → ℝ) :
    (realCliffordTwoOneVectorEquivSymmetric v : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-v 2 - v 1, v 0; v 0, -v 2 + v 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The vector coordinates recovered from a symmetric real two-by-two matrix. -/
@[simp]
theorem realCliffordTwoOneVectorEquivSymmetric_symm_apply
    (A : selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ)) :
    realCliffordTwoOneVectorEquivSymmetric.symm A =
      ![A.1 0 1, (A.1 1 1 - A.1 0 0) / 2,
        -(A.1 0 0 + A.1 1 1) / 2] := (rfl)

/-- The determinant in the symmetric-matrix model is the negative signature `(2,1)` form. -/
theorem realCliffordTwoOneVectorEquivSymmetric_det (v : Fin 3 → ℝ) :
    ((realCliffordTwoOneVectorEquivSymmetric v :
      selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ).det = -(realCliffordForm 2 1 v) := by
  rw [coe_realCliffordTwoOneVectorEquivSymmetric_apply, Matrix.det_fin_two,
    realCliffordForm_two_one_apply]
  simp
  ring

/-! ## The even Clifford algebra -/

private def realCliffordTwoOneAugmentedIsometry :
    (realCliffordForm 2 1).IsometryEquiv
      ((realCliffordForm 1 1).prod
        ((↑(1 : ℝˣ) : ℝ) • QuadraticMap.sq)) where
  toLinearEquiv := (realCliffordPositiveSplitIsometry 1 1).toLinearEquiv
  map_app' v := by
    convert (realCliffordPositiveSplitIsometry 1 1).map_app v using 1
    all_goals norm_num

private theorem realCliffordTwoOneAugmentedIsometry_apply (v : Fin (2 + 1) → ℝ) :
    realCliffordTwoOneAugmentedIsometry v = (![v 0, v 2], v 1) := by
  -- Expose the underlying signature-splitting isometry before comparing coordinates.
  change realCliffordPositiveSplitIsometry 1 1 v = _
  apply Prod.ext
  · funext i
    fin_cases i
    · simpa using realCliffordPositiveSplitIsometry_fst_pos 1 1 v 0
    · simpa using realCliffordPositiveSplitIsometry_fst_neg 1 1 v 0
  · simpa using realCliffordPositiveSplitIsometry_snd 1 1 v

private def realCliffordOneOneScaleIsometry :
    (-(↑((1 : ℝˣ)⁻¹) : ℝ) • realCliffordForm 1 1).IsometryEquiv
      (realCliffordForm 1 1) where
  toLinearEquiv := (realCliffordFormNegIsometry 1 1).toLinearEquiv
  map_app' v := by simp [neg_apply]

private theorem realCliffordOneOneScaleIsometry_apply (v : Fin (1 + 1) → ℝ) :
    realCliffordOneOneScaleIsometry v = ![v 1, v 0] := by
  funext i
  fin_cases i
  · simpa [realCliffordOneOneScaleIsometry,
      ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv] using
      realCliffordFormNegIsometry_apply_castAdd 1 1 v (0 : Fin 1)
  · simpa [realCliffordOneOneScaleIsometry,
      ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv] using
      realCliffordFormNegIsometry_apply_natAdd 1 1 v (0 : Fin 1)

/-- The split even-algebra model `Cl⁺(2,1) ≃ M₂(ℝ)`. -/
noncomputable def realCliffordTwoOneEvenEquivMatrix :
    CliffordAlgebra.even (realCliffordForm 2 1) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℝ :=
  (CliffordAlgebra.evenEquivOfIsometry realCliffordTwoOneAugmentedIsometry).trans <|
    (CliffordAlgebra.evenProdSMulSqEquiv (realCliffordForm 1 1) 1).trans <|
      (CliffordAlgebra.equivOfIsometry realCliffordOneOneScaleIsometry).trans
        realCliffordOneOneEquivMatrix

/-- The matrix coordinates of a product of two generators in `Cl⁺(2,1)`. -/
@[simp]
theorem realCliffordTwoOneEvenEquivMatrix_ι (m n : Fin (2 + 1) → ℝ) :
    realCliffordTwoOneEvenEquivMatrix
        ((CliffordAlgebra.even.ι (realCliffordForm 2 1)).bilin m n) =
      -(!![m 2 + m 1, m 0; -m 0, -m 2 + m 1] *
        !![n 2 - n 1, n 0; -n 0, -n 2 - n 1]) := by
  simp only [realCliffordTwoOneEvenEquivMatrix, AlgEquiv.trans_apply,
    CliffordAlgebra.evenEquivOfIsometry_ι,
    realCliffordTwoOneAugmentedIsometry_apply,
    CliffordAlgebra.evenProdSMulSqEquiv_ι, map_smul,
    CliffordAlgebra.equivOfIsometry_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CliffordAlgebra.map_apply_ι, realCliffordOneOneScaleIsometry_apply,
      realCliffordOneOneEquivMatrix_ι, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- In the split matrix model of `Cl⁺(2,1)`, Clifford reversal is matrix adjugation. -/
@[simp]
theorem realCliffordTwoOneEvenEquivMatrix_reverseEven
    (x : CliffordAlgebra.even (realCliffordForm 2 1)) :
    realCliffordTwoOneEvenEquivMatrix
        (CliffordAlgebra.reverseEven (realCliffordForm 2 1) x) =
      Matrix.adjugate (realCliffordTwoOneEvenEquivMatrix x) :=
  CliffordAlgebra.map_reverseEven_eq_adjugate_of_finrank_eq_three
    (realCliffordForm 2 1) (by norm_num) realCliffordTwoOneEvenEquivMatrix x

/-- In the split three-dimensional matrix model, the reverse norm-one equation is determinant
one. -/
@[simp↓]
theorem realCliffordTwoOne_reverseEven_mul_self_eq_one_iff_det_eq_one
    (x : CliffordAlgebra.even (realCliffordForm 2 1)) :
    CliffordAlgebra.reverseEven (realCliffordForm 2 1) x * x = 1 ↔
      (realCliffordTwoOneEvenEquivMatrix x).det = 1 :=
  CliffordAlgebra.reverseEven_mul_eq_one_iff_det_eq_one_of_finrank_eq_three
    (realCliffordForm 2 1) (by norm_num) realCliffordTwoOneEvenEquivMatrix x

end TauCeti

end
