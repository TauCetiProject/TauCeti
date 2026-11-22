/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.DeterminantBound
public import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Worked determinant-size bounds

These examples compare factorial entry bounds with sharp Euclidean-row Hadamard bounds,
including empty matrices, row and column orientations, and dependent Gram families.
-/

public section

open scoped Matrix
open Matrix

/-- The empty matrix has determinant one, and the norm bound retains that endpoint. -/
example (A : Matrix (Fin 0) (Fin 0) ℝ) : A.det = 1 ∧ ‖A.det‖ ≤ 1 := by
  have h := A.norm_det_le_factorial_prod (b := fun _ ↦ 1) (by intro i; exact Fin.elim0 i)
  exact ⟨det_isEmpty, h.trans_eq (by simp)⟩

/-- The logarithmic entry bound has the empty value zero. -/
example (A : Matrix (Fin 0) (Fin 0) ℝ) : Real.log |A.det| = 0 ∧ Real.log |A.det| ≤ 0 := by
  have h := A.log_abv_det_le AbsoluteValue.abs (b := fun _ ↦ 1)
    (by intro i; exact Fin.elim0 i) (by simp)
  exact ⟨by simp, h.trans_eq (by simp)⟩

/-- The two by two sign matrix attains the factorial bound and rejects omitting the factorial. -/
example :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]
    ‖A.det‖ = 2 ∧ ‖A.det‖ ≤ 2 ∧ ¬ ‖A.det‖ ≤ ∏ _ : Fin 2, (1 : ℝ) := by
  intro A
  have h := A.norm_det_le_factorial_prod (b := fun _ ↦ 1)
    (by norm_num [A, Fin.forall_fin_two])
  exact ⟨by norm_num [A, det_fin_two], h.trans_eq (by norm_num),
    by norm_num [A, det_fin_two]⟩

/-- Increasing one row bound remains valid and gives the looser upper bound four. -/
example : ‖(!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ).det‖ ≤ 4 :=
  (norm_det_le_factorial_prod _ (b := ![1, 2])
    (by norm_num [Fin.forall_fin_two])).trans_eq (by norm_num [Fin.prod_univ_two])

/-- The row bounds one and ten fail as column bounds for the same triangular matrix. -/
example :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 10, 1]
    A.det = 1 ∧ (∀ i j, ‖A i j‖ ≤ ![1, 10] i) ∧
      ¬ (∀ i j, ‖A i j‖ ≤ ![1, 10] j) ∧ ‖A.det‖ ≤ 20 := by
  intro A
  have hR : ∀ i j, ‖A i j‖ ≤ ![1, 10] i := by norm_num [A, Fin.forall_fin_two]
  exact ⟨by norm_num [A, det_fin_two], hR, by norm_num [A, Fin.forall_fin_two],
    (A.norm_det_le_factorial_prod hR).trans_eq (by norm_num [Fin.prod_univ_two])⟩

/-- The column form instead uses bounds ten and one, which fail as row bounds. -/
example :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 10, 1]
    (∀ i j, |A i j| ≤ ![10, 1] j) ∧
      ¬ (∀ i j, |A i j| ≤ ![10, 1] i) ∧ |A.det| ≤ 20 := by
  intro A
  have hC : ∀ i j, |A i j| ≤ ![10, 1] j := by norm_num [A, Fin.forall_fin_two]
  exact ⟨hC, by norm_num [A, Fin.forall_fin_two],
    (A.abv_det_le_factorial_prod' AbsoluteValue.abs hC).trans_eq
      (by norm_num [Fin.prod_univ_two])⟩

/-- Integer-valued absolute values are accepted directly, with row bounds three and one. -/
example :
    |(!![2, 3; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ).det| = 1 ∧
      |(!![2, 3; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ).det| ≤ 6 :=
  ⟨by norm_num [det_fin_two],
    (abv_det_le_factorial_prod _ AbsoluteValue.abs (b := ![(3 : ℤ), 1])
      (by norm_num [Fin.forall_fin_two])).trans_eq (by norm_num [Fin.prod_univ_two])⟩

/-- The logarithmic factorial bound applies at the sharp two by two example. -/
example : Real.log |(!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ).det| ≤ Real.log 2 :=
  (log_abv_det_le _ AbsoluteValue.abs (b := fun _ ↦ 1)
    (by norm_num [Fin.forall_fin_two]) (by norm_num [det_fin_two])).trans_eq (by norm_num)

/-- The Euclidean-row Hadamard estimate is sharp for the two by two sign matrix. -/
example :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]
    ‖A.det‖ = 2 ∧ (∏ i, ‖WithLp.toLp 2 (A i)‖) = 2 ∧
      ‖A.det‖ ≤ ∏ i, ‖WithLp.toLp 2 (A i)‖ := by
  intro A
  have hnorm : (∏ i, ‖WithLp.toLp 2 (A i)‖) = 2 := by
    norm_num [A, Fin.prod_univ_two, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  exact ⟨by norm_num [A, det_fin_two], hnorm, A.norm_det_le_prod_norm_toLp⟩

/-- At size three the sharp Euclidean-row bound improves the factorial entry bound. -/
example :
    let A : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 1; 1, -1, 1; 1, 1, -1]
    ‖A.det‖ = 4 ∧ (∏ i, ‖WithLp.toLp 2 (A i)‖) = 3 * Real.sqrt 3 ∧
      ‖A.det‖ ≤ 3 * Real.sqrt 3 ∧ ‖A.det‖ ≤ 6 ∧ 3 * Real.sqrt 3 < 6 := by
  intro A
  have hnorm : (∏ i, ‖WithLp.toLp 2 (A i)‖) = 3 * Real.sqrt 3 := by
    norm_num [A, Fin.prod_univ_three, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have hfac := A.norm_det_le_factorial_prod (b := fun _ ↦ 1)
    (by norm_num [A, Fin.forall_fin_succ])
  refine ⟨by norm_num [A, det_fin_three], hnorm,
    A.norm_det_le_prod_norm_toLp.trans_eq hnorm, hfac.trans_eq (by norm_num), ?_⟩
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- An orthonormal real pair has Gram determinant one and logarithmic upper bound zero. -/
example :
    let b := EuclideanSpace.basisFun (Fin 2) ℝ
    (gram ℝ b).det = 1 ∧ (gram ℝ b).det ≤ ∏ i, ‖b i‖ ^ 2 ∧
      Real.log (gram ℝ b).det = 0 ∧ Real.log (gram ℝ b).det ≤ 0 := by
  intro b
  have hlog := log_det_gram_le b.orthonormal.linearIndependent
  exact ⟨by simp [gram_eq_one_iff_orthonormal.mpr b.orthonormal],
    det_gram_le_prod_norm_sq b,
    by simp [gram_eq_one_iff_orthonormal.mpr b.orthonormal],
    hlog.trans_eq (by simp [b.norm_eq_one])⟩

/-- The complex logarithmic Gram estimate uses the real part of the determinant. -/
example :
    let b := EuclideanSpace.basisFun (Fin 2) ℂ
    (gram ℂ b).det = 1 ∧ (gram ℂ b).det.re ≤ ∏ i, ‖b i‖ ^ 2 ∧
      Real.log (gram ℂ b).det.re ≤ 0 := by
  intro b
  have hlog := log_re_det_gram_le b.orthonormal.linearIndependent
  exact ⟨by simp [gram_eq_one_iff_orthonormal.mpr b.orthonormal],
    re_det_gram_le_prod_norm_sq (𝕜 := ℂ) b, hlog.trans_eq (by simp [b.norm_eq_one])⟩

/-- The shear rows give a nonorthogonal Gram example. The Euclidean-row Hadamard bound `√2`
and Gram bound `2` hold but are not attained. -/
example :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]
    let v : Fin 2 → EuclideanSpace ℝ (Fin 2) := fun i ↦ WithLp.toLp 2 (A i)
    gram ℝ v = !![1, 1; 1, 2] ∧ (gram ℝ v).det = A.det ^ 2 ∧ (gram ℝ v).det = 1 ∧
      (gram ℝ v).det ≤ 2 ∧ |A.det| ≤ Real.sqrt 2 ∧
      Real.log (gram ℝ v).det ≤ Real.log 2 := by
  intro A v
  have hg : gram ℝ v = !![1, 1; 1, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [gram_apply, PiLp.inner_apply, v, A, Fin.sum_univ_two,
        EuclideanSpace.norm_eq]
  have hv : LinearIndependent ℝ v := det_gram_ne_zero_iff_linearIndependent.mp
    (by norm_num [hg, det_fin_two])
  refine ⟨hg, A.det_gram_toLp_eq_det_sq, by norm_num [hg, det_fin_two],
    (det_gram_le_prod_norm_sq (𝕜 := ℝ) v).trans_eq (by
      norm_num [v, A, EuclideanSpace.norm_eq, Fin.prod_univ_two, Fin.sum_univ_two]),
    A.abs_det_le_prod_norm_toLp.trans_eq (by
      norm_num [A, EuclideanSpace.norm_eq, Fin.prod_univ_two, Fin.sum_univ_two]), ?_⟩
  exact (log_det_gram_le hv).trans_eq (by
    norm_num [v, A, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.log_sqrt, ← mul_div_assoc])

/-- Two repeated vectors in dimension one satisfy Gram bounds but fail the logarithmic
hypothesis. -/
example :
    let v : Fin 2 → ℝ := fun _ ↦ 1
    (gram ℝ v).det = 0 ∧ ¬ LinearIndependent ℝ v ∧
      0 ≤ (gram ℝ v).det ∧ (gram ℝ v).det ≤ ∏ i, ‖v i‖ ^ 2 ∧
      (gram ℝ v).det ≤ 1 ∧ ¬ 0 < (gram ℝ v).det := by
  intro v
  have hg : (gram ℝ v).det = 0 := by norm_num [det_fin_two, gram_apply, v]
  exact ⟨hg, fun hv ↦ (det_gram_ne_zero_iff_linearIndependent.mpr hv) hg,
    re_det_gram_nonneg (𝕜 := ℝ) v, det_gram_le_prod_norm_sq (𝕜 := ℝ) v,
    (re_det_gram_le_pow (𝕜 := ℝ) (v := v) (D := 1) (by simp [v])).trans_eq (by simp),
    by simp [hg]⟩
