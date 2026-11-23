/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.DeterminantBound
public import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
public import TauCeti.Analysis.Polynomial.HasseDerivBound
public import TauCeti.LinearAlgebra.Matrix.ConfluentVandermonde
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Worked determinant-size bounds

These examples compare factorial entry bounds with sharp Euclidean-row Hadamard bounds,
including empty matrices, row and column orientations, and dependent Gram families. For a
confluent Vandermonde matrix, the row bounds come from evaluated Hasse derivative bounds.
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

/-- The confluent Vandermonde matrix for the nodes `0, 1` with multiplicities `2, 1` over `ℂ`.
Packaging the evaluated Hasse derivative bounds row by row over the support `{0, 1, 2}` gives
the row bounds `(1, 1, 1)` from the node bounds `(0, 1)` and `(1, 2, 1)` from the common node
bound `1`. The factorial bound then gives `1 ≤ 6` and `1 ≤ 12`, while the Euclidean row norms
`1, 1, Real.sqrt 3` give the sharper Hadamard bound `1 ≤ Real.sqrt 3`. -/
example :
    confluentVandermonde ![(0 : ℂ), 1] ![2, 1] = !![1, 0, 0; 0, 1, 0; 1, 1, 1] ∧
      ‖(confluentVandermonde ![(0 : ℂ), 1] ![2, 1]).det‖ = 1 ∧
      (∀ ρ j, ‖confluentVandermonde ![(0 : ℂ), 1] ![2, 1] ρ j‖ ≤ ![1, 1, 1] ρ) ∧
      ‖(confluentVandermonde ![(0 : ℂ), 1] ![2, 1]).det‖ ≤ 6 ∧
      (∀ ρ j, ‖confluentVandermonde ![(0 : ℂ), 1] ![2, 1] ρ j‖ ≤ ![1, 2, 1] ρ) ∧
      ‖(confluentVandermonde ![(0 : ℂ), 1] ![2, 1]).det‖ ≤ 12 ∧
      (∏ ρ, ‖WithLp.toLp 2 (confluentVandermonde ![(0 : ℂ), 1] ![2, 1] ρ)‖) = Real.sqrt 3 ∧
      ‖(confluentVandermonde ![(0 : ℂ), 1] ![2, 1]).det‖ ≤ Real.sqrt 3 := by
  have hA : confluentVandermonde ![(0 : ℂ), 1] ![2, 1] = !![1, 0, 0; 0, 1, 0; 1, 1, 1] := by
    ext ρ j
    obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective ρ
    rw [confluentVandermonde_finSigmaFinEquiv]
    fin_cases i <;> fin_cases k <;> fin_cases j <;> simp <;> rfl
  -- The row of the jet `⟨i, k⟩` is bounded by the maximum over the support `{0, 1, 2}` of
  -- `choose j k * N i ^ (j - k)`, for any bounds `N i` on the nodes.
  have hrow (N : Fin 2 → ℝ) (hN : ∀ i, ‖![(0 : ℂ), 1] i‖ ≤ N i)
      (B : Fin (∑ i, ![2, 1] i) → ℝ)
      (hB : ∀ (i : Fin 2) (k : Fin (![2, 1] i)), ∀ j : ℕ, j < 3 →
        ((j.choose k : ℕ) : ℝ) * N i ^ (j - k) ≤ B (finSigmaFinEquiv ⟨i, k⟩)) :
      ∀ ρ j, ‖confluentVandermonde ![(0 : ℂ), 1] ![2, 1] ρ j‖ ≤ B ρ := by
    intro ρ j
    obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective ρ
    rw [confluentVandermonde_apply, Equiv.symm_apply_apply]
    exact (Polynomial.norm_eval_hasseDeriv_X_pow_le_sup' (hN i) k
      (Finset.mem_range.2 j.isLt)).trans <|
        Finset.sup'_le _ _ fun j hj ↦ hB i k j (Finset.mem_range.1 hj)
  have hB₁ := hrow ![0, 1] (by simp [Fin.forall_fin_two]) ![1, 1, 1] <| by
    intro i k j hj
    fin_cases i <;> fin_cases k <;> interval_cases j <;> (change _ ≤ (1 : ℝ); norm_num)
  have hB₂ := hrow (fun _ ↦ 1) (by simp [Fin.forall_fin_two]) ![1, 2, 1] <| by
    intro i k j hj
    fin_cases i <;> fin_cases k <;> interval_cases j <;>
      first | (change _ ≤ (1 : ℝ); norm_num) | (change _ ≤ (2 : ℝ); norm_num)
  have hnorm :
      (∏ ρ, ‖WithLp.toLp 2 (confluentVandermonde ![(0 : ℂ), 1] ![2, 1] ρ)‖) = Real.sqrt 3 := by
    rw [hA]
    change ∏ ρ : Fin 3, ‖WithLp.toLp 2 ((!![1, 0, 0; 0, 1, 0; 1, 1, 1] :
      Matrix (Fin 3) (Fin 3) ℂ) ρ)‖ = Real.sqrt 3
    norm_num [Fin.prod_univ_three, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  refine ⟨hA, by simp [det_confluentVandermonde, Fin.prod_univ_two], hB₁, ?_, hB₂, ?_, hnorm,
    (norm_det_le_prod_norm_toLp _).trans_eq hnorm⟩
  · refine (norm_det_le_factorial_prod _ hB₁).trans_eq ?_
    change _ * ∏ i : Fin 3, ![(1 : ℝ), 1, 1] i = 6
    norm_num [Fin.prod_univ_three]
  · refine (norm_det_le_factorial_prod _ hB₂).trans_eq ?_
    change _ * ∏ i : Fin 3, ![(1 : ℝ), 2, 1] i = 12
    norm_num [Fin.prod_univ_three]
