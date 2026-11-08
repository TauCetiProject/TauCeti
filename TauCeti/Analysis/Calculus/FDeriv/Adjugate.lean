/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Det

/-!
# The Piola identity for a curl-free matrix field

If the directional derivatives of the rows of a differentiable square matrix field commute,
the corresponding divergence of every row of its adjugate vanishes. No invertibility of the
matrix is required. The cancellation pairs the two rows replaced in the derivative of a
cofactor, using the alternating property of the determinant.

The argument is adapted from the smooth Hessian Piola identity in the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean).
-/

public section

open scoped Matrix.Norms.Operator

namespace Matrix

private lemma det_swap_rows {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (j k : ι)
    (a b : ι → ℝ) (h : j ≠ k) :
    ((A.updateRow j a).updateRow k b).det =
      -((A.updateRow k a).updateRow j b).det := by
  let M := (A.updateRow k a).updateRow j b
  have hkj : k ≠ j := Ne.symm h
  have he :
      M.submatrix (Equiv.swap j k) id =
        (A.updateRow j a).updateRow k b := by
    ext r l
    by_cases hrj : r = j
    · subst r
      simp [M, Matrix.submatrix_apply, Matrix.updateRow_apply, h, hkj]
    · by_cases hrk : r = k
      · subst r
        simp [M, Matrix.submatrix_apply, Matrix.updateRow_apply]
      · simp [M, Matrix.submatrix_apply, Matrix.updateRow_apply, hrj, hrk,
          Equiv.swap_apply_of_ne_of_ne hrj hrk]
  rw [← he, Matrix.det_permute]
  simp [M, Equiv.Perm.sign_swap h]

private lemma fderiv_det_updateRow
    {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → ι → ι → ℝ) (x : E)
    (hA : ∀ k l, DifferentiableAt ℝ (fun y => A y k l) x)
    (j : ι) (c : ι → ℝ) (v : E) :
    fderiv ℝ (fun y => (Matrix.updateRow (A y) j c).det) x v =
      ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv ℝ (fun y => A y k l) x v)).det := by
  let D : E →L[ℝ] ι → ι → ℝ :=
    ContinuousLinearMap.pi (fun k =>
      ContinuousLinearMap.pi (fun l =>
        if k = j then (0 : E →L[ℝ] ℝ)
        else fderiv ℝ (fun y => A y k l) x))
  let B : E → ι → ι → ℝ :=
    fun y k l => if k = j then c l else A y k l
  have hD : HasFDerivAt B D x := by
    apply hasFDerivAt_pi.mpr
    intro k
    apply hasFDerivAt_pi.mpr
    intro l
    by_cases h : k = j
    · simpa only [B, h, ite_true] using (hasFDerivAt_const (c l) x)
    · simpa only [B, h, ite_false] using (hA k l).hasFDerivAt
  have he :
      (fun y => (Matrix.updateRow (A y) j c).det) =
        (fun y => (Matrix.of (B y)).det) := by
    funext y
    congr 1
    ext k l
    exact Matrix.updateRow_apply
  rw [he]
  -- Transport the Pi-norm row derivative to the matrix operator norm before composing with det.
  let rowsToMatrix : (ι → ι → ℝ) →L[ℝ] Matrix ι ι ℝ :=
    (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have rowsToMatrix_apply (M : ι → ι → ℝ) : rowsToMatrix M = Matrix.of M := by
    simp only [rowsToMatrix, ContinuousLinearEquiv.coe_coe,
      LinearEquiv.coe_toContinuousLinearEquiv', Matrix.coe_ofLinearEquiv]
  have hMatrix := rowsToMatrix.hasFDerivAt.comp x hD
  have hdetComp :=
    (Matrix.differentiable_det (rowsToMatrix (B x))).hasFDerivAt.comp x hMatrix
  have hd :
      fderiv ℝ (fun y => (Matrix.of (B y)).det) x v =
        fderiv ℝ Matrix.det (Matrix.of (B x)) (Matrix.of (D v)) := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L v) hdetComp.fderiv
    have houter := ContinuousLinearMap.comp_apply
      (fderiv ℝ Matrix.det (rowsToMatrix (B x))) (rowsToMatrix.comp D) v
    have hinner := ContinuousLinearMap.comp_apply rowsToMatrix D v
    have heval := h.trans (houter.trans
      (congrArg (fderiv ℝ Matrix.det (rowsToMatrix (B x))) hinner))
    simpa only [Function.comp_def, rowsToMatrix_apply] using heval
  have hdet := fderiv_det_eq_sum_updateRow (Matrix.of (B x)) (Matrix.of (D v))
  have hB : Matrix.of (B x) = Matrix.updateRow (Matrix.of (A x)) j c := by
    ext k l
    exact Matrix.updateRow_apply.symm
  have hAof : Matrix.of (A x) = A x := by
    ext k l
    exact Matrix.of_apply (A x) k l
  calc
    fderiv ℝ (fun y => (Matrix.of (B y)).det) x v =
        fderiv ℝ Matrix.det (Matrix.of (B x)) (Matrix.of (D v)) := hd
    _ = ∑ k, ((Matrix.of (B x)).updateRow k (Matrix.of (D v) k)).det := hdet
    _ = ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv ℝ (fun y => A y k l) x v)).det := by
      rw [hB, hAof]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k = j
      · subst k
        rw [ite_eq_left rfl]
        apply Matrix.det_eq_zero_of_row_eq_zero j
        intro l
        rw [Matrix.updateRow_self]
        simp [D]
      · rw [ite_eq_right h]
        have hr :
            (Matrix.of (D v)) k =
              fun l => fderiv ℝ (fun y => A y k l) x v := by
          funext l
          simp only [Matrix.of_apply, D, ContinuousLinearMap.pi_apply, ite_eq_right h]
        rw [hr]

/-- A curl-free matrix field has divergence-free adjugate rows in the specified directions. -/
theorem sum_fderiv_adjugate_eq_zero_of_comm
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Matrix ι ι ℝ) (e : ι → E) (x : E)
    (hA : ∀ k l, DifferentiableAt ℝ (fun y ↦ A y k l) x)
    (hcomm : ∀ j k l, fderiv ℝ (fun y ↦ A y k l) x (e j) =
      fderiv ℝ (fun y ↦ A y j l) x (e k)) (i : ι) :
    ∑ j, fderiv ℝ (fun y ↦ (A y).adjugate i j) x (e j) = 0 := by
  classical
  let C : ι → ι → ℝ :=
    fun j k =>
      if k = j then 0
      else (((A x).updateRow j (Pi.single i 1)).updateRow k
        (fun l => fderiv ℝ (fun y => A y k l) x (e j))).det
  have hdiv :
      ∀ j, fderiv ℝ (fun y => (A y).adjugate i j) x (e j) =
        ∑ k, C j k := by
    intro j
    have heq :
        (fun y => (A y).adjugate i j) =
          (fun y =>
            ((A y).updateRow j (Pi.single i 1)).det) := by
      funext y
      exact Matrix.adjugate_apply (A y) i j
    rw [heq]
    exact fderiv_det_updateRow
      (fun y => A y) x hA j (Pi.single i 1) (e j)
  have hanti : ∀ j k, C j k = -C k j := by
    intro j k
    by_cases h : j = k
    · subst k
      simp only [C, ite_eq_left rfl, neg_zero]
    · have hw :
          (fun l => fderiv ℝ (fun y => A y k l) x (e j)) =
            (fun l => fderiv ℝ (fun y => A y j l) x (e k)) := by
        funext l
        exact hcomm j k l
      simp only [C, ite_eq_right h, ite_eq_right (Ne.symm h)]
      rw [hw]
      exact det_swap_rows (A x) j k (Pi.single i 1)
        (fun l => fderiv ℝ (fun y => A y j l) x (e k)) h
  calc
    ∑ j, fderiv ℝ (fun y => (A y).adjugate i j) x (e j) =
        ∑ j, ∑ k, C j k := by
          apply Finset.sum_congr rfl
          intro j _
          exact hdiv j
    _ = 0 := by
      have hS :
          (∑ j, ∑ k, C j k) = -(∑ j, ∑ k, C j k) := by
        calc
          ∑ j, ∑ k, C j k = ∑ j, ∑ k, -C k j := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            exact hanti j k
          _ = ∑ j, -(∑ k, C k j) := by
            apply Finset.sum_congr rfl
            intro j _
            exact Finset.sum_neg_distrib _
          _ = -(∑ j, ∑ k, C k j) := by
            rw [Finset.sum_neg_distrib]
          _ = -(∑ j, ∑ k, C j k) := by
            congr 1
            exact Finset.sum_comm
      linarith

end Matrix
