/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Det
import TauCeti.Algebra.BigOperators.Finset.OffDiagonal
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic

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

/-- Each entry of the adjugate of an entrywise differentiable matrix field is differentiable. -/
theorem differentiableAt_adjugate_apply
    {ι E 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : E → Matrix ι ι 𝕜) (x : E)
    (hA : ∀ i j, DifferentiableAt 𝕜 (fun y ↦ A y i j) x) (i j : ι) :
    DifferentiableAt 𝕜 (fun y ↦ (A y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  apply Matrix.differentiable_det.differentiableAt.comp x
  apply differentiableAt_pi.mpr
  intro k
  apply differentiableAt_pi.mpr
  intro l
  by_cases hk : k = j
  · simp only [Matrix.updateRow_apply, hk, ite_true]
    exact differentiableAt_const _
  · simp only [Matrix.updateRow_apply, hk, ite_false]
    exact hA k l

/-- A curl-free matrix field has divergence-free adjugate rows in the specified directions. -/
theorem sum_fderiv_adjugate_eq_zero_of_comm
    {ι E 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : E → Matrix ι ι 𝕜) (e : ι → E) (x : E)
    (hA : ∀ k l, DifferentiableAt 𝕜 (fun y ↦ A y k l) x)
    (hcomm : ∀ j k l, fderiv 𝕜 (fun y ↦ A y k l) x (e j) =
      fderiv 𝕜 (fun y ↦ A y j l) x (e k)) (i : ι) :
    ∑ j, fderiv 𝕜 (fun y ↦ (A y).adjugate i j) x (e j) = 0 := by
  classical
  let C : ι → ι → 𝕜 :=
    fun j k =>
      if k = j then 0
      else (((A x).updateRow j (Pi.single i 1)).updateRow k
        (fun l => fderiv 𝕜 (fun y => A y k l) x (e j))).det
  have hdiv :
      ∀ j, fderiv 𝕜 (fun y => (A y).adjugate i j) x (e j) =
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
          (fun l => fderiv 𝕜 (fun y => A y k l) x (e j)) =
            (fun l => fderiv 𝕜 (fun y => A y j l) x (e k)) := by
        funext l
        exact hcomm j k l
      simp only [C, ite_eq_right h, ite_eq_right (Ne.symm h)]
      rw [hw]
      exact det_updateRow_updateRow_swap (A x) j k (Pi.single i 1)
        (fun l => fderiv 𝕜 (fun y => A y j l) x (e k)) h
  calc
    ∑ j, fderiv 𝕜 (fun y => (A y).adjugate i j) x (e j) =
        ∑ j, ∑ k, C j k := by
          apply Finset.sum_congr rfl
          intro j _
          exact hdiv j
    _ = 0 := by
      apply Finset.sum_sum_eq_zero_of_diag Finset.univ
      · intro j _
        simp only [C, ite_true]
      · intro j _ k _ _
        rw [hanti j k]
        exact neg_add_cancel _

end Matrix
