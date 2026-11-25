/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.RandomMatrices.Ginibre.Basic
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Support
public import TauCeti.Analysis.Matrix.GramFactorization
public import TauCeti.LinearAlgebra.Matrix.Rank.Closed

/-!
# Topological support of complex Gaussian Gram laws

The complex Ginibre law has full support on the rectangular matrix space. Its Gram pushforward
has support exactly the positive-semidefinite matrices of rank at most the sample size. This
closed support includes lower-rank matrices, although almost every Gram matrix has maximal
permitted rank. The proof uses the rectangular Gram factorization, so it also treats the zero
sample size.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §4.1.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder

namespace TauCeti.Probability

/-- The complex Ginibre law has full support on the rectangular matrix space. -/
@[simp]
theorem support_ginibreComplex (m n : ℕ) : (ginibreComplex m n).support = Set.univ := by
  rw [ginibreComplex_eq_map_properComplexGaussianMeasure,
    Measure.support_map_eq_closure_range _
      (support_properComplexGaussianMeasure_one _) (by fun_prop)]
  have hr : Set.range (fun z : Fin m × Fin n → ℂ ↦ Matrix.of fun i j ↦ z (i, j)) =
      Set.univ := by
    apply Set.range_eq_univ.mpr
    intro X
    exact ⟨fun p ↦ X p.1 p.2, by ext i j; simp⟩
  rw [hr, closure_univ]

/-- The support of a standard complex Gaussian Gram law is the closed set of
positive-semidefinite matrices of rank at most its sample size. -/
@[simp]
theorem support_gaussianGramComplex (m n : ℕ) :
    (gaussianGramComplex m n).support =
      {A : Matrix (Fin m) (Fin m) ℂ | A.PosSemidef ∧ A.rank ≤ n} := by
  rw [gaussianGramComplex_def,
    Measure.support_map_eq_closure_range _ (support_ginibreComplex m n) (by fun_prop)]
  have hr : Set.range (fun X : Matrix (Fin m) (Fin n) ℂ ↦ X * Xᴴ) =
      {A : Matrix (Fin m) (Fin m) ℂ | A.PosSemidef ∧ A.rank ≤ n} := by
    ext A
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    have h := Matrix.posSemidef_and_rank_le_iff_eq_conjTranspose_mul_self
      (m := Fin n) (B := A)
    simp only [Fintype.card_fin] at h
    rw [h]
    simpa [eq_comm] using
      (Matrix.conjTransposeAddEquiv (Fin m) (Fin n) ℂ).toEquiv.exists_congr_left
        (p := fun X ↦ X * Xᴴ = A)
  rw [hr]
  apply IsClosed.closure_eq
  exact _root_.isClosed_setOfPred_posSemidef.inter (Matrix.isClosed_setOfPred_rank_le n)

end TauCeti.Probability
