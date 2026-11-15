/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.RandomMatrices.Ginibre.Density
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
  Cambridge University Press, 2010, §2.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder MatrixOrder

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
    exact ⟨fun p ↦ X p.1 p.2, rfl⟩
  rw [hr, closure_univ]

/-- The support of a standard complex Gaussian Gram law is the closed cone of
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
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨posSemidef_self_mul_conjTranspose X,
        (Matrix.rank_self_mul_conjTranspose X).trans_le
          (by simpa using X.rank_le_card_width)⟩
    · rintro ⟨hA, hr⟩
      obtain ⟨X, hX⟩ := hA.exists_eq_conjTranspose_mul_self_of_rank_le
        (m := Fin n) (by simpa using hr)
      exact ⟨Xᴴ, by simpa using hX.symm⟩
  rw [hr]
  apply IsClosed.closure_eq
  have hpsd : IsClosed {A : Matrix (Fin m) (Fin m) ℂ | A.PosSemidef} := by
    simpa only [Set.Ici, Matrix.nonneg_iff_posSemidef] using
      (isClosed_Ici : IsClosed (Set.Ici (0 : Matrix (Fin m) (Fin m) ℂ)))
  exact hpsd.inter (Matrix.isClosed_setOfPred_rank_le n)

end TauCeti.Probability
