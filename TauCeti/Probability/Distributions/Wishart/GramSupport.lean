/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Basic
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.GramCone
public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.Analysis.Matrix.CovariancePseudoInverse
import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# Exact supports of Gaussian-Gram Wishart laws

The standard Gaussian-Gram law of degree `ν` has support the positive-semidefinite matrices
of rank at most `ν`, not merely the almost-sure maximal-rank stratum. For any positive-semidefinite
scale `S`, its support is the congruence image of this cone by `CFC.sqrt S`. This image is closed,
including at singular scales, so no additional closure is needed. Equivalently, the support
consists of the positive-semidefinite matrices of rank at most `ν` fixed by congruence with the
orthogonal range projector of `S`.

The formulas include degree zero, zero scale, and dimension zero. Invalid scales retain the
existing Dirac fallback of `TauCeti.Probability.wishartGramMeasure_of_not_posSemidef`;
their square root vanishes, so the congruence-image formula still applies.

The algebraic inputs are `TauCeti.Probability.range_wishartGram`, the closed congruence-image
results in `TauCeti.MeasureTheory.Measure.SymmetricMatrix.GramCone`, and
`Matrix.mul_covariancePseudoInverse_mul`. The probabilistic inputs are full support of the
standard Gaussian and support under continuous pushforward.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped MatrixOrder

namespace TauCeti.Probability

variable {p ν : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}

/-- The exact support of a standard Gaussian-Gram law is the closed
positive-semidefinite cone with rank at most its degree. -/
@[simp]
theorem support_wishartGramMeasure_one (ν : ℕ) :
    (wishartGramMeasure ν (1 : Matrix (Fin p) (Fin p) ℝ)).support =
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
          (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ ν} := by
  have hfull : (Measure.pi fun _ : Fin ν ↦
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) 1).support = univ := by
    simp [Measure.support_pi, multivariateGaussian_zero_one, support_stdGaussian]
  rw [wishartGramMeasure_eq_map_pi,
    Measure.support_map_eq_closure_range _ hfull continuous_wishartGram,
    range_wishartGram, Fintype.card_fin]
  exact (TauCeti.isClosed_setOf_posSemidef_rank_le ν).closure_eq

/-- For every scale, the Gaussian-Gram support is the square-root congruence image of the
positive-semidefinite rank-at-most-degree cone. The image is already closed, including for
singular scales and degrees; invalid scales give the singleton zero. -/
theorem support_wishartGramMeasure (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ) :
    (wishartGramMeasure ν S).support =
      Matrix.symmetricCongruenceLinearMap (CFC.sqrt S) ''
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
            (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ ν} := by
  by_cases hS : S.PosSemidef
  · rw [wishartGramMeasure_eq_map_sqrt ν hS,
      Measure.support_map_eq_closure_image _ (wishartGramMeasure ν 1).support_mem_ae
        (LinearMap.continuous_of_finiteDimensional _), support_wishartGramMeasure_one]
    exact (Matrix.isClosed_image_symmetricCongruenceLinearMap_setOf_posSemidef_rank_le
      (CFC.sqrt S) ν).closure_eq
  · have hn : ¬ 0 ≤ S := fun h ↦ hS (Matrix.nonneg_iff_posSemidef.mp h)
    rw [wishartGramMeasure_of_not_posSemidef ν hS, CFC.sqrt_of_not_nonneg hn]
    have hmem : (0 : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) ∈
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
            (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ ν} := by
      simp [Matrix.PosSemidef.zero]
    simp [Matrix.symmetricCongruenceLinearMap_zero, Set.Nonempty.image_const ⟨0, hmem⟩]

/-- An algebraic characterization of Gaussian-Gram support: positive semidefiniteness,
rank at most the degree, and invariance under congruence with `S * S.covariancePseudoInverse`.
For positive-semidefinite `S`, this matrix is the orthogonal range projector; for invalid
scales it is zero, forcing `A = 0`. -/
theorem mem_support_wishartGramMeasure_iff (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    A ∈ (wishartGramMeasure ν S).support ↔
      (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
        (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ ν ∧
        Matrix.symmetricCongruenceLinearMap
          (S * S.covariancePseudoInverse) A = A := by
  rw [support_wishartGramMeasure ν S,
    Matrix.image_symmetricCongruenceLinearMap_setOf_posSemidef_rank_le
      (CFC.sqrt S) (CFC.sqrt S).covariancePseudoInverse
      (Matrix.mul_covariancePseudoInverse_mul
        (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S))),
    Matrix.sqrt_mul_covariancePseudoInverse_sqrt]
  rfl

/-- At a positive-definite scale the support is the full rank-at-most-degree PSD cone. -/
@[simp]
theorem support_wishartGramMeasure_of_posDef (ν : ℕ) (hS : S.PosDef) :
    (wishartGramMeasure ν S).support =
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
          (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ ν} := by
  ext A
  simp [mem_support_wishartGramMeasure_iff, Matrix.covariancePseudoInverse_of_posDef hS,
    Matrix.mul_nonsing_inv _ (S.isUnit_iff_isUnit_det.mp hS.isUnit)]

/-- Invalid scales have support equal to the singleton zero, as their law is Dirac. -/
theorem support_wishartGramMeasure_of_not_posSemidef (ν : ℕ) (hS : ¬ S.PosSemidef) :
    (wishartGramMeasure ν S).support = {0} := by
  simp [hS]

/-- A zero scale has support equal to the singleton zero at every degree. -/
@[simp]
theorem support_wishartGramMeasure_zero_right (ν : ℕ) :
    (wishartGramMeasure ν (0 : Matrix (Fin p) (Fin p) ℝ)).support = {0} := by
  ext A
  simp only [mem_support_wishartGramMeasure_iff, Matrix.zero_mul,
    Matrix.symmetricCongruenceLinearMap_zero, LinearMap.zero_apply, Set.mem_singleton_iff]
  constructor
  · exact fun h ↦ h.2.2.symm
  · rintro rfl
    simp [Matrix.PosSemidef.zero]

end TauCeti.Probability
