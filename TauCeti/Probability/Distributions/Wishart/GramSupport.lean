/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Basic
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.GramCone
public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Analysis.Matrix.CovariancePseudoInverse
import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# Exact supports of Gaussian-Gram Wishart laws

The standard Gaussian-Gram law of degree `ν` has support the positive-semidefinite matrices
of rank at most `ν`, not merely the almost-sure maximal-rank stratum. For any positive-semidefinite
scale `S`, its support is the congruence image of this cone by `CFC.sqrt S`. This image is closed,
including at singular scales, so no additional closure is needed. Equivalently, the support
consists of the positive-semidefinite matrices of rank at most `ν` fixed by congruence with the
orthogonal range projector of `CFC.sqrt S`.

The formulas include degree zero, zero scale, and dimension zero. Invalid scales retain the
existing Dirac fallback of `wishartGramMeasure_of_not_posSemidef`.

The algebraic input is `Matrix.PosSemidef.exists_eq_conjTranspose_mul_self_of_rank_le`;
the probabilistic input is full support of the standard Gaussian and support under continuous
pushforward.

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
theorem support_wishartGramMeasure_one (ν p : ℕ) :
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
  exact ((isClosed_setOfPred_posSemidef.preimage continuous_subtype_val).inter
    (TauCeti.isClosed_setOfPred_rank_le ν)).closure_eq

/-- For every positive-semidefinite scale, the Gaussian-Gram support is the square-root
congruence image of the positive-semidefinite rank-at-most-degree cone. The image is already
closed, including for singular scales and degrees. -/
theorem support_wishartGramMeasure (ν : ℕ) (hS : S.PosSemidef) :
    (wishartGramMeasure ν S).support =
      Matrix.symmetricCongruenceLinearMap (CFC.sqrt S) ''
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
            (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ ν} := by
  rw [wishartGramMeasure_eq_map_sqrt ν hS,
    Measure.support_map_eq_closure_image _ (wishartGramMeasure ν 1).support_mem_ae
      (LinearMap.continuous_of_finiteDimensional _), support_wishartGramMeasure_one]
  exact (Matrix.isClosed_image_symmetricCongruenceLinearMap_setOf_posSemidef_rank_le
    (CFC.sqrt S) (CFC.sqrt S).covariancePseudoInverse
    (Matrix.mul_covariancePseudoInverse_mul
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S))) ν).closure_eq

/-- An algebraic characterization of Gaussian-Gram support: positive semidefiniteness,
rank at most the degree, and invariance under the orthogonal range projector of the scale's
square root. -/
@[simp]
theorem mem_support_wishartGramMeasure_iff (ν : ℕ) (hS : S.PosSemidef)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    A ∈ (wishartGramMeasure ν S).support ↔
      (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
        (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ ν ∧
        Matrix.symmetricCongruenceLinearMap
          (CFC.sqrt S * (CFC.sqrt S).covariancePseudoInverse) A = A := by
  rw [support_wishartGramMeasure ν hS,
    Matrix.image_symmetricCongruenceLinearMap_setOf_posSemidef_rank_le
      (CFC.sqrt S) (CFC.sqrt S).covariancePseudoInverse
      (Matrix.mul_covariancePseudoInverse_mul
        (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)))]
  rfl

end TauCeti.Probability
