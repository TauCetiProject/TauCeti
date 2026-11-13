/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Mixture.Multivariate
import TauCeti.Probability.Distributions.Mixture.Support
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Topological support of multivariate Gaussian mixtures

The support of a finite multivariate Gaussian mixture is the union of the affine covariance
ranges of its positive-weight components. The covariance matrices may be singular, and the
union need not be convex. An invalid covariance parameter gives a Dirac component at its mean,
so its contribution is a singleton. Components of weight zero impose no covariance conditions.

## References

* G. McLachlan and D. Peel, *Finite Mixture Models*, Wiley (2000), Chapter 3.
-/

public section

open Convexity MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

open Classical in
/-- At every covariance parameter, the support of a multivariate Gaussian mixture is the union
of its positive-weight components' affine ranges, with singletons for invalid covariances. -/
theorem support_multivariateGaussianMixtureMeasure (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) :
    (multivariateGaussianMixtureMeasure p m S).support =
      ⋃ k, ⋃ (_ : 0 < p.weights k),
        if (S k).PosSemidef then
          (AffineSubspace.mk' (m k) (LinearMap.range (Matrix.toEuclideanLin (S k))) :
            Set (EuclideanSpace ℝ ι))
        else {m k} := by
  classical
  rw [multivariateGaussianMixtureMeasure_def, ← finiteMixtureMeasure_def,
    support_finiteMixtureMeasure]
  congr 1
  funext k
  by_cases hk : (S k).PosSemidef
  · simp [hk, support_multivariateGaussian hk]
  · simp [hk, multivariateGaussian_of_not_posSemidef _ hk, Measure.support_dirac]

/-- If every positive-weight covariance is positive semidefinite, the mixture support is
exactly the union of their affine covariance ranges, including singular and zero covariances. -/
@[simp]
theorem support_multivariateGaussianMixtureMeasure_of_posSemidef
    {p : StdSimplex ℝ≥0 κ} (m : κ → EuclideanSpace ℝ ι) {S : κ → Matrix ι ι ℝ}
    (hS : ∀ k, 0 < p.weights k → (S k).PosSemidef) :
    (multivariateGaussianMixtureMeasure p m S).support =
      ⋃ k, ⋃ (_ : 0 < p.weights k),
        (AffineSubspace.mk' (m k) (LinearMap.range (Matrix.toEuclideanLin (S k))) :
          Set (EuclideanSpace ℝ ι)) := by
  classical
  rw [support_multivariateGaussianMixtureMeasure]
  apply iUnion_congr
  intro k
  apply iUnion_congr
  intro hk
  simp [hS k hk]

end TauCeti.Probability
