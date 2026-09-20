/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Parameter measurability of multivariate Gaussian distributions

This file records joint measurability of the multivariate Gaussian law when its raw matrix
parameter is supplied by its entries.  This coordinate form lets a measurable random mean and
matrix-valued parameter define a measure-valued kernel without first bundling the matrix.

## Main result

* `TauCeti.measurable_multivariateGaussian` — the Gaussian law is jointly measurable in its mean
  and every coordinate of its raw matrix parameter.
-/

public section

noncomputable section

open ProbabilityTheory

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The multivariate Gaussian law is jointly measurable in its mean and every coordinate of its
raw matrix parameter.  When the matrix is positive semidefinite it is the covariance matrix;
otherwise `multivariateGaussian` is the Dirac measure at the mean. -/
@[fun_prop]
theorem measurable_multivariateGaussian :
    Measurable fun q : EuclideanSpace ℝ ι × (ι → ι → ℝ) =>
      multivariateGaussian q.1 (Matrix.of q.2) :=
  ProbabilityTheory.measurable_multivariateGaussian.comp
    (measurable_fst.prodMk ((Matrix.measurable_of ι ι ℝ).comp measurable_snd))

end TauCeti
