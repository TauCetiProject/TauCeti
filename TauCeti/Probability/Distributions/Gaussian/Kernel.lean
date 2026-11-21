/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Kernel.Basic

/-!
# Multivariate Gaussian kernels

Measurable families of means and covariances give Markov kernels via Mathlib's
`ProbabilityTheory.measurable_multivariateGaussian`. The isotropic observation kernel has
mean `c • x` and covariance `v • 1` at input `x`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section

variable {X : Type*} [MeasurableSpace X]

/-- The kernel of multivariate Gaussian laws whose mean and covariance are measurable functions
of the input. Like `multivariateGaussian`, it allows singular covariance and gives a point mass
at the mean when the covariance parameter is not positive semidefinite. -/
def multivariateGaussianKernel (m : X → EuclideanSpace ℝ ι) (S : X → Matrix ι ι ℝ)
    (hm : Measurable m) (hS : Measurable S) : Kernel X (EuclideanSpace ℝ ι) :=
  ⟨fun x ↦ multivariateGaussian (m x) (S x), measurable_multivariateGaussian.comp (hm.prodMk hS)⟩

/-- Evaluation of a Gaussian kernel gives the Gaussian law with the parameters at that input. -/
@[simp] theorem multivariateGaussianKernel_apply (m : X → EuclideanSpace ℝ ι)
    (S : X → Matrix ι ι ℝ) (hm : Measurable m) (hS : Measurable S) (x : X) :
    multivariateGaussianKernel m S hm hS x = multivariateGaussian (m x) (S x) := (rfl)

instance (m : X → EuclideanSpace ℝ ι) (S : X → Matrix ι ι ℝ)
    (hm : Measurable m) (hS : Measurable S) : IsMarkovKernel (multivariateGaussianKernel m S hm hS)
    where
  isProbabilityMeasure x := by
    rw [multivariateGaussianKernel_apply]
    infer_instance

end

/-- The Gaussian observation kernel with signal multiplier `c` and isotropic variance `v`.
At `v = 0` it is deterministic, and at `v < 0` it uses the same covariance-parameter convention
as `multivariateGaussian`. -/
def gaussianKernel (c v : ℝ) : Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) :=
  multivariateGaussianKernel (fun x ↦ c • x) (fun _ ↦ v • 1) (by fun_prop) measurable_const

/-- The conditional law at `x` is Gaussian with mean `c • x` and covariance `v • 1`. -/
@[simp] theorem gaussianKernel_apply (c v : ℝ) (x : EuclideanSpace ℝ ι) :
    gaussianKernel c v x = multivariateGaussian (c • x) (v • 1) := by
  rw [gaussianKernel, multivariateGaussianKernel_apply]

instance (c v : ℝ) : IsMarkovKernel (gaussianKernel (ι := ι) c v) := by
  rw [gaussianKernel]
  infer_instance

end TauCeti
