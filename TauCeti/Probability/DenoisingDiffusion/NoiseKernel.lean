/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.Prod

import TauCeti.MeasureTheory.Group.Convolution.Translation
import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.Probability.Distributions.Gaussian.Multivariate
import TauCeti.Probability.Distributions.Gaussian.Sum

/-!
# Variance-preserving Gaussian noising kernels

For a signal level `a`, the noising kernel `noiseKernel a` on `EuclideanSpace ℝ ι` sends `x` to
the law of `√a • x + √(1 - a) • e` with `e` standard Gaussian. These are the one-step transition
kernels of the forward chain of a denoising diffusion model. For `0 ≤ a ≤ 1` they preserve the
standard Gaussian law, and composing them multiplies the signal levels, which gives the closed
form of the `t`-step transition of the forward chain.

## Main results

* `TauCeti.Probability.noiseKernel`: the kernel `x ↦ law of √a • x + √(1 - a) • e`.
* `TauCeti.Probability.noiseKernel_apply`: `noiseKernel a x` is the isotropic Gaussian with mean
  `√a • x` and covariance parameter `(1 - a) • 1`, for every real `a`.
* `TauCeti.Probability.noiseKernel_comp`: `noiseKernel b ∘ₖ noiseKernel a = noiseKernel (a * b)`
  for `a ≤ 1` and `b ∈ [0, 1]`.
* `TauCeti.Probability.noiseKernel_one` and `TauCeti.Probability.noiseKernel_zero`: the
  noiseless kernel is the identity and the pure-noise kernel forgets its input.
* `TauCeti.Probability.stdGaussian_bind_noiseKernel`: for `a ∈ [0, 1]` the standard Gaussian law
  is invariant under `noiseKernel a`.

## References

* J. Ho, A. Jain and P. Abbeel, *Denoising diffusion probabilistic models*, NeurIPS 2020,
  equations (2) and (4).
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Real

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The variance-preserving noising kernel with signal level `a`: it sends `x` to the law of
`√a • x + √(1 - a) • e` for `e` a standard Gaussian vector. -/
noncomputable def noiseKernel (a : ℝ) : Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) :=
  (Kernel.id ×ₖ Kernel.const _ (stdGaussian (EuclideanSpace ℝ ι))).map
    (fun p ↦ √a • p.1 + √(1 - a) • p.2)

/-- Every noising kernel is a Markov kernel, whatever the signal level. -/
instance (a : ℝ) : IsMarkovKernel (noiseKernel (ι := ι) a) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The noising kernel at `x` is the standard Gaussian pushed forward by
`e ↦ √a • x + √(1 - a) • e`. -/
theorem noiseKernel_apply_eq_map (a : ℝ) (x : EuclideanSpace ℝ ι) :
    noiseKernel a x =
      (stdGaussian (EuclideanSpace ℝ ι)).map (fun e ↦ √a • x + √(1 - a) • e) := by
  rw [noiseKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def]

/-- With no noise, the noising kernel is the identity kernel. -/
@[simp]
theorem noiseKernel_one : noiseKernel (ι := ι) 1 = Kernel.id := by
  ext1 x
  simp [noiseKernel_apply_eq_map, Measure.map_const, Kernel.id_apply]

/-- With no signal, the noising kernel forgets its input and returns the standard Gaussian. -/
@[simp]
theorem noiseKernel_zero :
    noiseKernel (ι := ι) 0 = Kernel.const _ (stdGaussian (EuclideanSpace ℝ ι)) := by
  ext1 x
  simp [noiseKernel_apply_eq_map]

section DecidableEq

variable [DecidableEq ι]

/-- The noising kernel at `x` is the isotropic Gaussian with mean `√a • x` and covariance
`(1 - a) • 1`. For `a > 1` both sides are the point mass at `√a • x`. -/
theorem noiseKernel_apply (a : ℝ) (x : EuclideanSpace ℝ ι) :
    noiseKernel a x = multivariateGaussian (√a • x) ((1 - a) • 1) := by
  rw [noiseKernel_apply_eq_map, ← multivariateGaussian_zero_one,
    map_add_smul_multivariateGaussian _ Matrix.PosSemidef.one, smul_zero, add_zero]
  rcases le_or_gt a 1 with ha | ha
  · rw [Real.sq_sqrt (sub_nonneg.2 ha)]
  · rw [Real.sqrt_eq_zero'.2 (sub_nonpos.2 ha.le), zero_pow two_ne_zero, zero_smul,
      multivariateGaussian_zero_right, ← neg_sub a, neg_smul,
      multivariateGaussian_neg_right _ (Matrix.PosSemidef.one.smul (sub_nonneg.2 ha.le))]

end DecidableEq

/-- Composing two noising kernels multiplies their signal levels: noising with level `a` and
then with level `b` is noising with level `a * b`. The first level need not be nonnegative, since
for `a ≤ 0` both sides forget their input. -/
theorem noiseKernel_comp {a b : ℝ} (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    noiseKernel (ι := ι) b ∘ₖ noiseKernel a = noiseKernel (a * b) := by
  classical
  ext1 x
  -- The second step adds the independent noise `ν = N(0, 1 - b)` to the rescaled first step.
  set ν := (stdGaussian (EuclideanSpace ℝ ι)).map (fun e ↦ √(1 - b) • e)
  have hbind : (noiseKernel a x).bind (noiseKernel b) =
      (noiseKernel a x).map (fun y ↦ √b • y) ∗ ν := by
    rw [← Measure.bind_map_add_eq_conv _ _ (by fun_prop)]
    congr 1
    funext y
    rw [noiseKernel_apply_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def]
  have hν : ν = multivariateGaussian 0 ((1 - b) • 1) := by
    simpa only [zero_add, smul_zero, multivariateGaussian_zero_one,
      Real.sq_sqrt (sub_nonneg.2 hb₁)] using
      map_add_smul_multivariateGaussian (0 : EuclideanSpace ℝ ι) Matrix.PosSemidef.one 0 √(1 - b)
  have hmap : (noiseKernel a x).map (fun y ↦ √b • y) =
      multivariateGaussian (√b • √a • x) ((√b ^ 2 * (1 - a)) • 1) := by
    have := map_add_smul_multivariateGaussian (√a • x)
      (Matrix.PosSemidef.one.smul (sub_nonneg.2 ha₁)) 0 √b
    simp only [zero_add, smul_smul] at this
    rw [noiseKernel_apply, this, smul_smul]
  -- Gaussian convolution adds the means and the covariances.
  rw [Kernel.comp_apply, hbind, hmap, hν, multivariateGaussian_conv_multivariateGaussian _ _
    (Matrix.PosSemidef.one.smul (by positivity)) (Matrix.PosSemidef.one.smul (sub_nonneg.2 hb₁)),
    noiseKernel_apply, add_zero, smul_smul, ← add_smul, Real.sqrt_mul' a hb₀, mul_comm √b,
    Real.sq_sqrt hb₀]
  congr 2
  ring

/-- Noising with a level in `[0, 1]` preserves the standard Gaussian law: the noising kernels are
variance preserving. -/
theorem stdGaussian_bind_noiseKernel {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    (stdGaussian (EuclideanSpace ℝ ι)).bind (noiseKernel a) = stdGaussian (EuclideanSpace ℝ ι) := by
  have h := noiseKernel_comp (ι := ι) zero_le_one ha₀ ha₁
  rw [zero_mul, noiseKernel_zero] at h
  simpa using congrArg (fun κ ↦ κ 0) h

end TauCeti.Probability
