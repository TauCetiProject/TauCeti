/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real

import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TauCeti.InformationTheory.KullbackLeibler.Basic
import TauCeti.InformationTheory.KullbackLeibler.Pi
import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.Probability.Distributions.Gaussian.Basic
import TauCeti.Probability.Distributions.Tilted

/-!
# Relative entropy between Gaussian laws

For a common variance `v ≠ 0`,
`klDiv (gaussianReal a v) (gaussianReal b v) = ENNReal.ofReal ((a - b) ^ 2 / (2 * v))`.

The proof uses exponential tilting rather than densities: tilting `N(a, v)` by `exp (t * x)`
with `t = (b - a) / v` gives `N(b, v)` (`TauCeti.Probability.gaussianReal_tilted_mul`), so the
log-likelihood ratio of `N(a, v)` against `N(b, v)` is `log Z - t * x`, where `Z` is the moment
generating function of `N(a, v)` at `t`. Its mean under `N(a, v)` is
`a t + v t ^ 2 / 2 - t a = (a - b) ^ 2 / (2 v)`.

On Euclidean space, the isotropic Gaussian laws `N(a, v • 1)` and `N(b, v • 1)` are products of
real Gaussian laws of variance `v`, transported along `WithLp.toLp 2`
(`TauCeti.Probability.multivariateGaussian_smul_one_eq_map_pi`). Relative entropy is invariant
under that measurable equivalence and tensorizes over finite products (`TauCeti.klDiv_pi`), so the
divergence is the sum of the coordinate divergences, `‖a - b‖ ^ 2 / (2 v)`.

## Main statements

* `Real.klDiv_gaussianReal`: the relative entropy between real Gaussian laws with a common
  variance.
* `TauCeti.klDiv_multivariateGaussian`: the relative entropy between isotropic Gaussian laws on
  Euclidean space with a common variance.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Corollary 2.1(i),
  p. 87, for unit variance.

The proof is adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>), file
`CKSD/Nonparametric/LowerBounds/Gaussian.lean`, theorem `CKSD.klDiv_gaussianReal_gaussianReal`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal

namespace TauCeti

/-- The relative entropy between real Gaussian laws with a common nonzero variance `v` is
`(a - b) ^ 2 / (2 v)`. -/
theorem _root_.Real.klDiv_gaussianReal (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal a v) (gaussianReal b v) = ENNReal.ofReal ((a - b) ^ 2 / (2 * v)) := by
  set t : ℝ := (b - a) / v with ht
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  set μ := gaussianReal a v
  have hb : gaussianReal b v = μ.tilted (t * ·) := by
    rw [Probability.gaussianReal_tilted_mul, ht]
    congr 1
    field_simp
    ring
  have hexp : Integrable (fun x ↦ exp (t * x)) μ := integrable_exp_mul_gaussianReal t
  have hself : Integrable (llr μ μ) μ :=
    (integrable_congr (llr_self μ)).mpr (integrable_zero _ _ _)
  have hlin : Integrable (fun x ↦ t * x) μ :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).const_mul t
  have hint : Integrable (llr μ (μ.tilted (t * ·))) μ :=
    integrable_llr_tilted_right Measure.AbsolutelyContinuous.rfl hlin hself hexp
  have hval := integral_llr_tilted_right Measure.AbsolutelyContinuous.rfl hlin hexp hself
  rw [integral_congr_ae (llr_self μ), Probability.integral_exp_mul_gaussianReal a v t, log_exp,
    integral_const_mul, integral_id_gaussianReal] at hval
  simp only [Pi.zero_apply, integral_zero] at hval
  rw [hb, klDiv_of_ac_of_integrable (absolutelyContinuous_tilted hexp) hint, hval, ← hb,
    probReal_univ]
  simp only [μ, probReal_univ]
  congr 1
  rw [ht]
  field_simp
  ring

/-- The relative entropy between isotropic Gaussian laws on Euclidean space with a common
positive variance `v` is `‖a - b‖ ^ 2 / (2 v)`. -/
theorem klDiv_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : EuclideanSpace ℝ ι) {v : ℝ} (hv : 0 < v) :
    klDiv (multivariateGaussian a (v • 1)) (multivariateGaussian b (v • 1)) =
      ENNReal.ofReal (‖a - b‖ ^ 2 / (2 * v)) := by
  lift v to ℝ≥0 using hv.le
  have hv0 : v ≠ 0 := by exact_mod_cast hv.ne'
  rw [Probability.multivariateGaussian_smul_one_eq_map_pi,
    Probability.multivariateGaussian_smul_one_eq_map_pi, ← MeasurableEquiv.coe_toLp,
    Measure.klDiv_map_measurableEquiv, klDiv_pi]
  simp_rw [Real.klDiv_gaussianReal _ _ hv0]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity, EuclideanSpace.real_norm_sq_eq,
    Finset.sum_div]
  simp

end TauCeti
