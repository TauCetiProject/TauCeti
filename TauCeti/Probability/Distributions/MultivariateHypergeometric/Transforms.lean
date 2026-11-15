/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.MultivariateHypergeometric.Basic
public import TauCeti.Probability.Distributions.Multinomial.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Transforms of multivariate hypergeometric laws

The Euclidean cast of a multivariate hypergeometric count vector has every exponential
moment. Its directional moment-generating function and vector characteristic function are
finite sums with the binomial-coefficient masses of sampling without replacement. The
directional cumulant-generating function is the logarithm of the exponential sum.

The formulas use `multinomialToEuclidean`, as do the mean and covariance of this family.
They follow directly from `integral_multivariateHypergeometricMeasure`; no independence
between the category counts is assumed. Native-count `HasLaw` corollaries give exponential
integrability and the mgf for weighted counts on any probability space.

All measure formulas include empty category types, empty or full samples, zero category
sizes, and the zero measure when the sample size exceeds the population size. On the
probability range the exponential sum is strictly positive; outside it both transforms
vanish and the cgf retains the convention `Real.log 0 = 0`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 39.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Every real observable of the Euclidean multivariate hypergeometric count vector has
exponential-integrability domain all of `ℝ`, including invalid sample sizes. -/
@[simp]
theorem integrableExpSet_map_multinomialToEuclidean_multivariateHypergeometricMeasure
    (K : ι → ℕ) (n : ℕ) (f : EuclideanSpace ℝ ι → ℝ) :
    integrableExpSet f
      ((multivariateHypergeometricMeasure K n).map multinomialToEuclidean) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  exact measurableEmbedding_multinomialToEuclidean.integrable_map_iff.mpr
    (integrable_multivariateHypergeometricMeasure _ K n)

open Classical in
/-- The directional mgf is the finite exponential sum of the sampling masses. The formula
also holds for invalid sample sizes, when the law and the sum are zero. -/
theorem mgf_inner_multivariateHypergeometricMeasure (K : ι → ℕ) (n : ℕ)
    (θ : EuclideanSpace ℝ ι) (t : ℝ) :
    mgf (fun x ↦ ⟪θ, x⟫)
      ((multivariateHypergeometricMeasure K n).map multinomialToEuclidean) t =
      ∑ k ∈ Finset.piAntidiag Finset.univ n,
        ((∏ i, ((K i).choose (k i) : ℝ)) / ((∑ i, K i).choose n : ℝ)) *
          Real.exp (t * ∑ i, θ i * (k i : ℝ)) := by
  rw [mgf, measurableEmbedding_multinomialToEuclidean.integral_map,
    integral_multivariateHypergeometricMeasure]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [multivariateHypergeometricWeight_toReal, (Finset.mem_piAntidiag.mp hk).1,
    inner_multinomialToEuclidean, smul_eq_mul]

open Classical in
/-- The directional cgf is the logarithm of the finite exponential sum, on the full
exponential-integrability domain `ℝ`. -/
theorem cgf_inner_multivariateHypergeometricMeasure (K : ι → ℕ) (n : ℕ)
    (θ : EuclideanSpace ℝ ι) (t : ℝ) :
    cgf (fun x ↦ ⟪θ, x⟫)
      ((multivariateHypergeometricMeasure K n).map multinomialToEuclidean) t =
      Real.log (∑ k ∈ Finset.piAntidiag Finset.univ n,
        ((∏ i, ((K i).choose (k i) : ℝ)) / ((∑ i, K i).choose n : ℝ)) *
          Real.exp (t * ∑ i, θ i * (k i : ℝ))) := by
  rw [cgf, mgf_inner_multivariateHypergeometricMeasure]

open Classical in
/-- The vector characteristic function is the finite Fourier sum of the sampling masses,
with characteristic kernel `exp (I * ⟪t, x⟫)`. -/
theorem charFun_map_multinomialToEuclidean_multivariateHypergeometricMeasure
    (K : ι → ℕ) (n : ℕ) (t : EuclideanSpace ℝ ι) :
    charFun ((multivariateHypergeometricMeasure K n).map multinomialToEuclidean) t =
      ∑ k ∈ Finset.piAntidiag Finset.univ n,
        ((∏ i, ((K i).choose (k i) : ℝ)) / ((∑ i, K i).choose n : ℝ)) •
          Complex.exp ((∑ i, (t i : ℂ) * (k i : ℂ)) * Complex.I) := by
  rw [charFun_apply, measurableEmbedding_multinomialToEuclidean.integral_map,
    integral_multivariateHypergeometricMeasure]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [multivariateHypergeometricWeight_toReal, (Finset.mem_piAntidiag.mp hk).1,
    real_inner_comm, inner_multinomialToEuclidean]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → ι → ℕ} {K : ι → ℕ} {n : ℕ}

/-- Every weighted total of multivariate hypergeometric counts has exponential moments of
all real orders. No independence of the counts is required. -/
theorem integrableExpSet_sum_cast_multivariateHypergeometricMeasure
    (hX : HasLaw X (multivariateHypergeometricMeasure K n) P) (θ : ι → ℝ) :
    integrableExpSet (fun ω ↦ ∑ i, θ i * (X ω i : ℝ)) P = Set.univ :=
  Set.eq_univ_of_forall fun t ↦ hX.integrable_fun_comp
    (integrable_multivariateHypergeometricMeasure
      (fun k ↦ Real.exp (t * ∑ i, θ i * (k i : ℝ))) K n)

open Classical in
/-- The mgf of a weighted total of multivariate hypergeometric counts is the finite
exponential sum of their joint sampling masses. -/
theorem mgf_sum_cast_multivariateHypergeometricMeasure
    (hX : HasLaw X (multivariateHypergeometricMeasure K n) P) (θ : ι → ℝ) (t : ℝ) :
    mgf (fun ω ↦ ∑ i, θ i * (X ω i : ℝ)) P t =
      ∑ k ∈ Finset.piAntidiag Finset.univ n,
        ((∏ i, ((K i).choose (k i) : ℝ)) / ((∑ i, K i).choose n : ℝ)) *
          Real.exp (t * ∑ i, θ i * (k i : ℝ)) := by
  have h := mgf_inner_multivariateHypergeometricMeasure K n (WithLp.toLp 2 θ) t
  rw [mgf, measurableEmbedding_multinomialToEuclidean.integral_map] at h
  simp only [inner_multinomialToEuclidean] at h
  rw [mgf, ← h]
  exact hX.integral_comp (f := fun k ↦ Real.exp (t * ∑ i, θ i * (k i : ℝ)))
    Measurable.of_discrete.aestronglyMeasurable

end ProbabilityTheory.HasLaw
